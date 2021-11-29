
extern crate num_cpus;
use std::collections::{BTreeMap,HashMap};
use std::convert::{TryInto,From};
use std::thread;
use crossbeam_channel::bounded;
use super::equivalence_classes::{DomainEquivClass,EquivClass};
use std::time::{Duration, Instant};
use ark_ff::{FftField, FftParameters, Field, One, PrimeField, Zero};
use std::ops::Mul;
use ark_poly::{
    domain::{EvaluationDomain, Radix2EvaluationDomain},
    evaluations::{univariate::{Evaluations}},
    polynomial::{
        univariate::{DensePolynomial, SparsePolynomial},
        Polynomial, UVPolynomial,
    },
};

pub use super::{parallelize::{parallel_hashmap_noaux, parallel_vec_function,parallel_function,parallel_btreemap,parallel_hashmap,parallel_hashmap_flatten}};
use ark_test_curves::bls12_381::Fr;
use rand::distributions::{Distribution, Uniform};
pub fn verifier_challenge<F: PrimeField>() -> F {
    let modulus:usize = F::size_in_bits()/8;
    let rb: Vec<u8> = (0..modulus).map(|_| { rand::random::<u8>() }).collect();
    let mut challenge;
    loop {
        challenge = F::from_random_bytes(&rb);
        if challenge.is_some() {
            break;
        }
    }
    challenge.unwrap()
}
fn prod_except_inverse<F:PrimeField>(args:&Vec<F>,except:&F) -> F{
    let mut prod = F::one();
    for el in args{
	if el != except{
	    prod = prod * (*except - *el);
	}
    }
    prod
}
fn prods<F:PrimeField>(args:Vec<F>) -> F{
    let mut prod = F::one();
    for el in args{
	prod = prod *  el;
    }
    prod
}
pub fn evaluate_poly<F: PrimeField>(
    p: &DensePolynomial<F>,
    d: &Radix2EvaluationDomain<F>,
) -> Evaluations<F, Radix2EvaluationDomain<F>> {
    let evals = d.elements().map(|e| p.evaluate(&e)).collect();
    Evaluations::from_vec_and_domain(evals, *d)
}
pub fn fft_evaluate_poly<F:FftField>(mut p:DensePolynomial<F>, d: &Radix2EvaluationDomain<F>) -> Evaluations<F,Radix2EvaluationDomain<F>>{
    d.fft_in_place(&mut p.coeffs);
    Evaluations::from_vec_and_domain(p.coeffs,*d)
}
fn create_test_poly<F:PrimeField>(degree : usize) -> DensePolynomial<F>{
    let mut coeffs = Vec::<F>::new();
    for _ in (0..degree){
	coeffs.push(verifier_challenge());
    }
    return DensePolynomial::from_coefficients_slice(&coeffs);
}
pub fn setup<F:PrimeField>(k : u32) -> (Radix2EvaluationDomain<F>){
    let mut domain = None;
    while domain == None{
	domain = Radix2EvaluationDomain::<F>::new(2u64.pow(k).try_into().unwrap());
    }
    domain.unwrap()
}
#[test]
fn test_fft_evaluate(){
    let poly = create_test_poly::<Fr>(10);
    let domain = setup(12u32);
    let now = Instant::now();
    let slow_eval = evaluate_poly(&poly,&domain);
    let now2 = Instant::now();
    let fast_eval = evaluate_poly(&poly,&domain);
    assert_eq!(slow_eval,fast_eval);
}
pub fn rand_usize(upperbound:usize) -> usize{
    let mut rng = rand::thread_rng();
    let rng_ = Uniform::from(1usize..upperbound);
    rng_.sample(&mut rng)
}
pub fn rand_to_lower_bound(rand:usize,new_bound:usize)->usize{
    rand % new_bound
}
//instead of returning DensePolynomial, return (numerator, denominator) but denominator is not inverted yet
fn lagrange_basis_term<F:FftField>(eli : F, elj : F,evaluation_point: &F) -> F{
    let denominator = (elj - eli);
    //    let numerator = -eli + evaluation_point;
    denominator
//    (numerator,denominator)
}
fn numerator<F:FftField>(x : &Vec<F>, j:usize, evaluation_point: &F) -> F{
    let mut n = F::from(1u32);
    let jth_el = x[j];
    for (i,v) in x.iter().enumerate(){
	if i != j {
	    let basis_term = jth_el - *v;
	    n = n * basis_term;
	}
    }
    n
    
}
fn lagrange_basis_poly<F:FftField>(x : &Vec<F>, j : usize, evaluation_point: &F) -> F{
    let mut n = F::from(1u32);
    let mut d : F = F::from(1u32);
    let jth_el = x[j];
    for (i,v) in x.iter().enumerate(){
	if i != j {
	    let basis_term = &lagrange_basis_term(*v,jth_el,&evaluation_point);
//	    n = n * basis_term.0;
	    d = d *  basis_term;
	}
    }
    let inverse_d = d.inverse();
    let alpha_factor = *evaluation_point - x[j];
    if inverse_d.is_none(){
	panic!("cannot interpolate because no inverse");
    }
//    n *
    inverse_d.unwrap() * alpha_factor.inverse().unwrap()

}


pub fn lagrange_interpolate_over_points<F:FftField>(x : Vec<F>,y : Vec<F>,challenge:&F) -> F{
    let now = Instant::now();
    assert_eq!(x.len(),y.len());
    assert_eq!(x.len() >=2, true);

    let mut zero_s_y = F::from(1u32);
    for i in &x{
	zero_s_y = zero_s_y * (*challenge - *i);
    }

    let mut sum = F::from(0u32);
    for (j,vy) in y.iter().enumerate(){
	let product  = *vy * lagrange_basis_poly(&x,j,challenge); 
	sum =  sum + product;
    }
    let prod = sum * zero_s_y;

    prod
}
pub fn lagrange_interpolate_with_precompute<F:FftField>(x : Vec<F>,y : Vec<F>,challenge:&F,c_alpha:BTreeMap<F,F>) -> F{
    let now = Instant::now();
    assert_eq!(x.len(),y.len());
    assert_eq!(x.len() >=2, true);


    let mut sum = F::from(0u32);
    for (j,vy) in y.iter().enumerate(){
	let mut zero_s_y = F::from(1u32);
	for i in &x{
	    if *i != x[j]{
		zero_s_y = zero_s_y * (*challenge - *i);
	    }
	}
	let denominator = *c_alpha.get(&x[j]).unwrap(); //* alpha_factor;
	let product = *vy * zero_s_y * denominator;
	sum =  sum + product;
    }
    let prod = sum; // zero_s_y;
    prod
}
fn subtract_challenge<F:PrimeField>(cosets:&Vec<F>,challenge:&F) -> Vec<F>{
    let mut new_map = Vec::new();
    for val in cosets{
	new_map.push(*challenge - *val);
    }
    new_map
}
pub fn lagrange_interpolate_with_precompute_tuple<F:PrimeField>(points:Vec<(F,F)>, coset_ind: F, aux:(&BTreeMap<(usize,F),Vec<(F,F)>>,F,Vec<F>,usize,F)) -> F{
    let (xs,ys):(Vec<F>,Vec<F>) = points.iter().cloned().unzip();
    let c_alpha = aux.0;
    let zero_sy = aux.1;
    let coset_inverses = aux.2;
    let round_num = aux.3;
    let challenge = aux.4;
    let mut sum = F::from(0u32);
    let denominators = c_alpha.get(&(round_num,coset_ind)).unwrap();
    let mut smallBTree = BTreeMap::new();
    for d in denominators{
	smallBTree.insert(d.0,d.1);
    }
    for (j,vy) in ys.iter().enumerate(){
	let product = *vy * smallBTree.get(&xs[j]).unwrap() * coset_inverses[j];
	sum =  sum + product;
    }
    let prod = sum * zero_sy;
    prod
}

fn mul_vec<F:FftField>(v : &Vec<F>,alpha:&F) -> F{
    let to_mul:Vec<F> = v.iter().map(|i| if(*i!=*alpha){*i - *alpha} else {F::one()}).collect();
    let mut prod = F::from(1u32);

    for i in v{
	prod = prod * i;
    }
    prod
}

#[test]
fn test_mul_vec(){
    let a = [Fr::from(6u32),Fr::from(7u32)];
    let zero = Fr::from(0u32);
    assert_eq!(Fr::from(42u32),mul_vec(&a.to_vec(),&zero));
}

pub fn optimize_lagrange_interpolate_over_points<F:FftField>(x : Vec<F>,y : Vec<F>,challenge:&F) -> F{
    assert_eq!(x.len(),y.len());
    assert_eq!(x.len() >=2, true);
    //compute Zero_s_{y}
    let mut zero_s_y = F::from(1u32);
    for i in &x{
	zero_s_y = zero_s_y * (*challenge - *i);
    }
    let mut sum = F::from(0u32);
    for (j,vy) in y.iter().enumerate(){
	let c_alpha = mul_vec(&x,&x[j]);
	assert_eq!(c_alpha == F::from(0u32),false);
	let div = *vy / (c_alpha * (*challenge - x[j]));
	sum = sum + div;
    }
    return sum * zero_s_y;
}

#[test]
fn test_lagrange(){
    let poly2 = DensePolynomial::from_coefficients_slice(&[Fr::one(),Fr::from(2u64)]);
    let eval_point = Fr::from(10u32);
    let x = [Fr::one(),Fr::from(2u64)];
    let y: Vec<Fr>  = x.iter().map(|e| poly2.evaluate(e)).collect();
    let eval = lagrange_interpolate_over_points(x.to_vec(),y.to_vec(),&eval_point);
    assert_eq!(eval,poly2.evaluate(&eval_point));
}
pub fn find_generator_from_vec<F: FftField>(v: &Vec<F>) -> F {
    let orderusize = v.len() as usize;
    let orderu64 = v.len() as u64;
    debug_assert_eq!(orderusize <= 1, false);
    let mut gen = None;
    for k in v {
        let maybe_gen = k;
        if maybe_gen.pow(&[orderu64]) == F::one() && maybe_gen.pow(&[orderu64 / 2]) != F::one() {
	    gen = Some(maybe_gen);
	    break;
        }
    }
    if gen.is_none(){
	panic!("vector does not form a group");
    }
    *gen.unwrap()
}
pub fn get_nth_primitive_root<F: FftField>(r: &Radix2EvaluationDomain<F>, n: u64) -> F {
    let generator = r.group_gen;
    let order = r.size;
    let mut rng = rand::thread_rng();
    let rng_ = Uniform::from(1u64..order);
    let mut new_gen;
    loop {
        let exp = rng_.sample(&mut rng);
        let el = generator.pow(&[exp]);
        new_gen = el.pow(&[order / n]);
        if new_gen.pow(&[n / 2]) != F::one() {
            break;
        }
    }
    return new_gen;
}

pub fn get_subgroup<F: FftField>(
    r: &Radix2EvaluationDomain<F>,
    n: u64,
) -> Option<Radix2EvaluationDomain<F>> {
    let generator = get_nth_primitive_root(r, n);
    let log_size_of_group = n.trailing_zeros();
    if log_size_of_group > F::FftParams::TWO_ADICITY {
        return None;
    }
    debug_assert_eq!(generator.pow([n]), F::one());
    let size_as_field_element = F::from(n);
    let size_inv = size_as_field_element.inverse()?;
    Some(Radix2EvaluationDomain {
        size: n,
        log_size_of_group,
        size_as_field_element,
        size_inv,
        group_gen: generator,
        group_gen_inv: generator.inverse()?,
        generator_inv: F::multiplicative_generator().inverse()?,
    })
}
pub fn get_subgroup_from_gen<F: FftField>(
    generator: F,
    n: u64,
) -> Option<Radix2EvaluationDomain<F>> {
    let log_size_of_group = n.trailing_zeros();
    if log_size_of_group > F::FftParams::TWO_ADICITY {
        return None;
    }
    debug_assert_eq!(generator.pow([n]), F::one());
    let size_as_field_element = F::from(n);
    let size_inv = size_as_field_element.inverse()?;
    Some(Radix2EvaluationDomain {
        size: n,
        log_size_of_group,
        size_as_field_element,
        size_inv,
        group_gen: generator,
        group_gen_inv: generator.inverse()?,
        generator_inv: F::multiplicative_generator().inverse()?,
    })
}
pub fn get_domain_from_vec<F: PrimeField>(d: Vec<F>) -> Option<Radix2EvaluationDomain<F>> {
    let group_gen = find_generator_from_vec(&d);
    get_subgroup_from_gen(group_gen, d.len() as u64)
}

pub fn vanishing_poly_over_domain<F: FftField>(
    r: &Radix2EvaluationDomain<F>,
) -> DensePolynomial<F> {
    let generator = r.group_gen;
    let order = r.size;
    let mut poly = DensePolynomial::<F>::from_coefficients_slice(&[
        generator.pow(&[order]) * (-F::one()),
        F::one(),
    ]);
    let mut index = order - 1;
    loop {
        let new_poly = DensePolynomial::from_coefficients_slice(&[
            generator.pow(&[index]) * (-F::one()),
            F::one(),
        ]);
        poly = &poly * &new_poly;
        if index == 1 {
            break;
        }
        index -= 1;
    }
    poly
}

fn eval_over_domain(
    poly: &DensePolynomial<Fr>,
    domain: &Radix2EvaluationDomain<Fr>,
) -> Evaluations<Fr, Radix2EvaluationDomain<Fr>> {
    let evals = domain
        .elements()
        .map(|elem| (*poly).evaluate(&elem))
        .collect();
    Evaluations::from_vec_and_domain(evals, *domain)
}

#[test]
fn test_vanishing_poly() {
    let domain = Radix2EvaluationDomain::<Fr>::new(4).unwrap();
    let vanishing_poly = vanishing_poly_over_domain(&domain);
    eval_poly(&vanishing_poly, &domain);
}
//dense polynomials are evaluted using FFT in arkworks which does not match up with naive evaluation
#[test]
fn arkworks_dense_evaluate_over_domain_doesnt_work() {
    let domain = Radix2EvaluationDomain::<Fr>::new(4).unwrap();
    let coeffs: [Fr; 5] = [
        Fr::from(1u64),
        Fr::from(2u64),
        Fr::from(3u64),
        Fr::from(4u64),
        Fr::from(5u64),
    ];
    let poly = DensePolynomial::from_coefficients_slice(&coeffs);
    let eval1 = eval_over_domain(&poly, &domain);
    let eval2 = poly.evaluate_over_domain(domain);
    assert_ne!(eval1, eval2);
}

fn eval_poly(p: &DensePolynomial<Fr>, d: &Radix2EvaluationDomain<Fr>) {
    let generator = d.group_gen;
    let order = d.size;
    let mut els = d.elements();
    for i in 1..order + 1 {
        let t = generator.pow(&[i]);
        let e = p.evaluate(&t);
        let el = &els.next();
        let f = match el {
            Some(a) => p.evaluate(a),
            None => Fr::one(),
        };
        assert_eq!(e, Fr::zero());
        assert_eq!(f, Fr::zero());
    }
}
pub fn sample_from_domain<F : PrimeField>(d : Radix2EvaluationDomain<F>,rand:usize)->F{
    let order = d.size;
    if order <= 0 {
	panic!("order is 0 {:?}",d);
    }
    let el = d.elements().nth(rand).unwrap();
    return el;
    
}

#[test]
fn test_multiply_polynomials() {
    let coeffs1: [Fr; 2] = [Fr::from(1u64), Fr::from(2u64)];
    let poly = DensePolynomial::<Fr>::from_coefficients_slice(&coeffs1);
    let coeffs2: [Fr; 2] = [Fr::from(1u64), Fr::from(3u64)];
    let poly2 = DensePolynomial::<Fr>::from_coefficients_slice(&coeffs2);
    let poly_product = &poly * &poly2;
    let mc: [Fr; 3] = [
        Fr::from(1u64) * Fr::from(1u64),
        Fr::from(1u64) * Fr::from(3u64) + Fr::from(2u64) * Fr::from(1u64),
        Fr::from(2u64) * Fr::from(3u64),
    ];
    let manual_pp = DensePolynomial::<Fr>::from_coefficients_slice(&mc);
    assert_eq!(poly_product, manual_pp);
}

pub fn q<F: Field>(n: u32) -> SparsePolynomial<F> {
    let exp = 2usize.pow(n);
    SparsePolynomial::<F>::from_coefficients_slice(&[(exp, F::one())])
}
//for a fixed n = 2
pub fn evaluate_q<F:Field>(elem:&F) -> F{
    let mut e = *elem;
    *e.square_in_place();
    e * e
}
#[test]
fn test_eq(){
    let n = 2;
    let q_ = q::<Fr>(n);
    assert_eq!(q_.evaluate(&Fr::from(2u64)),Fr::from(16u64));
}

fn test_function<F:PrimeField>(input: F) -> F{
    input * F::from(3u32)
}

fn normal_inverse<F:PrimeField>(elems:&Vec<F>) -> Vec<F>{
    let mut inverses = Vec::new();
    for e in elems{
	inverses.push(e.inverse().unwrap());
    }
    inverses
}
fn mul<F:PrimeField>(elems:Vec<F>,except:Option<F>)->F{
    let mut product = F::one();
    for e in elems{
	if(Some(e) != except){
	    product = product * e;
	}
    }
    product
}
fn partial_products<F:PrimeField>(elems:&Vec<F>) -> Vec<F>{
    //function for multiplying all field elements in elems together
    let mut products = Vec::new();
    products.push(elems[0]);
    for index in 1..elems.len(){
	let old_prod = products[index - 1].clone();
	products.push(old_prod * elems[index].clone());
    }
    products
}
#[test]
fn test_partial_products(){
    let f_vec = vec![Fr::one(),Fr::from(2u32),Fr::from(3u32),Fr::from(4u32)];
    let pp = partial_products(&f_vec);
    assert_eq!(pp[0],Fr::one());
    assert_eq!(pp[1],Fr::from(2u32));
    assert_eq!(pp[2],Fr::from(2u32) * Fr::from(3u32));
    assert_eq!(pp[3],Fr::from(2u32) * Fr::from(3u32) * Fr::from(4u32));
}
    
pub fn batch_inverse<F:PrimeField>(elems:Vec<F>) -> Vec<F>{
    let products = partial_products(&elems);
    let mut inverse = products[products.len() - 1].clone().inverse().unwrap();
    let mut inverses = Vec::new();
    for index in (1..products.len()).rev(){
	inverses.insert(0,products[index - 1] * inverse);
	inverse = inverse * elems[index];
    }
    inverses.insert(0,inverse);
    inverses
}
pub fn batch_inverse_par<F:PrimeField>(elems:Vec<F>) -> Vec<F>{
    let products = partial_products(&elems);
    let mut inverse = products[products.len() - 1].clone().inverse().unwrap();
    let mut inverses = Vec::new();
    for index in (1..products.len()).rev(){
	inverses.insert(0,products[index - 1] * inverse);
	inverse = inverse * elems[index];
    }
    inverses.insert(0,inverse);
    inverses
}

pub fn random_f<F: PrimeField>() -> F {
    let modulus:usize = F::size_in_bits()/8;
    let rb: Vec<u8> = (0..modulus).map(|_| { rand::random::<u8>() }).collect();
    let mut challenge;
    loop {
        challenge = F::from_random_bytes(&rb);
        if challenge.is_some() {
            break;
        }
    }
    challenge.unwrap()
}
pub fn random_field_els<F:PrimeField>(count:usize) -> Vec<F>{
    let mut els = Vec::new();
    for i in 0..count{
	els.push(random_f());
    }
    els
}
#[test]
fn test_batch_inverse(){
    let els = random_field_els::<Fr>(100000);
    let bi_now = Instant::now();
    let bi = parallel_batch_inverse_vec(els.clone());
    let ni_now = Instant::now();
    let ni = normal_inverse(&els);
    assert_eq!(ni,bi);

}

pub fn parallel_batch_inverse_map<F:PrimeField>(elems:&HashMap<F,Vec<F>>) -> HashMap<F,Vec<F>>{
    let fun = batch_inverse::<F>;
    parallel_hashmap_flatten(&elems,fun)
}
    /*
    let keys:Vec<F> = elems.keys().cloned().collect();
    let vec = flatten(elems);
    let fun = batch_inverse::<F>;
    let results = parallel_vec_function::<F,F>(&vec, fun);
    let mut p_results = vec![F::one();results.len()];
    for p in results{
	p_results[p.0] = p.1;
    }
    unflatten(p_results,4,keys)
*/


fn flatten<F:PrimeField>(to_flatten:&HashMap<F,Vec<F>>) -> Vec<F>{
    let mut results = Vec::new();
    for (key,val) in to_flatten{
	for e in val{
	    results.push(*e);
	}
    }
    results
}
fn unflatten<F:PrimeField>(to_unflatten:Vec<F>,interval:usize,keys:Vec<F>) -> HashMap<F,Vec<F>>{
    let mut input_index = 0;
    let mut key_index = 0;
    let mut results = HashMap::new();
    loop{
	if input_index  >= to_unflatten.len(){
	    break;
	}
	let mut temp = Vec::new();
	for i in 0..interval{
	    temp.push(to_unflatten[input_index + i]);
	}
	results.insert(keys[key_index],temp);
	input_index = input_index + interval;
	key_index = key_index + 1;
    }
    assert_eq!(key_index,keys.len());
    results	
}
pub fn parallel_batch_inverse_vec<F:PrimeField>(elems:Vec<F>) -> Vec<F>{
    let fun = batch_inverse::<F>;
    let results = parallel_vec_function::<F,F>(&elems, fun);
    let mut p_results = vec![F::one();elems.len()];
    for p in results{
	p_results[p.0] = p.1;
    }
    p_results
}

pub fn parallel_interpolate<F:PrimeField>(c_alpha: BTreeMap<(usize,F),Vec<(F,F)>>, point_sets:EquivClass<F>,zero_sy:HashMap<F,F>,coset_inverses:HashMap<F,Vec<F>>,round_num:usize,challenge:F) -> (Vec<F>,HashMap<F,F>){
    let mut domain_points = Vec::new();
    let mut aux_vec = Vec::new();
    for (key,val) in &point_sets.equiv_classes{
	domain_points.push(key.clone());
	aux_vec.push((&c_alpha,zero_sy.get(key).unwrap().clone(),coset_inverses.get(key).unwrap().clone(),round_num,challenge.clone()));
    }
    type T<'a,F:PrimeField> = (&'a BTreeMap<(usize,F),Vec<(F,F)>>,F,Vec<F>,usize,F);
    (domain_points,parallel_hashmap::<T<F>,F,Vec<(F,F)>,F>(point_sets.equiv_classes,aux_vec,lagrange_interpolate_with_precompute_tuple))
 
}
pub fn sequence_interpolate<F:PrimeField>(c_alpha: BTreeMap<(usize,F),Vec<(F,F)>>, point_sets:BTreeMap<F,Vec<(F,F)>>,zero_sy:BTreeMap<F,F>,coset_inverses:BTreeMap<F,Vec<F>>,round_num:usize,challenge:F) -> BTreeMap<F,F>{
    let mut new_map = BTreeMap::new();

    for (key,val) in &point_sets{
	let mut ys = Vec::new();
	let mut xs = Vec::new();
	for v in val{
	    ys.push(v.1);
	    xs.push(v.0);
	}

	new_map.insert(*key,lagrange_interpolate_over_points(xs.clone(),ys.clone(),&challenge));
    }
    new_map
 
}
pub fn parallel_inverse_calpha<F:PrimeField>(mut c_alpha:BTreeMap<(usize,F),Vec<(F,F)>>) -> BTreeMap<(usize,F),Vec<(F,F)>>{
    //collect 3rd points which is field element that needs to be inverse
    let mut to_be_inverted = Vec::new();
    for (key,val) in c_alpha.clone(){
	for v in val{
	    to_be_inverted.push(v.1);
	}
    }

    let results:Vec<F> = parallel_batch_inverse_vec(to_be_inverted);
    let mut count = 0;
    for (key,val) in c_alpha.clone(){
	let mut temp:Vec<(F,F)> = Vec::new();
	for v in val{
	    temp.push((v.0,results[count]));
	    count = count + 1;
	}
	c_alpha.insert(key,temp);
    }
    c_alpha
}
#[test]
fn test_parallel_batch_inverse(){
    let num_els:usize = 100000;
    let els = random_field_els::<Fr>(num_els);
    let bi_now = Instant::now();
    let bi = parallel_batch_inverse_vec(els.clone());
    let ni_now = Instant::now();
    let ni = normal_inverse(&els);
    assert_eq!(ni,bi);

}
