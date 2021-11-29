extern crate num_cpus;
#[path="util.rs"] pub mod util;
#[path="data_structures.rs"] pub mod data_structures;
#[path="iop.rs"] pub mod iop;
#[path="parallelize.rs"] pub mod parallelize;
#[path="niroa.rs"] pub mod niroa;
#[path="equivelence_classes.rs"] pub mod equivalence_classes;


use ark_std::hash::{Hash,Hasher};
use ark_ff::{PrimeField,ToBytes};
use ark_std::{
    io::{Read, Result as IoResult},
    vec::Vec,
};
use derivative::Derivative;
use std::thread;
use equivalence_classes::{DomainEquivClass,EquivClass};
use parallelize::{parallel_function,parallel_btreemap,parallel_btreemap_noaux,parallel_hashmap_noaux};
use crossbeam_channel::bounded;
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use std::time::{Duration, Instant};
use ark_test_curves::bls12_381::{Fr};
use ark_poly::{domain::{EvaluationDomain,Radix2EvaluationDomain},evaluations::{univariate::{Evaluations}},polynomial::{Polynomial,univariate::{DensePolynomial,SparsePolynomial}, UVPolynomial}};
use std::convert::{TryInto,From};
use iop::{Oracle, Setup, Iop, Prover, Verifier, Witness};
use std::collections::{BTreeMap, HashMap};
use std::iter::{FromIterator};
use niroa::{NiroaProof,Niroa, NiroaBatchProof, iop_prover_to_niroa_prover};
use util::{get_subgroup_from_gen,find_generator_from_vec,q,verifier_challenge,sample_from_domain,lagrange_interpolate_over_points,rand_usize,rand_to_lower_bound,lagrange_interpolate_with_precompute,fft_evaluate_poly,parallel_batch_inverse_map,parallel_inverse_calpha,parallel_interpolate,batch_inverse,random_field_els,sequence_interpolate};
use data_structures::{RSCodeDomain,Codeword,NonTerminalRound,TerminalRound,Round};
use ark_crypto_primitives::{merkle_tree::{MerkleTree,Path,Config,Digest},crh::pedersen,FixedLengthCRH,prf::blake2s::Blake2s as MyBlake};
use ark_std::io::Write;
use microbench::{self,Options};


pub type H = MyBlake;

#[derive(Clone,Debug,CanonicalSerialize,CanonicalDeserialize)]
pub struct BlakeMerkleTreeParams;

impl Config for BlakeMerkleTreeParams {
   const HEIGHT: usize = 32;
   type H = H;
}



pub struct Coord<F:PrimeField>{
    pub point:(F,F)
}
impl<F:PrimeField> ToBytes for Coord<F> {
    #[inline]
    fn write<W: Write>(&self, mut writer: W) -> IoResult<()> {
	self.point.0.write(&mut writer);
	self.point.1.write(&mut writer);
        Ok(())
    }
}
impl<F:PrimeField> Oracle for Round<F>{
    type X = F;
    type Y = F;
    type C = BlakeMerkleTreeParams;
    type Domain = RSCodeDomain<F>;
    //TODO - this function is a bit nonsense and makes me realize
    //oracle should maybe be codeword - challenge and all that
    //can be kept elsewhere
    fn points_to_domain(points: Vec<Self::X>) -> Self::Domain{
	vec_to_domain(&points)
    }

    fn from_domain_and_evals(domain:Self::Domain, evals: Vec<Self::Y>) -> Self{
	Round::NonTerminalRound_(NonTerminalRound{
	    index: 0,
	    codeword: Some(Evaluations::from_vec_and_domain(evals,domain.unwrap())),
	    challenge: Some(F::one()),
	    n : 0u32,
	    k : 0u32,
	    r : 0u32
	})
    }
    fn to_vec(&self) -> Vec<(Self::X,Self::Y)>{
	let mut coords = Vec::new();
	if let Round::NonTerminalRound_(round) = self {
	    let domain = round.codeword.as_ref().unwrap().domain();
	    let evals = &round.codeword.as_ref().unwrap().evals;
	    coords = domain.elements().zip(evals).map(|(x,y)| (x,*y)).collect();
	}
	else if let Round::TerminalRound_(round) = self{
	    coords = round.poly.as_ref().unwrap().coeffs.iter().map(|c|  (*c, F::from(0u32))).collect();
            coords.insert(0,(F::from(0u32),F::from(0u32)));
	}
	coords
	
    }

   fn to_evals(&self) -> Vec<Self::Y>{
	let mut coords = Vec::new();
	if let Round::NonTerminalRound_(round) = self {
	     let domain = round.codeword.as_ref().unwrap().domain();
	    let evals = &round.codeword.as_ref().unwrap().evals;
	    coords = evals.to_vec();
	}
	else if let Round::TerminalRound_(round) = self{
	    coords = round.poly.as_ref().unwrap().coeffs.iter().map(|c|  self.to_maybe_y(&c, &F::from(0u32))).collect();
            coords.insert(0,F::from(0u32));
	}
	coords
	
    }

    fn position(&self,domain_point:&Self::X) -> usize{
	let mut position = 0;
	if let Round::NonTerminalRound_(round) = self {
	    let domain = round.codeword.as_ref().unwrap().domain();
	    position = domain.elements().position(|x| x == *domain_point).unwrap();
	}
	else if let Round::TerminalRound_(round) = self{
	    let coeffs = &round.poly.as_ref().unwrap().coeffs;
	    let maybe_position = coeffs.iter().position(|x| x == domain_point);
	    if maybe_position.is_some(){
		position = maybe_position.unwrap() + 1; //otherwise position is 0		
	    }
	}
	position
    }
    fn to_maybe_y(&self, x: &F, y : &F) ->  Self::Y {
	if let Round::TerminalRound_(round) = self{
    	    let coeffs = &round.poly.as_ref().unwrap().coeffs;
    	    let maybe_position = coeffs.iter().position(|p| x == p);
	    if maybe_position.is_none(){
		return F::from(0u32);
	    }
	}
	*y
    }
    fn hash_to_x(hash:&Vec<u8>) -> F{
	let size_in_bytes:usize = F::size_in_bits()/8;
	if hash.len() > size_in_bytes{
	    return F::from_random_bytes(&hash[0..size_in_bytes].to_vec()).unwrap();
	}
	F::from_random_bytes(hash).unwrap()
    }
}
#[test]
fn test_to_vec(){
    let l0:RSCodeDomain<Fr> = setup(4);
    let p = create_test_poly::<Fr>(6);
   let evaluation = l0.unwrap().elements().map(|e| p.evaluate(&e)).collect();
    let oracle = Round::<Fr>::from_domain_and_evals(l0,evaluation);
    let vec = oracle.to_vec();
    let no = Round::<Fr>::from_vec(&vec);
    assert_eq!(get_non_terminal_round(&no).unwrap().codeword.as_ref().unwrap().domain() == l0.unwrap(), true);
}
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
//    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct FRISetup<F:PrimeField>{
    pub log_domain: u32,
    pub n : u32,
    pub rate_param: u32,
    pub c_alphas: BTreeMap<(usize,F),Vec<(F,F)>>,
    pub equiv_classes: DomainEquivClass<F>
    //BTreeMap<usize,Vec<(F,F,F)>>,
}
impl<F:PrimeField> Hash for FRISetup<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.log_domain.hash(state);
        self.n.hash(state);
	self.rate_param.hash(state);
	self.c_alphas.hash(state);
    }
}

pub fn set_fri_setup<F:PrimeField>(log_domain:u32,n:u32,rate_param:u32,c_alphas:BTreeMap<(usize,F),Vec<(F,F)>>) -> FRISetup<F>{
    FRISetup::<F>{
	log_domain,
	n,
	rate_param,
	c_alphas,
	equiv_classes:DomainEquivClass::new()
    }
}
impl<F:PrimeField> Setup for FRISetup<F>{
}



impl<F:PrimeField> Witness for DensePolynomial<F>{
}
//this is called in first prover function of niroa
pub fn setup<F:PrimeField>(k : u32) -> (RSCodeDomain<F>){
    let mut domain = None;
    while domain == None{
	domain = Radix2EvaluationDomain::<F>::new(2u64.pow(k).try_into().unwrap());
    }
    domain
}
fn pf_1<F:PrimeField>(args: ( F, Vec<Round<F>>,FRISetup<F>,&DensePolynomial<F>))->Round<F>{
    let challenge = args.0;
    let oracles = args.1;
    let fri_setup = args.2;
    let witness = args.3;
    let l0:RSCodeDomain<F> = setup(fri_setup.log_domain);
    let now = Instant::now();
    let first_codeword = get_codeword_from_poly(&witness,l0);

    return Round::NonTerminalRound_(NonTerminalRound {codeword: first_codeword, challenge: Some(challenge),index:0, n: fri_setup.n, r:fri_setup.rate_param, k : fri_setup.log_domain});
}

fn pf_2<F:PrimeField>(args:(F,  Vec<Round<F>>, FRISetup<F>,&DensePolynomial<F>))->Round<F>{
    let challenge = args.0;
    let oracles = args.1;
    let setup = args.2;
    let witness = args.3;
    let round = get_non_terminal_round(oracles.last().unwrap()).unwrap();
    //pass in c_alpha - all elements for this round (domain,x,prod)
    get_next_round(challenge,round,setup.c_alphas,setup.equiv_classes)
}
/*
#[test]
fn test_iop_to_niroa(){
    let rho = 2;
    let k = 8;
    let n = 2;
    let new_func = iop_prover_to_niroa_prover::<Round<Fr>,FRISetup<Fr>,DensePolynomial<Fr>>(Box::new(pf_1));
    let mut frisetup = fri_setup(k,n,rho);
    let poly = create_test_poly::<Fr>(6);
    let challenge = verifier_challenge();
    let orig_oracle = pf_1((&challenge,&Vec::new(),&frisetup,&poly));
    let (new_oracle, root, trees) = new_func(&challenge,&Vec::new(),&frisetup,&poly);
    assert_eq!(get_non_terminal_round(&orig_oracle).unwrap().codeword, get_non_terminal_round(&new_oracle).unwrap().codeword);
    
}
*/
fn vf<F:PrimeField>(oracles:&Vec<Round<F>>, setup:&FRISetup<F>) -> F{
    verifier_challenge()
}

pub fn fri_setup<F:PrimeField>(k:u32,n:u32,r:u32) -> FRISetup<F>{
    let num_rounds = get_last_nt_round_index(k,r,n);
    let now = Instant::now();
    let c_alphas_no_inverse = parallel_compute_calpha_as_map(k,num_rounds,n);
    let c_alphas = parallel_inverse_calpha(c_alphas_no_inverse);

    let setup = FRISetup::<F>{
	log_domain : k,
	n : n,
	rate_param: r,
	c_alphas : c_alphas,
	equiv_classes:DomainEquivClass::new()//ec
    };
    return setup;
}

pub fn fri_iop<'a,F:PrimeField>(log_domain_size: u32, n : u32, rate_param:u32, s:&'a FRISetup<F>,p:&'a DensePolynomial<F>) -> Iop<'a,Round<F>,FRISetup<F>,DensePolynomial<F>>{
    let mut prover_functions:Vec<fn((F, Vec<Round<F>>,FRISetup<F>,&DensePolynomial<F>)) -> Round<F>> = Vec::new();
    let mut verifier_functions:Vec<Box<dyn Fn(&Vec<Round<F>>, &FRISetup<F>) -> F>> = Vec::new();
    prover_functions.push(pf_1);
    verifier_functions.push(Box::new(vf::<F>));
    let round_count = get_last_nt_round_index(log_domain_size, rate_param, n);
    for i in 0..round_count{
	prover_functions.push(pf_2);
	verifier_functions.push(Box::new(vf::<F>));
    }

    Iop{
	setup_params: &s,
	prover: Prover {
	    prover_functions,
	    witness: &p
	},
	verifier: Verifier{
	    verifier_challenges: verifier_functions,
	    get_query_points: Box::new(get_query_points::<F>),
	    verifier_query: Box::new(fri_query::<F>)
	}
    }
}
pub fn fri_commit<F:PrimeField>(mut setup : &FRISetup<F>, w: &DensePolynomial<F>) -> NiroaProof<Round<F>>{
    let temp_p = DensePolynomial::from_coefficients_slice(&[F::one()]);
    let mut friiop = fri_iop(setup.log_domain,setup.n,setup.rate_param,&mut setup, &temp_p);
    let mut fri_niroa = Niroa::<Round<F>,FRISetup<F>,DensePolynomial<F>>::from(friiop);
    fri_niroa.commit_phase(w)
}

pub fn fri_batch_commit<F:PrimeField>(mut setup : &FRISetup<F>, w: &Vec<DensePolynomial<F>>) -> NiroaBatchProof<Round<F>>{
    let temp_p = DensePolynomial::from_coefficients_slice(&[F::one()]);
    let mut friiop = fri_iop(setup.log_domain,setup.n,setup.rate_param,&mut setup, &temp_p);
    let mut fri_niroa = Niroa::<Round<F>,FRISetup<F>,DensePolynomial<F>>::from(friiop);
    fri_niroa.batch_commit(w)

}
pub fn batch_verify<F:PrimeField>(mut setup:&FRISetup<F>,proof:&NiroaBatchProof<Round<F>>) -> bool{
    //verify each individual commitment
    for p in &proof.individual_proofs{
	if(fri_verify(&mut setup, &p) == false){
	    return false;
	}
    }
    //verify paths of sums of query points againt lc root
    true
}


pub fn fri_verify<F:PrimeField>(mut setup: &FRISetup<F>, proof: &NiroaProof<Round<F>>) -> bool{
    let temp_p = DensePolynomial::from_coefficients_slice(&[F::one()]);
    let mut friiop = fri_iop(setup.log_domain,setup.n,setup.rate_param,&mut setup, &temp_p);
    let mut fri_niroa = Niroa::<Round<F>,FRISetup<F>,DensePolynomial<F>>::from(friiop);
    fri_niroa.query_phase(proof)
}
#[test]
fn test_fri_batch_niroa_correctness(){
    let rho = 2;
    let k = 10;
    let n = 2;
    let p = create_test_poly::<Fr>(6);
    let p1 = create_test_poly::<Fr>(6);
    let mut frisetup = fri_setup(k,n,rho);
    let proofs = fri_batch_commit(&mut frisetup, &vec![p,p1]);

    let result = batch_verify(&mut frisetup, &proofs);
    assert_eq!(result,true);
}
#[test]
fn test_fri_batch_niroa_soundness(){
    let rho = 2;
    let k = 4;
    let n = 2;
    let p = create_test_poly::<Fr>(6);
    let p1 = create_test_poly::<Fr>(8);
    let p2 = create_test_poly::<Fr>(10);
    let mut frisetup = fri_setup(k,n,rho);
    let proofs = fri_batch_commit(&mut frisetup, &vec![p1,p2]);
    let result = batch_verify(&mut frisetup, &proofs);
    assert_eq!(result,false);
    
}



pub fn query_polynomial<F:PrimeField>(p : &DensePolynomial<F>, points : Vec<F>,log_domain_size:u32) -> (Vec<(F,F)>, Vec<Path<BlakeMerkleTreeParams>>){
    let l0:RSCodeDomain<F> = setup(log_domain_size);
    let domain = l0.unwrap();
    let evaluation = fft_evaluate_poly(p.clone(), &domain);
    let oracle = Round::<F>::from_domain_and_evals(l0,evaluation.evals);
    let tree = oracle.to_tree();
    let mut paths = Vec::new();
    let mut coords:Vec<(F,F)> = Vec::new();
    for (i,point) in points.iter().enumerate(){
	let codeword = &get_non_terminal_round(&oracle).unwrap().codeword;
	let eval = query_codeword(codeword,point);
	coords.push((*point,eval));
	let position = get_non_terminal_round(&oracle).unwrap().codeword.as_ref().unwrap().domain().elements().position(|x| x == *point).unwrap();
	let path = tree.generate_proof(position, &eval).unwrap();
	paths.push(path);
    }
    (coords,paths)
}
/*
pub fn fri_niroa_prover<'a,F:PrimeField>(rate_param: u32, log_domain_size: u32, n: u32, polynomial: &'a DensePolynomial<F>,setup:&mut FRISetup<F>)->NiroaProof<BlakeMerkleTreeParams,Round<F>,FRISetup<F>>{
    let mut oracle = Vec::new();
    let mut challenges = Vec::new();
    let mut friiop = fri_iop(log_domain_size,n,rate_param,polynomial, &setup,&mut oracle,&mut challenges);
    let niroa_proof = Niroa::<BlakeMerkleTreeParams,Round<F>,FRISetup<F>,DensePolynomial<F>>::from(friiop);
    niroa_proof.prover
}
pub fn fri_niroa_verifier<F:PrimeField>(proof:NiroaProof<BlakeMerkleTreeParams,Round<F>,FRISetup<F>>,setup:&mut FRISetup<F>)->bool{
   (proof.verifier_query.function)(&proof.query_points,&setup, &proof.challenges)
}


#[test]
fn test_fri_niroa_correctness(){
    let rho = 2;
    let k = 4;
    let n = 2;
    let p = create_test_poly::<Fr>(3);
    let mut frisetup = fri_setup(k,n,rho);
    let niroa = fri_niroa_prover(rho,k,n,&p,&mut frisetup);
    let now = Instant::now();
    let result = fri_niroa_verifier(niroa,&mut frisetup);
    println!("niroa_verify: {}", now.elapsed().as_millis());
    assert_eq!(result,true);
}
#[test]
fn test_fri_niroa_soundness(){
    let rho = 2;
    let k = 4;
    let n = 2;
    let p = create_test_poly::<Fr>(18);
    let mut frisetup = fri_setup(k,n,rho);
    let mut oracle = Vec::new();
    let mut challenges = Vec::new();
    let mut friiop = fri_iop(k,n,rho,&p, &mut frisetup,&mut oracle,&mut challenges);
    let niroa_proof = Niroa::<BlakeMerkleTreeParams,Round<Fr>,FRISetup<Fr>,DensePolynomial<F>>::from(friiop);
    let result = (niroa_proof.prover.verifier_query.function)(&niroa_proof.prover.query_points,&frisetup, &niroa_proof.prover.challenges);
    assert_eq!(result,false);
}
#[test]
fn test_correctness(){
    let rho = 2;
    let k = 5;
    let n = 2;
    let p = create_test_poly::<Fr>(3);
    let pt = prover(rho,k,n,&p,None);
    let rand = rand_usize(Fr::size_in_bits());
    let result = verifier(&pt,rand);
    assert_eq!(result,true);
    
}
*/
#[test]
fn test_fri_niroa_soundness(){
    let rho = 2;
    let log_domain_size = 10;
    let n = 2;
    // degree needs to be bigger than 16 * 1/4 = 4
    let p = create_test_poly::<Fr>(18);
    let mut frisetup = fri_setup(log_domain_size,n,rho);
    let proof = fri_commit(&mut frisetup, &p);
    let result = fri_verify(&mut frisetup, &proof);
    assert_eq!(result,false);
}




pub fn prover<F: PrimeField>(rate_param: u32, log_domain_size: u32, n : u32, p: &DensePolynomial<F>,first_codeword:Option<Codeword<F>>)->Vec<Round<F>> {
    let l0:RSCodeDomain<F> = setup(log_domain_size);
    let first_codeword_;
    if first_codeword.is_none() {
	first_codeword_ = get_codeword_from_poly(&p,l0);
    } else {
	first_codeword_ = first_codeword.unwrap();
    }
    let cur_round = Round::NonTerminalRound_(NonTerminalRound {codeword: first_codeword_, challenge: Some(verifier_challenge()),index:0, n: n, r:rate_param, k : log_domain_size});
    let rounds = vec![cur_round];
    collect_rounds(rounds)
}

pub fn get_query_points<F:PrimeField>(o: &Vec<Round<F>>) -> Vec<Vec<(F,F)>>{
    let mut saved_query_point:Option<F> = None;
    let mut query_points = Vec::new();
    for round in o {
	let mut round_query_points = Vec::new();
	if let Round::NonTerminalRound_(r) = round {
	    if let Some(a) = saved_query_point{
       		let y = query_codeword(&r.codeword,&a);
    		if r.index == 1{

		}
		round_query_points.push((a,y));
	    }
            let initial_domain = r.codeword.as_ref().unwrap().domain();
	    let c:Vec<F> = initial_domain.elements().collect();

	    let rand = 1usize; //rand_to_lower_bound(rand_usize(F::size_in_bits()),initial_domain.size as usize);
	    let verifier_sample = sample_from_domain(r.codeword.as_ref().unwrap().domain(),rand);
            let q_ = q(r.n);
            let coset = s_y(Some(r.codeword.as_ref().unwrap().domain()),verifier_sample,&q_);

	    let ys = get_restricted_codeword(&coset,&r.codeword,Some(initial_domain));

            let mut points:Vec<(F,F)> = coset.iter().zip(ys.iter()).map(|(x,y)| (*x,*y)).collect();
	    round_query_points.append(&mut points);
	    query_points.push(round_query_points);
	    let new_domain_points  = q_.evaluate(&verifier_sample);

	    saved_query_point = Some(new_domain_points);
	}
	//terminal round
	else if let Round::TerminalRound_(r) = round {
	    //store coefficients of polynomial
	    let mut round_query_points = Vec::new();
	    let tpoly = r.poly.as_ref().unwrap();
	    //store evaluation of a
	    if let Some(a) = saved_query_point{
		round_query_points.push((tpoly.evaluate(&a),F::from(0u32)));
	    }
	    for c in tpoly.coeffs(){
		round_query_points.push((*c,F::from(0u32)));
	    }
	    query_points.push(round_query_points);
	}
    }
    query_points
}

pub fn fri_query<F:PrimeField>(query_points : &Vec<Vec<(F,F)>>, setup: &FRISetup<F>,challenges: &Vec<F>)->bool{
    //TODO : handle the case when query_points.len() < 2
    for i in 0..query_points.len(){
	//second to last round
	if i == query_points.len() - 2{
	    let points : (Vec<F>,Vec<F>) = query_points[i].iter().cloned().unzip();
	    let mut xs = points.0;
	    let mut ys = points.1;
	    if i!=0{
		xs = xs[1..].to_vec();
		ys = ys[1..].to_vec();
	    }

	    let eval = lagrange_interpolate_over_points(xs.to_vec(),ys.to_vec(),&challenges[i]);

	    let pre_coeffs: (Vec<F>,Vec<F>) = query_points[i+1].iter().cloned().unzip();
	    let coeffs = pre_coeffs.0;
	    let poly = DensePolynomial::from_coefficients_slice(&coeffs[1..]);
	    if coeffs[0] != eval{

		return false;
	    }
	    return true;
	}	
	else if i == 0{
	    let points: (Vec<F>,Vec<F>) = query_points[0].iter().cloned().unzip();
	    let lagrange_eval = lagrange_interpolate_over_points(points.0,points.1,&challenges[0]);

            if lagrange_eval != query_points[1][0].1{

		return false;
	    }
	}
	else{
	    let points: (Vec<F>,Vec<F>) = query_points[i].iter().cloned().unzip();
	    let mut xs = &points.0[1..];
	    let mut ys = &points.1[1..];
	    let evaluation = lagrange_interpolate_over_points(xs.to_vec(),ys.to_vec(),&challenges[i]);
	    let query = query_points[i+1][0].1;
    	    if evaluation != query{

		return false;
	    }
	}
	
    }
    true
}
pub fn verifier<F:PrimeField>(p : &Vec<Round<F>>,rand:usize) -> bool{    
    let mut rands = vec![rand];
    let initial_domain = get_non_terminal_round(&p[0]).unwrap().codeword.as_ref().unwrap().domain();
    //iterate through rounds, creating new randomness for each round
    for _ in p {
	rands.push(rand_to_lower_bound(rand_usize(F::size_in_bits()),initial_domain.size as usize));
    }

    let mut rand_iter = rands.iter();
    for i in 0..(p.len() - 1){
	let v = &p[i];
	let next = &p[i+1];
	let rand_i = rand_iter.next().unwrap();
        assert_eq!(rand_i <= &F::size_in_bits(),true);
	if let Some(false) = round_check(&v,&next,*rand_i){
	    return false;
	}
    }
    return true;	
}







//Round helper function
pub fn get_non_terminal_round<F:PrimeField>(r:&Round<F>)->Option<&NonTerminalRound<F>>{
    match r {
	Round::NonTerminalRound_(nt) => Some(nt),
	Round::TerminalRound_(_) => None
    }
}
//**********************get next round from current round and associated helper functions ******************//
impl<F:PrimeField> Round<F>{
    fn next(&self) -> Option<Round<F>>{
	
	match self{
	    //stubbed inputo for challenge
	    //btree map argument doesn't make sense but this function is only used interactively anyway
	    Round::<F>::NonTerminalRound_(round) => Some(get_next_round(F::from(1u32),round,BTreeMap::new(),DomainEquivClass::new())),
	    Round::<F>::TerminalRound_(_) => None
	}
    }
}

fn get_last_nt_round_index(k : u32, r:u32, n:u32) -> usize{
    let r_:f64 = ((k - r)/n) as f64;
    r_.floor() as usize
}

fn is_next_round_terminal<F:PrimeField>(curr_round : &NonTerminalRound<F>) -> bool{
    let last_round = get_last_nt_round_index(curr_round.k, curr_round.r, curr_round.n);
    if last_round > 0 && curr_round.index < last_round - 1 {
	return false;
    }
    else{
	return true;
    }
}

//This function outputs the upper bound of the degree of the polynomial that the points in the codeword interpolate to
fn get_max_degree<F:PrimeField>(c : &Codeword<F>, r : u32,k: u32) -> usize{
    if k == r{
	return 0;
    }
    let rho = (2u32 as f32).powi(-1 * (r as i32));	 
    let d = (rho * (c.as_ref().unwrap().domain().size as f32)) as usize - 1;
    return d;
}


//get next round from current round
fn get_next_round<F:PrimeField>(challenge: F, curr_round : &NonTerminalRound<F>,c_alphas:BTreeMap<(usize,F),Vec<(F,F)>>,equiv_classes:DomainEquivClass<F>) -> Round<F>{
    //passing in c_alpha - it's domain, x , prod
    let next_codeword = get_codeword_from_codeword(&curr_round.codeword,curr_round.challenge.unwrap(),curr_round.n,c_alphas,curr_round.index,&equiv_classes);
    if is_next_round_terminal(&curr_round) == false{
	return Round::NonTerminalRound_(NonTerminalRound{
	    index: curr_round.index + 1,
	    codeword: next_codeword,
	    challenge: std::option::Option::Some(challenge),
	    n : curr_round.n,
	    k: curr_round.k,
	    r : curr_round.r
	});
    }
    else {
	let now = Instant::now();
	let last_interpolation = next_codeword.as_ref().unwrap().interpolate_by_ref();

	return Round::<F>::TerminalRound_(TerminalRound{
	    poly:Some(get_first_d_coeffs(get_max_degree(&next_codeword,curr_round.r,curr_round.k) + 1,
					 last_interpolation)),
	    domain: Some(next_codeword.as_ref().unwrap().domain())
	});
    }
}
/*
fn create_closure<F:PrimeField>(equiv_classes:BTreeMap<F,Vec<F>>, challenge: F, c: &Codeword<F>) -> Box<dyn Fn(F) -> F>{
    Box::new(|y| interpolate_eval(&equiv_classes.get(&y).unwrap().to_vec(),challenge,&c))
}
*/
fn parallel_zero_y<F:PrimeField>(coset:HashMap<F,Vec<F>>) -> HashMap<F,F>{
    let mut output = vec![F::one();coset.len()];
    let results = parallel_hashmap_noaux::<F,Vec<F>,F>(coset,prods);
    results
}

fn get_codeword_from_codeword<F:PrimeField>(c :  &Codeword<F>, challenge: F, n:u32 ,c_alpha:BTreeMap<(usize,F),Vec<(F,F)>>,round_num:usize,equiv_classes:&DomainEquivClass<F>) -> (Codeword<F>){
    //    let q = &util::q_power(n);

    let equiv_subtracts = EquivClass::get_equiv_classes(&c,challenge);//,equiv_classes,round_num);
    let subtracts = equiv_subtracts.0;
    let equiv_classes = equiv_subtracts.1;


    let zero_sy = parallel_zero_y(subtracts.clone());

    let unflattened_inverses = parallel_batch_inverse_map(&subtracts);

    let mut range_points = Vec::new();
    let new_ys = parallel_interpolate(c_alpha,equiv_classes,zero_sy,unflattened_inverses,round_num,challenge);
    let domain = vec_to_domain(&new_ys.0);
    for d in domain.as_ref().unwrap().elements(){
	range_points.push(new_ys.1.get(&d).unwrap().clone());
    }
   let output = (Some(Evaluations::from_vec_and_domain(range_points.clone(),domain.unwrap())));

    return output;

}

fn hashmap_insert<F: PrimeField>(key : F, val: F, hm : &mut HashMap<F,Vec<F>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
fn subtract_challenge<F:PrimeField>(cosets:&EquivClass<F>,challenge:&F) -> HashMap<F,Vec<F>>{
    let mut new_map = HashMap::new();
    for (key,val) in &cosets.equiv_classes{
	for x in val{
    	    hashmap_insert(*key,(*challenge - x.0),&mut new_map);
	}
    }
    new_map
}
fn subtract_el<F:PrimeField>(cosets:Vec<(Vec<F>,Vec<F>,BTreeMap<F,F>)>,challenge:F) -> Vec<Vec<F>>{
    let mut results = Vec::new();
    for p in &cosets{
        let mut operands = Vec::new();
	for x in &p.0{
	    operands.push(*x - challenge);
	}
	results.push(operands);
    }
    results
}
pub fn get_points_to_interpolate<F:PrimeField>(coset_inds : &Vec<F>, challenge:&F, c: &Codeword<F>,equiv_classes:&BTreeMap<F,Vec<F>>) -> Vec<(Vec<F>,Vec<F>,F)>{
    //wrangle coset_ind,c, equiv_classes into [(xs,ys)] a vector of tuples of vectors

    let domain = Some(c.as_ref().unwrap().domain());
    let mut point_sets = Vec::new();

    for coset_ind in coset_inds{
	let xs = &equiv_classes.get(&coset_ind).unwrap().to_vec();
	let now = Instant::now();
	let ys = get_restricted_codeword(xs,&c,domain);

	point_sets.push((xs.to_vec(),ys.to_vec(),*coset_ind));
    }

    point_sets
}
//not use by above functions, but used by prover to get first round, and used by verifier to get last round
fn get_codeword_from_poly<F:PrimeField>(p : &DensePolynomial<F>, d : RSCodeDomain<F>) -> Codeword<F>{
    let evals = match d {
	None => None,
	Some(_) => Some(fft_evaluate_poly(p.clone(),&d.unwrap()))//Some(d.unwrap().elements().map(|e| {p.evaluate(&e)}).collect())
    };
    evals
    /*
    match evals {
	None => None,
	Some(c) => Some(Evaluations::from_vec_and_domain(c,d.unwrap()))
    }
*/	
}
/************************************************************************************************/




#[test]
fn test_setup(){
    let domain:RSCodeDomain::<Fr> = setup(2);
    assert_eq!(domain.unwrap().size,4);
    let options = Options::default();
    microbench::bench(&options, "setup", || setup::<Fr>(2));
}
#[test]
fn test_subgroups(){
    use util::get_subgroup;
    let initial_subgroup:RSCodeDomain::<Fr> = setup(10);
    let new_subgroup = get_subgroup(&initial_subgroup.unwrap(),8);
    let result = new_subgroup.unwrap().size();
    assert_eq!(result,8);
    
}


fn insert<F: PrimeField>(key : F, val: F, hm : &mut BTreeMap<F,Vec<F>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
#[test]
fn test_insert(){
    let mut hm = BTreeMap::new();
    insert(Fr::from(3u64), Fr::from(4u64),&mut hm);
    insert(Fr::from(3u64), Fr::from(17u64),&mut hm);
    assert_eq!(hm.get(&Fr::from(3u64)).unwrap().len(),2);
    insert(Fr::from(3u64),Fr::from(25u64),&mut hm);
    assert_eq!(hm.get(&Fr::from(3u64)).unwrap().len(),3);
}

fn vec_to_domain<F:PrimeField>(v: &Vec<F>)->RSCodeDomain<F>{
    assert_eq!(v.len()<=1,false);
    let group_gen = find_generator_from_vec(&v);
    let domain = get_subgroup_from_gen(group_gen, v.len() as u64);
    domain
}
fn get_next_domain<F:PrimeField>(q : &SparsePolynomial<F>, prev_domain: RSCodeDomain<F>)->(RSCodeDomain<F>,BTreeMap<F,Vec<F>>){
    if prev_domain == None{
	return (None,BTreeMap::new());
    }
    let mut equiv_classes = BTreeMap::new();
    for elem in prev_domain.unwrap().elements(){
	insert(q.evaluate(&elem),elem, &mut equiv_classes);
    }
    let elems:Vec<F> = Vec::from_iter(equiv_classes.keys().map(|e| *e));
    let domain = vec_to_domain(&elems);
    (domain,equiv_classes)
}


#[test]
fn test_get_next_domain(){
    let k = 10;
    let n = 2;
    let lo:RSCodeDomain<Fr> = setup(k);
    let q_ = q(n);
    let l1 = get_next_domain(&q_,lo);
    let options = Options::default();
    microbench::bench(&options, "get_next_domain domain size 2^10", || get_next_domain(&q_,lo));
    for (_,val) in l1.1.iter(){
	assert_eq!(val.len(),2usize.pow(n));
    }
    //correct size
    assert_eq!(l1.0.unwrap().size, 2u64.pow((k - n) as u32));
    //domain matches keys
    assert_eq!(Vec::from_iter(l1.1.keys().map(|e| *e)).sort(),Vec::from_iter(l1.0.unwrap().elements()).sort());
    
}



fn add_restr_el<F : PrimeField >(restriction: &Vec<F>, index:usize,x:F) -> Option<usize>{
    let result = restriction.into_iter().find(|y| y == &&x);

    if result.is_none(){
	return None;
    }
    else{
	return Some(index);
    }	
}


fn get_restricted_indices<F:PrimeField>(restriction: &Vec<F>, d : RSCodeDomain<F>) -> Vec<Option<usize>> {
    d.unwrap().elements().enumerate().map(|(i,x)|-> Option<usize>{return add_restr_el(&restriction,i,x);}).collect()
}


fn get_restricted_codeword<F:PrimeField>(x : &Vec<F>, c: &Codeword<F>, domain: RSCodeDomain<F>) -> (Vec<F>){
    let now = Instant::now();
    let indices = get_restricted_indices(&x,domain);

    let orig_y = &c.as_ref().unwrap().evals;
    let mut new_y = Vec::new();
    for i in indices{
	if i.is_some(){
	    new_y.push(orig_y[i.unwrap()]);
	}
    }
    new_y
}
/*
pub fn parallel_interpolate_eval<F:PrimeField>(ys : &Vec<F> ,challenge:F,c : &Codeword<F>,equiv_classes:&BTreeMap<F,Vec<F>>,c_alpha:&Vec<(F,F,F)>,zero_y:Vec<F>,coset_inverses:Vec<Vec<F>>) -> Vec<F> {
    let domain = Some(c.as_ref().unwrap().domain());

    let cores:usize = num_cpus::get();
    let max = ys.len();
    let (snd,rcv) = bounded(1);
    let mut prods = Vec::new();
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let remainder = max % cores;
	let mut next = 0;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let cosets = &ys[next..(next + this_batch_size)];
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    s.spawn(move |_| {
		for i in 0..this_batch_size{
       		    let xs = &equiv_classes.get(&cosets[i]).unwrap().to_vec();
		    let ys = get_restricted_codeword(xs,&c,domain);
			//find all elements of calpha with domain_point = cosets[i] - pass in Map of (alpha,product)
		    let mut map = BTreeMap::new();
		    for a in c_alpha{
			if a.0 == cosets[i]{
			    map.insert(a.1,a.2);
			}
		    }
			sen.send(((next / this_batch_size),lagrange_interpolate_with_precompute_tuple((xs.to_vec(),ys,&challenge,map,zero_sy,coset_inverses)))).unwrap();
				  //lagrange_interpolate_with_precompute(xs.to_vec(),ys,&challenge,map))).unwrap();
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    prods.push(msg);
	}
    }).unwrap();
    
    prods.sort_by(|a,b| a.0.partial_cmp(&b.0).unwrap());
    prods.iter().map(|(i,e)| *e).collect()
}
*/
fn get_all_domains<F:PrimeField>(log_domain_size:u32,num_rounds:usize,coset_size_log:u32) -> Vec<(usize,F,Vec<F>)>{
    // Each domain maps to a set of cosets in previous domain
    //first get the first domain
    let mut prev_domain = None;
    while prev_domain == None {
	prev_domain = Radix2EvaluationDomain::<F>::new(2u64.pow(log_domain_size).try_into().unwrap());
    }
    //each element of sys is (round_num,domain_point,coset in prev domain)
    let mut sys : Vec<(usize,F, Vec<F>)> = Vec::new();
    //cosets is a set of cosets - one for each element of next domain
    for i in 0..num_rounds{
	//each round - domain = domain associated with round
	//cosets = cosets in last round - each one maps to domain point in domain
	let (domain,cosets) = get_next_domain(&q(coset_size_log),prev_domain);
	//key is point in domain, val is one coset : Vec<F>
	for (key,val) in cosets{
	    sys.push((i,key,val));
	}
	prev_domain = domain;
    }
    sys
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

pub fn compute_calpha<F:PrimeField>(log_domain_size:u32,num_rounds:usize,coset_size_log:u32) -> Vec<(usize,F,F,F)>{
    let cosets = get_all_domains(log_domain_size,num_rounds,coset_size_log);
    let mut everything = Vec::new();
    for (round_num,domain_point,coset) in &cosets{
	let mut prods = Vec::new();
	for x in coset{
	    prods.push((*round_num,*domain_point,*x,prod_except_inverse(&coset,&x)));
	}
	everything.append(&mut prods);
    }
    everything
}
#[test]
fn profile_compute_calpha(){
    let k = 13u32;
    let r = 1u32;
    let n = 2u32;
    let now = Instant::now();
    let num_rounds = get_last_nt_round_index(k,r,n);
    let c_alpha = compute_calpha::<Fr>(k,num_rounds,n);

}
#[test]
fn profile_parallel_compute_calpha(){
    let k = 20u32;
    let r = 1u32;
    let n = 2u32;
    let now = Instant::now();
    let num_rounds = get_last_nt_round_index(k,r,n);
    let c_alpha = parallel_compute_calpha::<Fr>(k,num_rounds,n);

    //k = 13 : n = 2: 365 ms, n = 4: 303, n = 6: 342ms
    
}
pub fn parallel_compute_calpha<F:PrimeField>(log_domain_size:u32,num_rounds:usize,coset_size_log:u32) -> Vec<(usize,F,F,F)>{
    let cosets = get_all_domains(log_domain_size,num_rounds,coset_size_log);
    let cores:usize = num_cpus::get();
    let max = cosets.len();
    let mut everything = Vec::new();
    let (snd,rcv) = bounded(1);
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for c in 0..cores{
	    let mut this_batch_size = 0usize;
    	    if c < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    //create a slice
	    let cosets_slice = &cosets[next..(next + this_batch_size)];
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    s.spawn(move |_| {
	        let now = Instant::now();    
		for i in 0..this_batch_size{
		    let (round_num,domain_point,coset) = &cosets_slice[i];
		    let mut prods = Vec::new();
		    for x in coset{
			prods.push((*round_num,*domain_point,*x,prod_except_inverse(&coset,&x)));
		    }
		    sen.send(prods).unwrap();
      	         
		}

	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for mut msg in rcv.iter(){
	    everything.append(&mut msg);
	}
    }).unwrap();
    
    everything.sort_by(|a,b| (*a).0.partial_cmp(&b.0).unwrap());
    everything
}
pub fn parallel_compute_calpha_as_map<F:PrimeField>(log_domain_size:u32,num_rounds:usize,coset_size_log:u32) -> BTreeMap<(usize,F),Vec<(F,F)>>{
    let cosets = get_all_domains(log_domain_size,num_rounds,coset_size_log); //this is equivalent to get_equivalence_classes
    let cores:usize = num_cpus::get();
    let max = cosets.len();
    let mut everything = BTreeMap::new();
    let (snd,rcv) = bounded(1);
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for c in 0..cores{
	    let mut this_batch_size = 0usize;
    	    if c < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    //create a slice
	    let cosets_slice = &cosets[next..(next + this_batch_size)];
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    s.spawn(move |_| {
	        let now = Instant::now();    
		for i in 0..this_batch_size{
		    let (round_num,domain_point,coset) = &cosets_slice[i];
		    let mut prods = Vec::new();
		    for x in coset{
			prods.push((*round_num,*domain_point,*x,prod_except_inverse(&coset,&x)));
		    }
		    sen.send(prods).unwrap();
      	         
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for mut msg in rcv.iter(){
	    for m in msg{
		let t:(usize,F,F,F) = m;

		everything.entry((t.0,t.1)).and_modify(|vec:&mut Vec<(F,F)>| {vec.push((t.2,t.3))}).or_insert(vec![(t.2,t.3)]);
	    }
	}
    }).unwrap();

    everything
}
fn interpolate_eval<F:PrimeField>(xs : &Vec<F>, challenge:F, c:&Codeword<F>) -> F{
    let domain = Some(c.as_ref().unwrap().domain());
    let ys = get_restricted_codeword(xs,&c,domain);
    lagrange_interpolate_over_points(xs.to_vec(),ys,&challenge)
}

#[test]
fn test_interpolate_eval(){
    let challenge = verifier_challenge();
    let poly = test_poly();
    let domain:RSCodeDomain<Fr> = setup(4);
    let c1 = get_codeword_from_poly(&poly,domain);
    let d = Some(c1.as_ref().unwrap().domain());
    let q = util::q(2);
    let next = get_next_domain(&q,d);
    let y = next.0.unwrap().elements().next().unwrap();
    let coset = next.1.get(&y).unwrap().to_vec();
    let t1 = interpolate_eval(&coset,challenge,&c1);
    let t2 = interpolate_eval(&coset,challenge,&c1);
    let options = Options::default();
    microbench::bench(&options, "interpolate eval", || interpolate_eval(&coset,challenge,&c1));
    assert_eq!(t1,t2);
}
/*
#[test]
fn test_parallel_interpolate_eval(){
    let challenge = verifier_challenge();
    let poly = test_poly();
    let domain:RSCodeDomain<Fr> = setup(4);
    let c1 = get_codeword_from_poly(&poly,domain);
    let d = Some(c1.as_ref().unwrap().domain());
    let q = util::q(2);
    let next = get_next_domain(&q,d);
    let equiv_classes = next.1;
    // sequential interpolate eval
    let mut new_ys = Vec::new();
    for y in next.0.unwrap().elements(){
	new_ys.push(interpolate_eval(&equiv_classes.get(&y).unwrap().to_vec(),challenge,&c1));
    }
    let par_ys = parallel_interpolate_eval(&next.0.unwrap().elements().collect(),challenge,&c1,&equiv_classes);
    assert_eq!(new_ys,par_ys);
}
*/

/*
fn test_get_codeword_from_codeword(max_degree:usize){
    let n = 2;
    let log_degree_plus1 = (((max_degree + 1) as f64).log2()).ceil() as u32;
    let log_domain_size = log_degree_plus1 + 2;
    let l0:RSCodeDomain<Fr> = setup(log_domain_size);
    let poly_to_commit = create_test_poly(max_degree);
    let q:SparsePolynomial<Fr> = util::q(n);
    let codeword0 = get_codeword_from_poly(&poly_to_commit,l0);
    assert_eq!(&codeword0.as_ref().unwrap().evals.len(),&2usize.pow(log_domain_size as u32));
    let k1 = log_domain_size - n;

    let options = Options::default();
    microbench::bench(&options, "get_next_codeword0", || get_codeword_from_codeword(&codeword0, Fr::from(82u64), &q));

    let codeword1 = get_codeword_from_codeword(&codeword0, Fr::from(82u64), &q);
    assert_eq!(&codeword1.as_ref().unwrap().evals.len(),&2usize.pow(k1 as u32));

}
*/

//d = max_degree + 1 = 2^{-R} * |L^{r}| - 1 + 1 = 2^{-R} * |L^{r}|
fn get_first_d_coeffs<F:PrimeField>(d : usize, poly : DensePolynomial<F>)->DensePolynomial<F>{
    let mut coeffs_iter = poly.coeffs.iter();
    let mut new_coeffs = Vec::new();
    for _ in 0..d{
    	if let Some(c) = coeffs_iter.next(){
	       new_coeffs.push(*c);
	}
	else{
	   break;
	}

    }
    return DensePolynomial::from_coefficients_slice(&new_coeffs[..]);
}

//iterative alternative to collect_rounds
fn iterative_collect_rounds<F:PrimeField>(first_round:Round<F>,round_count:usize) -> Vec<Round<F>>{
    let mut rounds:Vec<Round<F>> = vec![first_round];
    for _ in 1..round_count{
	rounds.push(rounds.last().unwrap().next().unwrap());
    }
    return rounds;
}

fn collect_rounds<F:PrimeField>(mut rounds:Vec<Round<F>>) -> Vec<Round<F>>{
    if let Round::TerminalRound_(_) = rounds.last().unwrap(){
	return rounds;
    }
    else{
	rounds.push(rounds.last().unwrap().next().unwrap());
	return collect_rounds(rounds);
    }
}

    




//Verifier:

// Get equivalence class s_y defined by q(x) = x^{2^{n}} = y /
fn s_y<F: PrimeField>(d : RSCodeDomain<F> , x : F, q : &SparsePolynomial<F>) -> Vec<F>{
    let y = q.evaluate(&x);
    let mut coset = Vec::new();
    for elem in d.unwrap().elements(){
	if q.evaluate(&elem) == y {
	    coset.push(elem);
	}
    }
    return coset;
}



pub fn query_codeword<F : PrimeField >(c : &Codeword<F>, x: &F) -> F{
    let domain:Vec<F> = c.as_ref().unwrap().domain().elements().collect();
    let vec = get_restricted_indices(&vec![*x],Some(c.as_ref().unwrap().domain()));

    let mut result = None;
    for (index, e) in vec.iter().enumerate(){
	if e.is_some(){
	    result = Some(index);
	}
    }
    if(result == None){
	panic!("Element not found in codeword domain");
    }
    return (c).as_ref().unwrap().evals[result.unwrap()];

}


fn round_consistency<F:PrimeField>(coset : Vec<F>, c_i : &Codeword<F>, c_iplus1 : &Codeword<F> , verifier_challenge : F, verifier_sample : F) -> bool{
    let c1 = query_codeword(c_iplus1,&verifier_sample);
    //interpolate over {(x,y): x is in coset,  (x,y) is in c_i, and then evaluate result at verifier_challenge
    let now = Instant::now();
    let e = interpolate_eval(&coset,verifier_challenge,c_i);

    //this should be equal to the next codeword queried at verifier_sample (coset comes from sample)
    c1 == e

}


//this is used by vlpa19 verifier
pub fn get_coset_from_codeword<F:PrimeField>(domain:RSCodeDomain<F>,sample:F,n:u32)->Vec<F>{
    let q_ = q(n);
    s_y(domain,sample,&q_)
}
fn round_check_helper<F:PrimeField>(r: &NonTerminalRound<F>,next_codeword:&Codeword<F>,rand:usize) -> bool{
    let q_ = q(r.n);
    let rand_ = 1usize;//rand_to_lower_bound(rand,r.codeword.as_ref().unwrap().domain().size as usize);
    let verifier_sample = sample_from_domain(r.codeword.as_ref().unwrap().domain(),rand_);
    let coset = s_y(Some(r.codeword.as_ref().unwrap().domain()),verifier_sample,&q_);
    let round_test = round_consistency(coset, &(r.codeword), (&next_codeword),r.challenge.unwrap(),q_.evaluate(&verifier_sample));
    return round_test;
}
fn round_check<F:PrimeField>(round_i : &Round<F>, round_iplus1: &Round<F>,rand:usize)->Option<bool>{
    if let Round::NonTerminalRound_(r) = round_i{
	match round_iplus1{
	    Round::TerminalRound_(TerminalRound{poly,domain}) => return Some(round_check_helper(r,&get_codeword_from_poly(poly.as_ref().unwrap(),*domain),rand)),
	    Round::NonTerminalRound_(r_next) => return Some(round_check_helper(r,&r_next.codeword,rand))
	}
    }
    else{
	return None;
    }
}
/********** TESTs *************************/
/*
#[test]
fn test_query_codeword2(){
    let q_ = util::q(2);
    let domain = setup(4);
    let poly = test_poly();
    let codeword = get_codeword_from_poly(&poly, domain);
    let next_codeword = get_codeword_from_codeword(&codeword,verifier_challenge(),&q_);
    let rand = rand_usize(codeword.as_ref().unwrap().domain().size as usize);
    let sample = sample_from_domain(codeword.as_ref().unwrap().domain(),rand);
    let next_c_el = q(2).evaluate(&sample);
    query_codeword(&next_codeword,&next_c_el);
}
*/

fn test_poly() -> DensePolynomial<Fr>{
    let coeffs:[Fr;16] = [Fr::from(1u64),Fr::from(2u64),Fr::from(3u64),Fr::from(4u64),Fr::from(5u64),Fr::from(1u64),Fr::from(2u64),Fr::from(3u64),Fr::from(4u64),Fr::from(5u64),Fr::from(5u64),Fr::from(1u64),Fr::from(2u64),Fr::from(3u64),Fr::from(4u64),Fr::from(5u64)];
    return DensePolynomial::from_coefficients_slice(&coeffs);
}

fn create_test_poly<F:PrimeField>(degree : usize) -> DensePolynomial<F>{
    let mut coeffs = Vec::<F>::new();
    for _ in (0..degree){
	coeffs.push(verifier_challenge());
    }
    return DensePolynomial::from_coefficients_slice(&coeffs);
}
#[test]
fn test_create_test_poly(){
    let p = create_test_poly::<Fr>(10);
    assert_eq!(p.coeffs.len(),10);
}
#[test]
fn test_query_codeword(){
    let domain = setup(4);
    let poly = test_poly();
    let codeword = get_codeword_from_poly(&poly,domain);
    let x_1 = codeword.as_ref().unwrap().domain().elements().next().unwrap();
    let y = poly.evaluate(&x_1);
    let y_ = query_codeword(&codeword, &x_1);
    assert_eq!(y,y_);
}


#[test]
fn test_evaluating_lower_than_domain(){
    let domain = setup(10); //domain of size 16
    let poly = create_test_poly::<Fr>(18);
    let evals = domain.unwrap().elements().map(|e| poly.evaluate(&e)).collect();
    let codeword = Some(Evaluations::from_vec_and_domain(evals,domain.unwrap()));
    let options = Options::default();
    microbench::bench(&options, "from vec and domain", ||Evaluations::from_vec_and_domain(domain.unwrap().elements().map(|e| poly.evaluate(&e)).collect(),domain.unwrap()));
    let poly_again = codeword.as_ref().unwrap().interpolate_by_ref();
    assert_eq!(poly_again.coeffs.len() == 16,false);
}
			


//#[test]
fn test_correctness_zeroth_poly(){
    let rho = 2;
    let k = 6;
    let n = 2;
    let p = create_test_poly::<Fr>(0);
    let pt = prover(rho,k,n,&p,None);
    let rand = rand_usize(Fr::size_in_bits());
    let result = verifier(&pt,rand);
    assert_eq!(result,true);
}








