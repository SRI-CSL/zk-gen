use crate::data_structures::{UniversalParams,CommitterKey,VerifierKey,PreparedVerifierKey,Commitment,Randomness,Proof,FriProof,TempProof,WitnessProof};
use ark_ff::{One,BigInteger256,Fp256,Zero};
use std::collections::{BTreeMap};
use rand_core::RngCore;
use ark_std::{string::String,marker::PhantomData,io::{Read,Write},ops::{Mul,Sub,Div,Neg,SubAssign,Add,AddAssign}};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use fri::fri::{FRISetup, BlakeMerkleTreeParams,data_structures::{RSCodeDomain,Round,Codeword},setup,fri_batch_commit, batch_verify, fri_commit, fri_verify, prover,query_polynomial, get_non_terminal_round,fri_iop,set_fri_setup,get_coset_from_codeword,query_codeword,verifier,fri_setup,niroa::{NiroaBatchProof,NiroaProof},util::{rand_usize,sample_from_domain,verifier_challenge,rand_to_lower_bound,lagrange_interpolate_over_points}};

use ark_test_curves::bls12_381::{Fr, FrParameters};
use ark_ff::{PrimeField,Field};
use ark_poly::{domain::{EvaluationDomain,GeneralEvaluationDomain,Radix2EvaluationDomain},polynomial::{Polynomial,univariate::{DenseOrSparsePolynomial,DensePolynomial,SparsePolynomial}, UVPolynomial}};
use ark_poly_commit::{PolynomialCommitment,data_structures::*,error::Error};
use ark_crypto_primitives::Path;
use derivative::Derivative;
struct CommitmentError{
    msg: u32
}

fn simulate_opening_queries<F:PrimeField>(commitment_y: &F, commitment_x: &F, witness_y: &F,opening_challenge:&F,opening_eval:&F)->bool{
    let simulated_query = (*commitment_y - *opening_eval) / (*commitment_x - *opening_challenge);
    if simulated_query != *witness_y{
	return false;
    }
    return true;
	
}
fn divide<F:PrimeField>(n:&DensePolynomial<F>,d:&DensePolynomial<F>)->Option<(DensePolynomial<F>,DensePolynomial<F>)>{
    DenseOrSparsePolynomial::from(n).divide_with_q_and_r(&DenseOrSparsePolynomial::from(d))
}
#[test]
fn test_divide(){
    let n = DensePolynomial::from_coefficients_slice(&[Fr::from(0u64),Fr::from(7u64),Fr::from(11u64),Fr::from(134u64)]);
    let d = DensePolynomial::from_coefficients_slice(&[Fr::from(0u64),Fr::from(1u64)]);
    let p = divide(&n,&d).unwrap().0;
    let point = verifier_challenge();
    let p_eval = p.evaluate(&point);
    let sim_eval = n.evaluate(&point) / d.evaluate(&point);
    assert_eq!(p_eval,sim_eval);
    
}
#[test]
fn test_subtract(){
    let point = verifier_challenge();
    let poly = &DensePolynomial::from_coefficients_slice(&[Fr::from(0u64),Fr::from(7u64),Fr::from(11u64),Fr::from(134u64)]);
    let eval = poly.evaluate(&point);
    let numerator = poly - &DensePolynomial::from_coefficients_slice(&[eval]);
    let new_point = verifier_challenge();
    assert_eq!(numerator.evaluate(&new_point),poly.evaluate(&new_point) - eval);
}
fn get_prover_poly_from_point<F:PrimeField>(point : &F, poly:&DensePolynomial<F>)->Option<(DensePolynomial<F>,DensePolynomial<F>)>{
    let eval = poly.evaluate(&point);
    let numerator = poly - &DensePolynomial::from_coefficients_slice(&[eval]);
    let denominator = &DensePolynomial::from_coefficients_slice(&[F::from(0u64),F::from(1u64)]) - &DensePolynomial::from_coefficients_slice(&[*point]);
    divide(&numerator,&denominator)
}
//for testing purposes
fn fake_get_prover_poly_from_point<F:PrimeField>(point : F, fake_eval:F, poly:&DensePolynomial<F>)->Option<(DensePolynomial<F>,DensePolynomial<F>)>{
    let numerator = poly - &DensePolynomial::from_coefficients_slice(&[fake_eval]);
    let denominator = &DensePolynomial::from_coefficients_slice(&[F::from(0u64),F::from(1u64)]) - &DensePolynomial::from_coefficients_slice(&[point]);
    divide(&numerator,&denominator)
}

#[test]
fn test_get_ppfp(){
    let poly = DensePolynomial::from_coefficients_slice(&[Fr::from(2u64),Fr::from(5u64)]);
    let point = Fr::from(2u64);
    let result = get_prover_poly_from_point(&point,&poly);
    assert_eq!(result.as_ref().unwrap().1,DensePolynomial::from_coefficients_slice(&[]));
    let new_poly = result.unwrap().0;
    let rand_field_el = verifier_challenge();
    let simulated_new_poly = (poly.evaluate(&rand_field_el) - poly.evaluate(&point)) / (rand_field_el - point);
    assert_eq!(simulated_new_poly,new_poly.evaluate(&rand_field_el));

}
#[derive(Derivative,CanonicalSerialize,CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
//#[derive(CanonicalSerialize, CanonicalDeserialize, Clone, Default, Debug)]
pub struct Vlpa19<F:PrimeField>{
    test:F
}

impl<F:PrimeField> Vlpa19<F>{
    pub fn new(degree:usize) -> Self{
	Vlpa19{
	    test: F::one()
	}
    }
    pub fn update(&mut self){
	self.test = F::from(6u32);
    }
    pub fn setup(n: u32,k:u32,rate_param:u32,max_degree:usize) -> UniversalParams<F>{

	let initial_domain = setup(k);
        UniversalParams{
	    log_domain_size:k,
	    initial_domain,
	    n,
	    rate_param,
	    max_degree

	 }
    }
    pub fn bucket_by_degree(polynomials:&Vec<LabeledPolynomial<F,DensePolynomial<F>>>) -> BTreeMap<usize,Vec<LabeledPolynomial<F,DensePolynomial<F>>>>{
	let mut degree_map = BTreeMap::new();
	for p in polynomials{
	    degree_map.entry(p.polynomial().degree()).and_modify(|vec:&mut Vec<LabeledPolynomial<F,DensePolynomial<F>>>| { vec.push(p.clone())}).or_insert(vec![p.clone()]);
	}
	degree_map
    }
    fn get_min_log_domain(degree:usize,rate_param:u32) -> u32{
	//actually want to take ceil for degrees that are not powers of 2
	//but if it is a power of 2, then we will need to add 1
	//so take floor and then add 1 to accomodate both cases
	    let mut floor_log_degree = ((degree as f64).log2()).floor() as u32;
	    floor_log_degree + rate_param + 1
    }

    //this should return an NiroaBatchProof
    pub fn batch_commit(params:&CommitterKey<F>,c_alpha:BTreeMap<(usize,F),Vec<(F,F)>>,polynomials:&Vec<LabeledPolynomial<F,DensePolynomial<F>>>)-> Vec<LabeledCommitment<Commitment<F>>>{

	let mut commitments = Vec::new();
	let degree_map = Vlpa19::bucket_by_degree(polynomials);
	let mut setup = params.setup.clone();
//        let mut setup = setup//set_fri_setup(params.log_domain_size,params.n,params.rate_param,c_alpha);

	for (degree,batch) in degree_map{
	    setup.log_domain = Self::get_min_log_domain(degree,params.rate_param);
	    let polys = batch.iter().by_ref().map(|p| p.polynomial().clone()).collect();

	    let labels:Vec<String> = batch.iter().by_ref().map(|p| p.label().clone()).collect();
	    let proofs = fri_batch_commit(&mut setup,&polys);
	    for (i,p) in proofs.individual_proofs.iter().enumerate(){
		let commitment = Commitment{
		    fri_proof: FriProof(p.clone()),
		    lc_eval_root: proofs.linear_combination_eval_root.clone(),
		    degree_bound: degree,
		    label: labels[i].to_string()
		};
		let lc = LabeledCommitment::new(labels[i].to_string(),commitment,Some(degree));
		commitments.push(lc);
	    }
	}
	commitments
    }
    pub fn commit(params:&CommitterKey<F>,c_alpha:BTreeMap<(usize,F),Vec<(F,F)>>,polynomial:&DensePolynomial<F>)->Commitment<F>{
	let mut setup = set_fri_setup(params.log_domain_size,params.n,params.rate_param,c_alpha);
	let proof = fri_commit(&mut setup, polynomial);
	let root = proof.roots[0].clone();
	Commitment{
	    fri_proof:FriProof(proof),
	    lc_eval_root: root,
	    degree_bound:polynomial.degree(),
	    label: "proof".to_string()
	}
    }
    pub fn transform_points(points:&Vec<(F,F)>,query:&F,eval:&F) -> Vec<(F,F)>{
	let mut witness_round = Vec::new();
	for point in points{
	    let numerator = point.1 - eval;
	    let denominator = point.0 - query;
	    witness_round.push((point.0,numerator / denominator));
	}
	witness_round
    }
    fn create_test_poly(degree : usize) -> DensePolynomial<F>{
	let mut coeffs = Vec::<F>::new();
	for _ in (0..degree){
	    coeffs.push(F::from(2u32));
	}
	return DensePolynomial::from_coefficients_slice(&coeffs);
    }

    fn generate_proof(lc: Vec<LabeledCommitment<Commitment<F>>>, poly: &DensePolynomial<F>,opening_challenge:F,ck:&CommitterKey<F>,eval:&F,degree_bound:usize,rate_param:u32) -> (FriProof<F>, Vec<(F,F)>, Vec<Path<BlakeMerkleTreeParams>>){
	let witness_polynomial = get_prover_poly_from_point(&opening_challenge,&poly).unwrap().0;

	//commit to witness polynomial

	let mut setup = ck.setup.clone(); //set_fri_setup(ck.log_domain_size,ck.n,ck.rate_param,ck.c_alphas.clone());

	let witness_fri_proof = fri_commit(&mut setup, &witness_polynomial);

	//get query points of witness at same locations as was queried for the batch commitment so verifier
	//can compare them
	let x_args = lc[0].commitment().fri_proof.0.query_points[0].iter().map(|c| c.0).collect();
	let points = query_polynomial(&witness_polynomial,x_args,setup.log_domain);

	(FriProof(witness_fri_proof), points.0, points.1)
    }
    pub fn open(commitments:&BTreeMap<usize,Vec<LabeledCommitment<Commitment<F>>>>, poly:&Vec<LabeledPolynomial<F,DensePolynomial<F>>>,opening_challenge:F ,ck:&CommitterKey<F>)->Proof<F>{
	let mut proofs = Vec::new();
	for lp in poly{
	    let p = lp.polynomial();
    	    let eval = p.evaluate(&opening_challenge);

	    let comms = commitments.get(&lp.degree_bound().unwrap()).unwrap();
	    let (proof,points,paths) = Self::generate_proof(comms.to_vec(),p,opening_challenge,ck,&eval,lp.degree_bound().unwrap(),ck.rate_param);
	    //compare poly evals to addition of comms evals
	    let witness_proof = WitnessProof{
		degree_bound : lp.degree_bound().unwrap(),
		proof: proof,
		sim_query_points: points,
		sim_paths: paths,
		eval: eval,
		point:opening_challenge
	    };


	    proofs.push(witness_proof);
    
	//TODO : when using enforced degree bounds, instead of bucketing by exact degree, make sure that taking the degree of the linear combination still makes sense
	}
	Proof{proof: proofs}
    }


   pub fn bucket_commitment_by_degree(commitments:&Vec<LabeledCommitment<Commitment<F>>>) -> BTreeMap<usize,Vec<LabeledCommitment<Commitment<F>>>>{
	let mut degree_map = BTreeMap::new();
	for c in commitments{
	    degree_map.entry(c.commitment().degree_bound).and_modify(|vec:&mut Vec<LabeledCommitment<Commitment<F>>>| { vec.push(c.clone())}).or_insert(vec![c.clone()]);
	}
	degree_map
    }
    
    pub fn verify(commitments:&Vec<LabeledCommitment<Commitment<F>>>,proof:&Proof<F>,params:&VerifierKey<F>,point:F)->bool{
	//all commitments should be same degree and same round and proof should be proof of linear combination
//	TODO : add opening challenges - but for now assume we just add them up
        //verify FRI Proof associated with commitment
	let mut setup = set_fri_setup::<F>(params.log_domain_size,params.n,params.r,BTreeMap::new());
	let commitment_buckets = Vlpa19::bucket_commitment_by_degree(&commitments);
	let mut verify_commitment = true;
	if(commitment_buckets.len() == 0){
	    verify_commitment = false;
	}
	for (degree,bucket) in &commitment_buckets{
	    let log_domain = Vlpa19::<F>::get_min_log_domain(degree.clone(),setup.rate_param);
	    setup.log_domain = log_domain;
	    let root = bucket[0].commitment().lc_eval_root;
	    let proofs:Vec<NiroaProof<Round<F>>> = bucket.iter().map(|c| c.commitment().fri_proof.0.clone()).collect();
	    let verify = batch_verify(&mut setup, &NiroaBatchProof { individual_proofs : proofs , linear_combination_eval_root: root});
	    if(verify == false){
		verify_commitment = false;
	    }
	}
	//verify FRI Proof associated with proof of openings (verify commitment to witness polynomial)
	let mut setup2 = set_fri_setup(params.log_domain_size,params.n,params.r,BTreeMap::new());
	let mut verify_proof = true;
	if(proof.proof.len() == 0){
	    verify_proof = false;
	}
	for p in &proof.proof{
	    let verify = fri_verify(&mut setup2, &p.proof.clone().0);
	    if(verify == false){
		verify_proof = false;
	    }
	}

	let mut verify_w = true;
	if (proof.proof.len() == 0){
	    verify_w = false;
	}
	//there will be two proofs per degree bound, one for each query point
	for p in &proof.proof{
	    //asscoiate bucket with p
	    let bucket = commitment_buckets.get(&p.degree_bound).unwrap();
	    let verify = Self::verify_witness(p,bucket,&point);
	    if(verify == false){
		verify_w = false;
	    }
	}

	//TODO: verify paths of witness points verify against merkle root
	
	verify_commitment && verify_proof && verify_w
    }

fn add_two_points(point1 : &(F,F), point2: &(F,F)) -> (F,F){
    assert_eq!(point1.0 == point2.0,true);
    (point1.0.clone(), point1.1.clone() + point2.1.clone())
}    
fn add_multiple_set_of_points(points: Vec<Vec<(F, F)>>) -> Vec<(F, F)>{
    //each p is a vector of points
    //store sums in vector where sum i is the sum associated with x_i - where each summand is in the ith position of their points vector
    let length = points[0].len();
    let mut sums = Vec::new();
    //initiliaze sums
    let first_oracle = &points[0];
    for i in 0..length{
	//store ith x component - initialize y to 1
	sums.push((first_oracle[i].0.clone(), F::zero()));
    }
    //adding all ith components (adding ys keeping x the same)
    for p in points{
	for i in 0..length{
	    assert_eq!(sums[i].0 == p[i].0,true);
	    sums[i] = Self::add_two_points(&sums[i], &p[i]);
	}
    }
    sums
}
    fn verify_witness(witness: &WitnessProof<F>, commitments: &Vec<LabeledCommitment<Commitment<F>>>,point:&F) -> bool{
	let witness_degree = witness.degree_bound;
	let commitment_degree = commitments[0].commitment().degree_bound;
	assert_eq!(witness_degree,commitment_degree);
	//each commitment has a proof. Each proof has query_points. We want
	//the first element of query_points
	let mut first_round_queries:Vec<Vec<(F,F)>> = Vec::new();
	let mut result = true;
	for c in commitments{
	    first_round_queries.push(c.commitment().fri_proof.0.query_points[0].clone());
	}

	let sim_witness:Vec<(F,F)> = Self::add_multiple_set_of_points(first_round_queries);

	let witness_query_points = &witness.sim_query_points;
	for (i,(p1,p2)) in sim_witness.iter().enumerate(){
	    let is_consistent = simulate_opening_queries::<F>(&p2,&p1,&witness_query_points[i].1, point, &witness.eval);
	    if(is_consistent == false){
		result = false;
	    }
	}

	result
    }
	    
    
}


#[test]
fn random_inversion_tests() {
    assert!(Fr::zero().inverse().is_none());

    for _ in 0..5 {
        let mut a:Fr = verifier_challenge();
        let b = a.inverse().map(|b| {
            a *= &b;
            assert_eq!(a, Fr::one());
        });
    }
    let mut new_a = Fr::from(4u32);
    let new_b = new_a.inverse().unwrap();
    assert_eq!(Fr::from(4u32).inverse().unwrap() * Fr::from(4u32),Fr::one());
}
    #[test]
fn transform_points_interpolation(){
    let verifier_challenge1 = Fr::from(4u32).inverse().unwrap();

    let poly = DensePolynomial::from_coefficients_slice(&[Fr::from(2u32),Fr::from(2u32) * Fr::from(4u32),Fr::from(16u32)]);
    //these points interpolate to poly
    let manual_point_1 = (Fr::from(1u32),poly.evaluate(&Fr::from(1u32)));
    let manual_point_2 = (Fr::from(2u32),poly.evaluate(&Fr::from(2u32)));
    let manual_point_3 = (Fr::from(3u32), poly.evaluate(&Fr::from(3u32)));
    let manual_interpolate_evaluate = poly.evaluate(&verifier_challenge1);
     assert_eq!(Fr::from(4u32).inverse().unwrap() * Fr::from(4u32).inverse().unwrap(), Fr::from(16u32).inverse().unwrap());
    assert_eq!(manual_interpolate_evaluate,Fr::from(5u32));
    assert_eq!(manual_interpolate_evaluate * Fr::from(4u32),Fr::from(20u32));


    let points = vec![manual_point_1,manual_point_2,manual_point_3];
    let i = points.iter().cloned().unzip();
    let interp_eval = lagrange_interpolate_over_points(i.0,i.1,&verifier_challenge1);
    assert_eq!(manual_interpolate_evaluate,interp_eval);
    
    let x = DensePolynomial::from_coefficients_slice(&[Fr::from(0u32),Fr::from(1u32)]);
    let new_challenge = verifier_challenge();
    let eval_challenge = poly.evaluate(&new_challenge);
    let poly_q_r = get_prover_poly_from_point(&new_challenge,&poly).unwrap();
    assert_eq!((poly_q_r.0).evaluate(&manual_point_1.0), (manual_point_1.1 - eval_challenge) / (manual_point_1.0 - new_challenge));
    assert_eq!((poly_q_r.0).evaluate(&manual_point_2.0), (manual_point_2.1 - eval_challenge) / (manual_point_2.0 - new_challenge));
    assert_eq!((poly_q_r.0).evaluate(&manual_point_3.0), (manual_point_3.1 - eval_challenge) / (manual_point_3.0 - new_challenge));
    //now test with interpolation
    let man_eval = (manual_interpolate_evaluate - eval_challenge) / (verifier_challenge1 - new_challenge);
    let point1 = (Fr::from(1u32),(manual_point_1.1 - eval_challenge) / (Fr::from(1u32) - new_challenge));
    let point2 = (Fr::from(2u32),(manual_point_2.1 - eval_challenge) / ( Fr::from(2u32) - new_challenge ));
    assert_eq!((poly_q_r.0).evaluate(&point2.0),point2.1);
    let point3 = (manual_point_3.0, (manual_point_3.1 - eval_challenge) / (manual_point_3.0 - new_challenge));
    assert_eq!((poly_q_r.0).evaluate(&point3.0),point3.1);
    let points = vec![point1,point2,point3];
    let i = points.iter().cloned().unzip();
    let new_eval = lagrange_interpolate_over_points(i.0,i.1,&verifier_challenge1);

    assert_eq!(new_eval, man_eval);
}
