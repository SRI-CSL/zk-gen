use crate::vlpa19::{Vlpa19};
use crate::data_structures::{UniversalParams,CommitterKey,VerifierKey,PreparedVerifierKey,Commitment,Randomness,Proof,FriProof,CommitmentMulDegreeBounds,ProofLC,PreparedCommitment};
use std::time::{Duration, Instant};
use rand_core::RngCore;
use ark_std::{string::String,marker::PhantomData,io::{Read,Write},ops::{Mul,Sub,Div,Neg,SubAssign,Add,AddAssign},collections::{BTreeMap, BTreeSet}};
use ark_std::{convert::TryInto,iter::FromIterator};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use fri::fri::{data_structures::{RSCodeDomain,Round},fri_setup,query_codeword,fri_iop, get_coset_from_codeword,setup,prover,get_non_terminal_round,util::{rand_usize,sample_from_domain,verifier_challenge,rand_to_lower_bound}};
use ark_test_curves::bls12_381::{Fr, FrParameters};
use ark_ff::{PrimeField,Field};
use ark_poly::{domain::{EvaluationDomain,GeneralEvaluationDomain,Radix2EvaluationDomain},polynomial::{Polynomial,univariate::{DenseOrSparsePolynomial,DensePolynomial,SparsePolynomial}, UVPolynomial}};
use ark_poly_commit::{PolynomialCommitment,data_structures::*,error::Error,QuerySet,Evaluations,LinearCombination,evaluate_query_set};

pub struct Vlpa19_Marlin<F:PrimeField>{
    _f :PhantomData<F>
}
pub fn lc_query_set_to_poly_query_set<'a, F: Field, T: Clone + Ord>(
    linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
    query_set: &QuerySet<T>,
) -> QuerySet<T> {
    let mut poly_query_set = QuerySet::<T>::new();
    let lc_s = linear_combinations.into_iter().map(|lc| (lc.label(), lc));
    let linear_combinations = BTreeMap::from_iter(lc_s);
    for (lc_label, (point_label, point)) in query_set {
        if let Some(lc) = linear_combinations.get(lc_label) {
            for (_, poly_label) in lc.iter().filter(|(_, l)| !l.is_one()) {
                if let LCTerm::PolyLabel(l) = poly_label {
                    poly_query_set.insert((l.into(), (point_label.clone(), point.clone())));
                }
            }
        }
    }
    poly_query_set
}

fn get_shifted_poly<F:PrimeField>(max_degree_bound:usize,degree_bound:usize,poly:&DensePolynomial<F>)->DensePolynomial<F>{
    let exp = max_degree_bound - degree_bound;
    let shift:DensePolynomial<F> = SparsePolynomial::from_coefficients_vec([(exp,F::one())].to_vec()).into();
    &shift * poly
}
struct CommitmentError{
    msg: u32
}
#[test]
fn test_degreebounds(){
    let degree_poly_vec:Vec<Option<usize>> = vec![Some(3),Some(4),Some(5),None,Some(10)];
    let mut degree_bound:usize = degree_poly_vec.iter().map(|d| if(d.is_some()) {return d.unwrap()} else{return 0 }).max().unwrap();
    assert_eq!(degree_bound,10);
}

impl<F:PrimeField> PolynomialCommitment<F,DensePolynomial<F>> for Vlpa19_Marlin<F>
{		   
    type UniversalParams = UniversalParams<F>;
    type CommitterKey = CommitterKey<F>;
    type Commitment = Commitment<F>;
    type VerifierKey = VerifierKey<F>;
    type PreparedVerifierKey = PreparedVerifierKey<F>;
    type Error = Error;
    type Randomness = Randomness;
    type Proof = ProofLC<F>;
    type BatchProof = Vec<Self::Proof>;
    type PreparedCommitment = PreparedCommitment<F>;
    //max_degree determined by code in marlin
    fn setup<R:RngCore>(max_degree:usize,num_vars:Option<usize>,rng:&mut R) -> Result<Self::UniversalParams, Self::Error>{


	//find rate_param and log_domain_size based on system wide max degree
	/*
	let mut log_degree_plus1= (((max_degree) as f64).log2()).ceil() as u32;
	let log_domain_size = log_degree_plus1 + 1;
	let rate_param = log_domain_size - log_degree_plus1; // rate param is 1
	 */
	let mut log_degree= (((max_degree) as f64).log2()).ceil() as u32;
	let rate_param = 1;
	let log_domain_size = log_degree + rate_param;
	let n = 2; //log_domain_size / 2;
	Ok(Vlpa19::setup(n,log_domain_size,rate_param,max_degree))
    }

    fn trim(pp:&Self::UniversalParams, supported_degree:usize, supported_hiding_bound:usize, enforced_degree_bounds:Option<&[usize]>) -> Result<(Self::CommitterKey, Self::VerifierKey), Self::Error>{
	let enforced_degree_bounds = enforced_degree_bounds.map(|v| {
	    let mut v = v.to_vec();
	    v.sort();
	    v.dedup();
	    v
	});
	let now = Instant::now();
	let frisetup = fri_setup(pp.log_domain_size,pp.n,pp.rate_param); //one time computation of c_alpha

	let new_map = frisetup.c_alphas.clone();
	Ok((CommitterKey{setup:frisetup,log_domain_size:pp.log_domain_size,initial_domain:pp.initial_domain,n:pp.n,max_degree:pp.max_degree,rate_param:pp.rate_param,enforced_degree_bounds:enforced_degree_bounds,c_alphas:new_map},VerifierKey{initial_domain:pp.initial_domain,n:pp.n,r:pp.rate_param,log_domain_size:pp.log_domain_size}))
    }

    fn commit<'a>(ck: &Self::CommitterKey,
		  polynomials: impl IntoIterator<Item=&'a LabeledPolynomial<F,DensePolynomial<F>>>,
		  rng:Option<&mut dyn RngCore>
    ) -> Result<(Vec<LabeledCommitment<Self::Commitment>>,Vec<Self::Randomness>),Self::Error>{
	//for each polynomial in polynomials, commit to polynomial
	//Find the maximum degree bound over set of polynomials and use that to compute rate param (degree bounds should all be the same)
	let mut randomness = Vec::new();


	let poly_vec:Vec<&LabeledPolynomial<F,DensePolynomial<F>>> = polynomials.into_iter().collect();
	let mut polynomials = Vec::new();
	//commit to each polynomial
	for p in &poly_vec{
	    let polynomial: &DensePolynomial<F> = (p.polynomial());
	    polynomials.push(polynomial.clone());
	    randomness.push(Randomness::default());
	}

	//test commitments against polynomials
	
	let new_map = ck.c_alphas.clone();
	let degrees:Vec<usize> = polynomials.iter().map(|p| p.degree()).collect();
	let polys = poly_vec.iter().by_ref().map(|p| p.clone().clone()).collect();
	let commitments = Vlpa19::batch_commit(ck,new_map,&polys);
	Ok((commitments,randomness))		
    }

    //opening challenges refers to randomness send by verifier that prover uses to build a linear combination of labeled_polynomials
    //point is the point at which the polynomial is evaluated, for which we output a proof
    fn open_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        labeled_polynomials: impl IntoIterator<Item = &'a LabeledPolynomial<F, DensePolynomial<F>>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        point: &'a <ark_poly::univariate::DensePolynomial<F> as Polynomial<F>>::Point,
        opening_challenges: &dyn Fn(u64) -> F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<Self::Proof, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a{
	//everthing is round specific here! So I think we are free to just group by degree

	let mut eval_sum = F::zero();

	let mut lc_commitment_ = Vec::new();
	for c in commitments.into_iter(){
	    lc_commitment_.push(c.clone());
	}


	let lp:Vec<LabeledPolynomial<F,DensePolynomial<F>>> = labeled_polynomials.into_iter().by_ref().map(|p| p.clone()).collect();

	let mut poly_map = BTreeMap::new();
	for l in lp.iter(){
	    poly_map.entry(l.label().to_string()).or_insert(l.polynomial());
	}

	let commitment_buckets = Vlpa19::bucket_commitment_by_degree(&lc_commitment_);


	let mut lc_polys = Vec::new();
	let mut challenge_counter = 0;
	
	for (degree,batch) in &commitment_buckets{
    	    let mut poly_sum = DensePolynomial::from_coefficients_slice(&[F::zero()]);
	    for b in batch{
		let challenge = 1u32; //opening_challenges((challenge_counter) as u64);
		//this is the linear combination with coefficient

		let poly = &poly_map.get(&b.commitment().label.to_string()).unwrap().clone();
		//poly degree associated with label 30 has degree 31
		//poly associated with a_row has degree 31
		//degree associated with commitment of a_row is 30 instead of 31
		//degree associated with commitment of b_row is 31 instead of 30
		//a_row and b_row somehow got switched in commitment map

		poly_sum +=  &(&DensePolynomial::from_coefficients_slice(&[F::from(challenge)]) * poly);
		challenge_counter = challenge_counter + 1;
	    }
	    let lc_poly = LabeledPolynomial::new(degree.to_string(),poly_sum, Some(degree.clone()), Some(degree.clone()));
	    assert_eq!(&lc_poly.degree_bound().unwrap(),degree);
	    lc_polys.push(lc_poly);
	}
	let proof = Vlpa19::open(&commitment_buckets,&lc_polys,*point, &ck);

        Ok(ProofLC{
	    proof: proof,
	    lc_label: String::new()
	})	    	    
    }

  fn check_individual_opening_challenges<'a>(
     vk:&Self::VerifierKey,
     commitments: impl IntoIterator<Item=&'a LabeledCommitment<Self::Commitment>>,
     point: &'a <ark_poly::univariate::DensePolynomial<F> as Polynomial<F>>::Point,
     values: impl IntoIterator<Item=F>,
     proof: &Self::Proof,
     opening_challenges: &dyn Fn(u64) -> F,
     rng: Option<&mut dyn RngCore>
 )->Result<bool,Self::Error>
    where
	Self::Commitment: 'a{

      let commitments:Vec<LabeledCommitment<Commitment<F>>> = commitments.into_iter().cloned().collect();
      let mut test_commitments:Vec<Commitment<F>> = Vec::new();
      for c in &commitments{
	    test_commitments.push(c.commitment().clone());
      }
      let commitment_buckets = Vlpa19::bucket_commitment_by_degree(&commitments);
      let proof_degrees:Vec<usize> = proof.proof.proof.iter().map(|proof| proof.degree_bound).collect();
        return Ok(Vlpa19::verify(&commitments,&proof.proof,vk,point.clone()));
  }
   fn open_combinations_individual_opening_challenges<'a>(
        ck: &Self::CommitterKey,
        linear_combinations: impl IntoIterator<Item = &'a LinearCombination<F>>,
        polynomials: impl IntoIterator<Item=&'a LabeledPolynomial<F,DensePolynomial<F>>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<<ark_poly::univariate::DensePolynomial<F> as Polynomial<F>>::Point>,
        opening_challenges: &dyn Fn(u64) -> F,
        rands: impl IntoIterator<Item = &'a Self::Randomness>,
        rng: Option<&mut dyn RngCore>,
    ) -> Result<BatchLCProof<F, DensePolynomial<F>, Self>, Self::Error>
    where
        Self::Randomness: 'a,
        Self::Commitment: 'a,
        DensePolynomial<F> : 'a,
    {

	let mut rands = Vec::new();
        let linear_combinations: Vec<_> = linear_combinations.into_iter().collect();
        let polynomials: Vec<_> = polynomials.into_iter().collect();
        let poly_query_set =
		lc_query_set_to_poly_query_set(linear_combinations.iter().copied(), query_set);
        let poly_evals = evaluate_query_set(polynomials.iter().copied(), &poly_query_set); //evaluates each polynomial individually on relevent points
        let mut pquery_to_labels_map = BTreeMap::new();
	    //maps label of polynomials to points
        for (label, (point_label, point)) in poly_query_set.iter() {
            let labels = pquery_to_labels_map
                .entry(label)
                .or_insert((point_label, point));
        }

	    //maps linear combination label to point
	let mut lquery_to_labels_map = BTreeMap::new();
        for (lc_label, (point_label, point)) in query_set.iter() {
            let labels = lquery_to_labels_map
                .entry(lc_label)
                .or_insert((point_label, point));
        }

	
       let poly_label_map: BTreeMap<String,&LabeledPolynomial<F,DensePolynomial<F>>> = polynomials.into_iter().map(|p| (p.label().to_string(),p)).collect();

       let commitment_label_map:BTreeMap<_,_> = commitments.into_iter().map(|c| (c.commitment().label.to_string(),c)).collect();

	let mut proofs = Vec::new();
	let mut evals = Vec::new();
	    let mut query_points_map = BTreeMap::new();
	    //for each linear combination
	    //prover evaluates linear combinations
	for (lc) in linear_combinations {
	    let q = lquery_to_labels_map.get(lc.label()).unwrap(); //get point to evaluate lc at
	    
	    query_points_map.insert(q,true);
	}
	    let query_points:Vec<(String,F)> = query_points_map.keys().cloned().map(|(a,b)| (*a,*b)).map(|(a,b)| (a.clone(), b.clone())).collect();
	    let mut round_map = BTreeMap::new();
	    round_map.entry(0usize).or_insert(vec!["a_row","a_col","a_val","a_row_col","b_row","b_col","b_val","b_row_col","c_row","c_col","c_row_col"]);
	    round_map.entry(1usize).or_insert(vec!["w","z_a","z_b","mask_poly"]);
	    round_map.entry(2usize).or_insert(vec!["t","g_1","h_1"]);
	    round_map.entry(3usize).or_insert(vec!["g_2","h_2"]);
	    for (key,value) in round_map{
		let mut polynomials: Vec<&'a LabeledPolynomial<_,_>>  = Vec::new();
		let mut commitments: Vec<&'a LabeledCommitment<Self::Commitment>> = Vec::new();
		//gather polynomials and commitments for round associated with key
		for label in &value{
		    let poly = &poly_label_map.get(&label.to_string()).unwrap().clone();
    		    polynomials.push(poly);
		    let commitment = &commitment_label_map.get(&label.to_string()).unwrap().clone();
		    commitments.push(commitment);
		}

		for qp in &query_points{
    		    let lc_poly = polynomials.iter().map(|p| *p);
		    let lc_comm = commitments.iter().map(|c| *c);
		    //this returns a ProofLC which has a vector of Proofs
		    //associated with one round and one query points
		    //each proof -> (round,query_point)
		    let mut proof = Self::open_individual_opening_challenges(
		    ck,
		    lc_poly,
		    lc_comm,
		    &qp.1,
		    opening_challenges,
		    &rands,
		    None
		    )?;
		
		proof.set_lc_label(key.to_string().clone() + &qp.0.to_string());
		proofs.push(proof);
		}
	    }
	    //proofs is a vector of ProofLCs . Each ProofLC has a label associated with the round and then ONE PROOF which has a vector of WitnessProofs
        Ok(BatchLCProof {
            proof: proofs,
            evals: Some(evals)
        })
    }



   fn check_combinations_individual_opening_challenges<'a, R: RngCore>(
        vk: &VerifierKey<F>,
        lc_s: impl IntoIterator<Item = &'a LinearCombination<F>>,
        commitments: impl IntoIterator<Item = &'a LabeledCommitment<Self::Commitment>>,
        query_set: &QuerySet<<ark_poly::univariate::DensePolynomial<F> as Polynomial<F>>::Point>,
        evaluations: &Evaluations<F,<ark_poly::univariate::DensePolynomial<F> as Polynomial<F>>::Point>,
        proof: &BatchLCProof<F, DensePolynomial<F> , Self>,
        opening_challenges: &dyn Fn(u64) -> F,
        rng: &mut R,
    ) -> Result<bool, Error>
    where
        Commitment<F>: 'a,
    {

       //BatchLC has an evals field - so what is the extra evaluations argument that is input to this function?
        let label_comm_map = commitments
            .into_iter()
            .map(|c| (c.label(), c))
           .collect::<BTreeMap<_, _>>();
       let mut result = true;
       let mut proofi = proof.proof.iter(); //iterating through ProofLC - each associated with a Proof - in turn associated with vector of WitnessProofs
       let mut query_to_labels_map = BTreeMap::new();
       for (label, (point_label, point)) in query_set.iter() {
            let labels = query_to_labels_map
                .entry(label)
                .or_insert((point_label, point));
        }
       let mut evaluations = evaluations.clone();
       //verify each linear combination and each query point - but the linear combinations defined by round and degree
       //so similar to open - you need to get - traverse through rounds, and then gt degree
       for lc in lc_s {
	   let lc_label = lc.label().clone();
	   let num_polys = lc.len();
	   let mut degree_bound = None;
	   let mut evals:Vec<F> = Vec::new();
	   let mut labeled_comms = Vec::new();
	   let mut coeffs_and_comms = Vec::new();
	   let query_point = query_to_labels_map.get(&lc_label.to_string()).as_ref().unwrap().1;
	   for (coeff,label) in lc.iter(){
              if label.is_one() {
                for (&(ref label, _), ref mut eval) in evaluations.iter_mut() {
                     if label == &lc_label {               
                      }
                }
              } else {
		  let label:&String = label.try_into().unwrap();
		  let &cur_comm = label_comm_map.get(label).ok_or(Error::MissingPolynomial {
		  label: label.to_string(),
	       })?;
	       if num_polys == 1 && cur_comm.degree_bound().is_some(){
		   assert!(coeff.is_one(), "Coefficients must be one for degree bounded equations");
		   degree_bound = cur_comm.degree_bound();
	       }else if cur_comm.degree_bound().is_some(){
		   return Err(Error::EquationHasDegreeBounds(lc_label));
	       }
	       coeffs_and_comms.push((coeff.clone(),cur_comm));
	       labeled_comms.push(cur_comm);
	      }

	   }

       }


       let label_proof_map = proof.proof.iter().map(|p| (p.label(), p)).collect::<BTreeMap<_,_>>();
       let mut round_map = BTreeMap::new();
       round_map.entry(0usize).or_insert(vec!["a_row","a_col","a_val","a_row_col","b_row","b_col","b_val","b_row_col","c_row","c_col","c_row_col"]);
       round_map.entry(1usize).or_insert(vec!["w","z_a","z_b","mask_poly"]);
       round_map.entry(2usize).or_insert(vec!["t","g_1","h_1"]);
       round_map.entry(3usize).or_insert(vec!["g_2","h_2"]);
       for (key,value) in round_map{
	   let mut commitments: Vec<&'a LabeledCommitment<Self::Commitment>> = Vec::new();
	   let mut proofs: Vec::<&'a ProofLC<F>> = Vec::new();
	   for label in &value{
	       //proofs and commitments associated with this round
	       //for each round, you have WitnessProofs for each degree and each query point
	       //each ProofLC has one label and it is labeled by round - but then it has them for each degree and query point - you will isolate query point later
	       commitments.push(label_comm_map.get(&label.to_string()).unwrap().clone());
	   }
	   for (label,qp) in query_set{
	       let lc_commitments = commitments.iter().map(|c| *c);
   	       let proof = label_proof_map.get(&(key.to_string().clone() + &qp.0.to_string())).unwrap().clone();
	       let point:F = qp.1;
	       let eval = Vec::new();
		   result &= Self::check_individual_opening_challenges(
                       vk,
		       lc_commitments,
                       &point,
	               eval,
                       proof,
                       opening_challenges,
                       Some(rng),
		   )?;	     
	       }
       }
   
       Ok(result)       
   }
}

	  



