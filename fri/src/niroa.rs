use ark_std::{fmt::Debug,string::String,marker::PhantomData,io::{Read,Write}};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use std::time::{Duration, Instant};
pub use super::{iop::{Oracle, Setup, Iop, Prover, Verifier,Witness},parallelize::parallel_function};
use ark_ff::{PrimeField,ToBytes,One,FromBytes,Zero};
use ark_crypto_primitives::{merkle_tree::{MerkleTree,Path,Config,Digest},
			    crh::pedersen,FixedLengthCRH};
use blake2::Blake2s;
use ark_std::fmt;
use rand_xorshift::XorShiftRng;
use rand::SeedableRng;
use ark_ed_on_bls12_381::EdwardsProjective as JubJub;
#[derive(Clone)]
pub struct Window4x256;
impl pedersen::Window for Window4x256 {
    const WINDOW_SIZE: usize = 4;
    const NUM_WINDOWS: usize = 256;
}
/*
fn from_bytesh<B:FromBytes,R:Read>(r: &mut R) -> B{
    B::read(&mut r).ok().unwrap()
}
 */
fn unflatten<F:Clone>(to_unflatten:Vec<F>,interval:usize) -> Vec<Vec<F>>{
    assert_eq!(to_unflatten.len() % interval, 0);
    let mut input_index = 0;
    let mut results = Vec::new();
    loop{
	if input_index  >= to_unflatten.len(){
	    break;
	}
	let mut temp = Vec::new();
	for i in 0..interval{
	    temp.push(to_unflatten[input_index + i].clone());
	}
	input_index = input_index + interval;
	results.push(temp);
    }
    results	
}
fn serialize_bytes_to_vec<O:Oracle>(r:Vec<u8>,veclength:usize, num_paths: Vec<usize>, path_lengths: Vec<usize>) -> (Vec<Digest<<O as Oracle>::C>>,Vec<Vec<Path<<O as Oracle>::C>>>){
    //for first type, do a for loop until 1 nd count indicse.
    //for second loop, flush out the correct amount of indices and then start adding to vector
    let mut val1:&[u8] = &r[..];
    let mut f_vec = Vec::new();
    let mut f_counter = 0;
    for i in 0..veclength{
	let mut output = Digest::<<O as Oracle>::C>::read(&mut val1).ok();
	f_vec.push(output.unwrap());
    }
    //continue with Ts
    let mut t_vec = Vec::new();
    let mut start = 0;
    for top_level_it in 0..veclength{
	let num_paths = num_paths[top_level_it];
	let ind_path_lengths = &path_lengths[start..(start + num_paths)];
	start = start + num_paths;
	let mut counter = 0;
	let mut round_paths = Vec::new();
	//for each path in Vec<Path>
	for it in 0..num_paths{
	    let mut path_vec = Vec::new();
	    let path_length = ind_path_lengths[it];
	    //for each pair in Path
	    let mut pit = 0;
	    while pit < 2 * path_length{
		let mut pair0 = Digest::<<O as Oracle>::C>::read(&mut val1).ok();
		let mut pair1 = Digest::<<O as Oracle>::C>::read(&mut val1).ok();
		if let (Some(a),Some(b)) = (pair0,pair1){
		    path_vec.push((a,b));
		}
		else{
		    panic!("path was serialized incorrectly");
		}
		pit = pit + 2;
	    }
	    let path = Path::<<O as Oracle>::C>::set_path(path_vec);
	    round_paths.push(path);
	    //create a path from vec of pairs of digests
	    //add this path to round_paths
	}
	t_vec.push(round_paths);
	//now add Vec<Path> to t_vec
    }
	
    (f_vec,t_vec)

}
fn hash(input:&Vec<u8>,size:usize) -> Vec<u8>{
    const outsize:usize = 32;
    let mut hash = Blake2s::new(outsize);
    let mut out = [0u8;outsize];
    hash.update(&input[..]);
    hash.finalize(&mut out[..outsize]);
    let mut out_vec = Vec::new();
    for i in 0..size{
	out_vec.push(out[i]);
    }
    out_vec
}
fn hash_concatenation(i1: &Vec<u8>,i2:&Vec<u8>) -> Vec<u8>{
    let mut vec1 = Vec::new();
    for i in 0..i1.len(){
	vec1.push(i1[i]);
    }
    let mut vec2 = Vec::new();
    for i in 0..i2.len(){
	vec2.push(i2[i]);
    }
    vec1.append(&mut vec2);
    hash(&vec1,32)
}
#[derive(Clone)]
pub struct NiroaProof<O:Oracle>{
    pub roots: Vec<Digest<<O as Oracle>::C>>,
    pub paths: Vec<Vec<Path<<O as Oracle>::C>>>,
    pub query_points: Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,
    pub sigma : Vec<u8>,
    pub challenges: Vec<<O as Oracle>::X>
}
impl<O:Oracle> PartialEq for NiroaProof<O> {
    fn eq(&self, other: &Self) -> bool {
	self.roots == other.roots && self.paths == other.paths && self.query_points == other.query_points && self.sigma == other.sigma && self.challenges == other.challenges
	    
    }
}

impl<O:Oracle> Eq for NiroaProof<O>{

}
pub type MerkleRoot<O:Oracle> = Digest<<O as Oracle>::C>;
//for purposes of VLPA19s use of FRI - we only need
//the root of the evaluation of the linear combination
//for other things - does it make sense to also create a proof of the linear combination?
pub struct NiroaBatchProof<O:Oracle>{
    pub individual_proofs: Vec<NiroaProof<O>>,
    pub linear_combination_eval_root : MerkleRoot<O>
}

pub struct Niroa<'a,O:Oracle,S:Setup,W:Witness>{
    pub setup_params : &'a S,
    pub prover : NiroaProver<O,S,W>,
    pub verifier: NiroaVerifier<S,O>
}

impl<'a,O:'static + Oracle,S:'static + Setup + Sync + Send + Clone,W:'static + Witness + Sync + Send + Clone> Niroa<'a,O,S,W>{
    pub fn commit_phase(&mut self,wit: &W) -> NiroaProof<O> {
	let mut oracles = Vec::new();
	let mut roots = Vec::new();
	let mut hash_acc = hash(&vec![10u8],32);
	let mut trees = Vec::new();
	let mut fns = self.verifier.verifier_challenges.iter().zip(self.prover.prover_functions.iter());
	let mut challenges = Vec::new();
	let mut challenge = <O as Oracle>::hash_to_x(&hash_acc);
	for (v,p) in fns{
	    let oracle = p((challenge.clone(),oracles.clone(), self.setup_params.clone(), &wit.clone()));
	    let (root,tree) = (self.prover.oracle_hash)(&oracle);
    	    challenges.push(challenge.clone());
	    oracles.push(oracle);
	    trees.push(tree);
	    let c_a  = v(self.setup_params, &root, &hash_acc);
	    challenge = c_a.0;
	    hash_acc = c_a.1;
    	    roots.push(root);
	}
	//stub - in future will pass seed
	let (query_points,paths) = (self.verifier.get_query_points)(&oracles,&trees);
	NiroaProof{
	    roots,
	    paths,
	    query_points,
	    sigma: hash_acc,
	    challenges
	}
	    
    }    
    pub fn query_phase(&mut self, p: &NiroaProof<O>) -> bool{
	(self.verifier.verifier_query)(&p.query_points,self.setup_params, &p.challenges, &p.roots, &p.paths)
    }

    pub fn batch_commit(&mut self, witnesses: &Vec<W>) -> NiroaBatchProof<O>{
	// element i, j is ith round, jth polynomial for the
	//following vectors
	//each element is first round oracles for all polynomials
	let mut oracles = Vec::new();
	let mut roots = Vec::new();
	let mut trees = Vec::new();
	let mut hash_acc = hash(&vec![10u8],32);
	let mut challenges = Vec::new();
	let mut challenge = <O as Oracle>::hash_to_x(&hash_acc);
	let mut fns = self.verifier.verifier_challenges.iter().zip(self.prover.prover_functions.iter());
	let mut wits = Vec::new();
	for (i,w) in witnesses.iter().enumerate(){
	    oracles.push(Vec::new());
	    roots.push(Vec::new());
	    trees.push(Vec::new());
	    wits.push(w);
	}
	//for each round
	for (round_index,(v,p)) in fns.enumerate(){
	    //parallelize evaluation, setting the first elemen of oracles, trees, and roots
	   
	    if round_index == 0{
		//call parallel_function where In: is (F,Vec<Oracle<F>>, Setup, DensePolynomial) and Out is (Oracle<F>,Digest<>, MerkleTree)
		//next, create a vector of such tuples by by iterating over witnesses and collecting
		//then call prallel_function
		//input is (<O as Oracle>::X, Vec<O>, S, W)
		//output is (O,Digest<<O as Oracle>::C>, MerkleTree<<O as Oracle>::C>)
		let mut inputs = Vec::new();
		let setup_params = self.setup_params.clone();
		for (witness_index,wit) in wits.iter().enumerate(){
		    inputs.push((challenge.clone(), oracles[witness_index].clone(), setup_params.clone(),wit.clone()));
		}
		
		let now  = Instant::now();
		let results = parallel_function::<(<O as Oracle>::X, Vec<O>,S,&W),O>(&inputs,*p);

		//one oracle for each polynomial for round 0
		//index polynomials
		for (index,oracle) in results {
			oracles[index].push(oracle.clone());
			let (root,tree) = (self.prover.oracle_hash)(&oracle.clone());
			trees[index].push(tree);
			roots[index].push(root);

		}
		challenges.push(challenge);
		let root_accum = &roots[0][round_index];
		let c_a = v(self.setup_params,root_accum,&hash_acc);
		challenge = c_a.0;
		hash_acc = c_a.1;

	    }
	    else{


		let nowl = Instant::now();
	    //for each polynomial : 
		for (witness_index,wit) in wits.iter().enumerate(){
		    let oracle = p((challenge.clone(),oracles[witness_index].clone(), self.setup_params.clone(), &wit.clone()));
		    let (root,tree) = (self.prover.oracle_hash)(&oracle);
		    oracles[witness_index].push(oracle);
		    trees[witness_index].push(tree);
		    //instead of root, you want to pass in roots for all polynomials
    		    roots[witness_index].push(root);
		}
		//now we accumulate roots and pass to v
		//this is a stub - we will do a real root accumulator
		challenges.push(challenge);
		let root_accum = &roots[0][round_index];
		let c_a = v(self.setup_params,root_accum,&hash_acc);
		challenge = c_a.0;
		hash_acc = c_a.1;
	    }
    
    }
	let mut proofs = Vec::new();
	for (i,oracles_per_wit) in oracles.iter().enumerate(){
	    //stub -in future will pass in seed as argument - but right now seed is set within function so its deterministic
	    let nowq = Instant::now();
	    let qp = (self.verifier.get_query_points)(&oracles_per_wit,&trees[i]);
	    proofs.push(NiroaProof{
		roots:roots[i].to_vec(),
		paths:qp.1,
		query_points: qp.0,
		sigma: hash_acc.clone(),
		challenges: challenges.clone()
	    });
	}
	//add all first oracles and get root
	let mut first_oracles = Vec::new();
	for oracles_vec in oracles{
	    first_oracles.push(oracles_vec[0].clone());
	}
	let new_oracle = add_oracles(first_oracles);
	let new_oracle_root = new_oracle.to_tree().root();
	NiroaBatchProof {
	    individual_proofs: proofs,
	    linear_combination_eval_root: new_oracle_root
	}
	}
    }

    //TODO : should this function somehow be in Oracle trait??
    //TODO : this function needs to return an oracle
fn add_oracles<O:Oracle>(oracles: Vec<O>) -> O {
    let mut new_oracles: Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>> = Vec::new();
    for o in oracles{
	let new_vec = o.to_vec();
	new_oracles.push(new_vec);
    }
    let points = add_multiple_set_of_points::<O>(new_oracles);
    O::from_vec(&points)
}
fn add_multiple_set_of_points<O:Oracle>(points: Vec<Vec<(<O as Oracle>::X, <O as Oracle>::Y)>>) -> Vec<(<O as Oracle>::X, <O as Oracle>::Y)>{
    //each p is a vector of points
    //store sums in vector where sum i is the sum associated with x_i - where each summand is in the ith position of their points vector
    let length = points[0].len();
    let mut sums = Vec::new();
    //initiliaze sums
    let first_oracle = &points[0];
    for i in 0..length{
	//store ith x component - initialize y to 1
	sums.push((first_oracle[i].0.clone(), <O as Oracle>::Y::zero()));
    }
    //adding all ith components (adding ys keeping x the same)
    for p in points{
	for i in 0..length{
	    assert_eq!(sums[i].0 == p[i].0,true);
	    sums[i] = add_two_points::<O>(&sums[i], &p[i]);
	}
    }
    sums
    
}

fn add_two_points<O: Oracle>(point1 : &(<O as Oracle>::X, <O as Oracle>::Y), point2: &(<O as Oracle>::X, <O as Oracle>::Y)) -> (<O as Oracle>::X, <O as Oracle>::Y){
    assert_eq!(point1.0 == point2.0,true);
    (point1.0.clone(), point1.1.clone() + point2.1.clone())
}
pub struct NiroaProver<O:Oracle,S:Setup,W:Witness>{
    pub prover_functions:/* Vec<Box<dyn Fn*/ Vec<fn((<O as Oracle>::X,Vec<O>,S,&W)) -> O>, //>>,
    pub oracle_hash : Box<dyn Fn(&O) -> (Digest<<O as Oracle>::C>,MerkleTree<<O as Oracle>::C>)>
}

pub struct NiroaVerifier<S:Setup,O:Oracle>{
    //STUB - pass in challenges as temporary measure
    pub verifier_challenges : Vec<Box<dyn Fn(&S, &Digest<<O as Oracle>::C>,&Vec<u8>) -> (<O as Oracle>::X,Vec<u8>)>>,
    pub get_query_points: Box<dyn Fn(&Vec<O>,&Vec<MerkleTree<<O as Oracle>::C>>) -> (Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>, Vec<Vec<Path<<O as Oracle>::C>>>)>, 
    pub verifier_query: Box<dyn Fn(&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,&S, &Vec<<O as Oracle>::X>,&Vec<Digest<<O as Oracle>::C>>,&Vec<Vec<Path<<O as Oracle>::C>>>) -> bool>//consider just passing in Proof here 
			      

}

pub struct VerifierFunction<O:Oracle,S:Setup>{
    pub function : fn(&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,&S, &Vec<<O as Oracle>::X>) -> bool,
    dummy_data: (Vec<<O as Oracle>::C>,Vec<O>,Vec<S>)
}
impl<O:'static + Oracle, S:'static + Setup> Clone for VerifierFunction<O,S>{
    fn clone(&self) -> Self {
	Self{
	    function: self.function,
	    dummy_data: (Vec::new(),Vec::new(),Vec::new())
	}
    }
}
impl<O:'static + Oracle,S:'static + Setup> Debug for VerifierFunction<O,S>{
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.dummy_data.1.fmt(f)
	}
}
impl<O:'static + Oracle,S:'static + Setup> CanonicalSerialize for VerifierFunction<O,S>{
        fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	Ok(())
    }
    fn serialized_size(&self) -> usize{
	0
    }
}
impl<O:'static + Oracle,S:'static + Setup> CanonicalDeserialize for VerifierFunction<O,S>{
    fn deserialize<R:Read>(mut reader:R)->Result<Self,SerializationError>{
	Ok(VerifierFunction{
	    function:verifier_query_stub::<O,S>,
	   dummy_data:(Vec::new(),Vec::new(),Vec::new())
	})
    }
}


impl<O:'static + Oracle> Debug for NiroaProof<O>{
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            self.sigma.fmt(f)
	}
}

impl<O:'static + Oracle> CanonicalDeserialize for NiroaProof<O>{
    fn deserialize<R:Read>(mut reader:R)->Result<Self,SerializationError>{
	//deserialize to bytes for roots and paths
	let vec_length = usize::deserialize(&mut reader).ok().unwrap();
	//deserialize vector of lengths
	let num_paths = Vec::<usize>::deserialize(&mut reader).ok().unwrap();
	let path_lengths = Vec::<usize>::deserialize(&mut reader).ok().unwrap();
	let roots_and_paths:Vec<u8> = Vec::<u8>::deserialize(&mut reader).ok().unwrap();
	
	type F<O:Oracle> = Digest<<O as Oracle>::C>; 

	let (roots,paths) = serialize_bytes_to_vec::<O>(roots_and_paths,vec_length,num_paths,path_lengths);
	type Points<O:Oracle> = Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>;
	let query_points = Points::<O>::deserialize(&mut reader).ok().unwrap();
	let sigma = Vec::<u8>::deserialize(&mut reader).ok().unwrap();
	let challenges = Vec::<<O as Oracle>::X>::deserialize(&mut reader).ok().unwrap();
	Ok(NiroaProof{
	    roots,
	    paths,
	    query_points,
	    sigma,
	    challenges
	})

    }
}
impl<O:'static + Oracle> CanonicalSerialize for NiroaProof<O>{
        fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	    //first convert roots and paths to ToByt
	    let mut bytes_writer = Vec::new();
	    self.roots.len().serialize(&mut writer);
	    self.roots.write(&mut bytes_writer);

	    //create a vector of lengths, describing how many paths are in each vector
	    let mut num_paths = Vec::new();
	    let mut path_lengths = Vec::new();
	    for p in &self.paths{
		num_paths.push(p.len());
		for path in p{
		    path_lengths.push(path.get_length());
		}
	    }
	    
	    num_paths.serialize(&mut writer);
	    path_lengths.serialize(&mut writer);
	    //flatten self.paths before writing it
	    //flatten it all the way down till it is only a vector of (Digest,Digest)
	    for p in &self.paths{
		for i in p{
		    for digest_pair in i.get_path(){
			digest_pair.0.write(&mut bytes_writer);
			digest_pair.1.write(&mut bytes_writer);
		    }
		}
	    }



	    //now serialize bytes
	    bytes_writer.serialize(&mut writer);
	    self.query_points.serialize(&mut writer);
	    self.sigma.serialize(&mut writer);
	    self.challenges.serialize(&mut writer);
	    Ok(())
     }
    fn serialized_size(&self) -> usize{
	0usize
    }
}
impl<O:'static + Oracle> ToBytes for NiroaProof<O>{
    fn write<W:Write>(&self,mut writer:W) -> ark_std::io::Result<()>{
	for p in &self.query_points{
	    for q in p{
		q.0.write(&mut writer);
		q.1.write(&mut writer);
	    }
	}
	Ok(())

    }
}

impl<O:'static + Oracle> Default for NiroaProof<O>{
    fn default() -> Self{
	prover_init::<O>()
    }
}


fn verifier_query_stub<O:Oracle,S:Setup>(a:&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,b:&S, c:&Vec<<O as Oracle>::X>) -> bool{
    true
}

pub fn prover_init<O:'static + Oracle>()->NiroaProof<O>{
    NiroaProof{
	roots:Vec::new(),
	paths:Vec::new(),
	query_points: Vec::new(),
	sigma: Vec::new(),
	challenges: Vec::new(),
    }
}



pub fn iop_prover_to_niroa_prover<O:'static + Oracle,S:'static + Setup,W:'static + Witness>(iop_prover: Box<dyn Fn(&<O as Oracle>::X,&Vec<O>,&S,&W) -> O>) -> Box<dyn Fn(&<O as Oracle>::X,&Vec<O>,&S,&W) -> (O,Digest<<O as Oracle>::C>,MerkleTree<<O as Oracle>::C>)> {
    let new_func = move |challenge: &<O as Oracle>::X, oracles: &Vec<O>, setup: &S,witness: &W| -> (O, Digest<<O as Oracle>::C>,MerkleTree<<O as Oracle>::C>) {
	let oracle = iop_prover(challenge,oracles,setup,witness);
	let tree = oracle.to_tree();
	let root = tree.root();
	(oracle,root,tree)
    };
    Box::new(new_func)
}
fn p_to_pp_helper<O: Oracle, S:Setup, W:Witness>(prover: fn(&<O as Oracle>::X,&Vec<O>,&S,&W) -> O, all_args: ( (&<O as Oracle>::X,  &Vec<O>,  &S, &W))) -> O{
    	let challenge = all_args.0;
	let oracles = all_args.1;
	let setup = all_args.2;
	let witness = all_args.3;
	let oracle = prover(challenge,oracles,setup,witness);
	let tree = oracle.to_tree();
	let root = tree.root();
	oracle
}
/*
pub fn prover_to_parallelizable_prover<O:'static + Oracle,S:'static + Setup,W:'static + Witness>(prover: fn(&<O as Oracle>::X,&Vec<O>,&S,&W) -> O) -> fn((&<O as Oracle>::X,&Vec<O>,&S,&W)) -> O{
    fn new_func<O:Oracle, S:Setup, W:Witness>(args : (&<O as Oracle>::X,&Vec<O>,&S,&W)) -> O
    {
    	let challenge = all_args.0;
	let oracles = all_args.1;
	let setup = all_args.2;
	let witness = all_args.3;
	let oracle = prover(challenge,oracles,setup,witness);
	let tree = oracle.to_tree();
	let root = tree.root();
	oracle
    }
    new_func

}*/
pub fn iop_challenges_to_niroa_challenges<O:'static + Oracle,S:'static + Setup>() -> Box<dyn Fn(&S,&Digest<<O as Oracle>::C>,&Vec<u8>) -> (<O as Oracle>::X,Vec<u8>)>{
    let new_func = move |setup:&S,root:&Digest<<O as Oracle>::C>,hash_acc:&Vec<u8>| -> (<O as Oracle>::X,Vec<u8>) {
	let mut writer = Vec::new();
	root.write(&mut writer);
	let mut sigma = hash_concatenation(&hash_acc,&writer);
	(<O as Oracle>::hash_to_x(&sigma),sigma)
    };
    Box::new(new_func)
}

pub fn iop_get_queries_to_niroa_get_queries<O:'static + Oracle, S:'static + Setup>(
    iop_get_query: Box<dyn Fn(&Vec<O>) -> Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>>) ->
    Box<dyn Fn(&Vec<O>,&Vec<MerkleTree<<O as Oracle>::C>>) -> (Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,Vec<Vec<Path<<O as Oracle>::C>>>)>{
	let new_func = move |oracles:&Vec<O>, trees: &Vec<MerkleTree<<O as Oracle>::C>>| -> (Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>, Vec<Vec<Path<<O as Oracle>::C>>>) {
	    let query_points = iop_get_query(oracles);
	    let mut paths = Vec::new();
	    for (i,tree) in trees.iter().enumerate(){
		let points = &query_points[i];
		let mut round_paths  = Vec::new();
		for point in points {
		    let path = tree.generate_proof(oracles[i].position(&point.0),&oracles[i].to_maybe_y(&point.0,&point.1)).unwrap();
		    round_paths.push(path)
		}
		paths.push(round_paths);
	    }
	    (query_points, paths)
	};
	Box::new(new_func)
	//so basically build up paths and then output iop get_query with those paths
    }

pub fn iop_query_to_niroa_query<O:'static + Oracle, S:'static + Setup>(
    iop_query: Box<dyn Fn(&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>, &S, &Vec<<O as Oracle>::X>) -> bool>) ->
    Box<dyn Fn(&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,&S, &Vec<<O as Oracle>::X>,&Vec<Digest<<O as Oracle>::C>>,&Vec<Vec<Path<<O as Oracle>::C>>>) -> bool>{
	let new_func =
	    move
	    |query_points:&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>, setup: &S, challenges: &Vec<<O as Oracle>::X>, roots: &Vec<Digest<<O as Oracle>::C>>, paths: &Vec<Vec<Path<<O as Oracle>::C>>> | -> bool{
		iop_query(query_points,setup,challenges)
		    //add merkle tree checks here
	    };
	Box::new(new_func)
    }



fn oracle_hash_func<O:'static + Oracle>(oracle:&O) -> (Digest<<O as Oracle>::C>,MerkleTree<<O as Oracle>::C>){
    let tree = oracle.to_tree();
    let root = tree.root();
    (root,tree)
}

	    
impl<'a, S:'static + Setup, O:'static + Oracle, W: 'static + Witness > From<Prover<'a,S,O,W>> for NiroaProver<O,S,W>{
    //convert IOP prover to NIROA prover
    fn from(p : Prover<'a,S,O,W>) -> Self{
	let niroa_funcs = p.prover_functions;
	NiroaProver{
	    prover_functions : niroa_funcs,
	    oracle_hash: Box::new(oracle_hash_func)
	}
    }
}
impl<'a, S:'static + Setup, O:'static + Oracle> From<Verifier<S,O>> for NiroaVerifier<S,O>{
    //convert IOP verifier to NIROA verifier
    fn from(v : Verifier<S,O>) -> Self{
	let mut verifier_challenges = Vec::new();
	//this is a bit confusing because for NIROA, we create totally new challenge functions, so verifier_challenges
	//is only used for enumeration
	for _ in v.verifier_challenges {
	    verifier_challenges.push(iop_challenges_to_niroa_challenges::<O,S>());
	}
	let get_query_points = iop_get_queries_to_niroa_get_queries::<O,S>(v.get_query_points);
	let verifier_query = iop_query_to_niroa_query::<O,S>(v.verifier_query);
	NiroaVerifier{
	    verifier_challenges,
	    get_query_points,
	    verifier_query
	}
    }
}
impl<'a,S:'static + Setup, O:'static + Oracle,W:'static + Witness> From<Iop<'a,O,S,W>> for Niroa<'a,O,S,W>{
    fn from(iop : Iop<'a,O,S,W>) -> Self{
	Self{
	    setup_params:iop.setup_params,
	    prover : NiroaProver::from(iop.prover),
	    verifier : NiroaVerifier::from(iop.verifier)
	}
    }
}


