use ark_ff::{ToBytes};
use num_traits::{One,Zero};
use ark_std::{fmt::Debug,string::String,marker::PhantomData,io::{Read,Write},ops::Add};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use ark_crypto_primitives::{merkle_tree::{MerkleTree,Path,Config,Digest},
			    crh::pedersen,FixedLengthCRH};
pub trait Oracle:
      ToBytes
    + Debug
    + Clone
    + Send
    + Sync
{
    type X : ToBytes + Debug + CanonicalSerialize + CanonicalDeserialize + Default + Clone + Add<Output = Self::X> + PartialEq + One + Send + Sync + ToBytes;
    type Y : ToBytes + Debug + CanonicalSerialize + CanonicalDeserialize + Default + Clone + Add<Output = Self::Y> + PartialEq + One + Zero + ToBytes;
    type C : Config;
    type Domain;
    fn to_vec(&self) -> Vec<(Self::X,Self::Y)>;
    fn points_to_domain(points: Vec<Self::X>) -> Self::Domain;
    fn from_vec(points: &Vec<(Self::X,Self::Y)>) -> Self{
	let (xs,ys) = points.iter().cloned().unzip();
	let new_domain = Self::points_to_domain(xs);
	Self::from_domain_and_evals(new_domain,ys)
    }
    fn to_evals(&self) -> Vec<Self::Y>;
    fn position(&self,domain_point:&Self::X) -> usize;
    fn hash_to_x(hash:&Vec<u8>) -> Self::X;
    fn to_maybe_y(&self,x : &Self::X, y: &Self::Y) -> Self::Y;
    fn from_domain_and_evals(domain:Self::Domain, evals:Vec<Self::Y>) -> Self;
    fn to_tree(&self) -> MerkleTree<Self::C>{
	let leaves = &self.to_evals();
	let mut rng = ark_std::test_rng();
	let crh_parameters = (<<Self as Oracle>::C as Config>::H::setup(&mut rng)).unwrap();
	let tree = MerkleTree::<Self::C>::new(crh_parameters.clone(), &leaves).unwrap();
	tree
    }
    
}
pub trait Setup{

}
pub trait Witness{
}
pub struct Prover<'a,S:Setup, O:Oracle, W:Witness>{
    pub prover_functions: Vec<fn((<O as Oracle>::X,Vec<O>,S,&W)) -> O>,
    pub witness: &'a W
}

pub struct Verifier<S:Setup,O:Oracle>{
    pub verifier_challenges: Vec<Box<dyn Fn(&Vec<O>,&S) -> <O as Oracle>::X>>,
    pub get_query_points: Box<dyn Fn(&Vec<O>) -> Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>>,
    pub verifier_query: Box<fn(&Vec<Vec<(<O as Oracle>::X,<O as Oracle>::Y)>>,&S, &Vec<<O as Oracle>::X>) -> bool>
}    
//using Box so size of type is known at compile-time
//https://www.reddit.com/r/rust/comments/aptl70/error_trait_size_is_not_known_at_compile_time
//oracles and setup_params have to be mutable references, so that they can be borrowed repeatedly
pub struct Iop<'a,O: Oracle, S:Setup, W:Witness> {
    pub setup_params: &'a S,
    pub prover: Prover<'a,S,O,W>,
    pub verifier: Verifier<S,O>,
    
}
pub struct IopProof<O:Oracle>{
    pub oracles: Vec<O>,
    pub challenges: Vec<<O as Oracle>::X>
}
impl<'a,O: Oracle,  S:Setup + Clone, W:Witness> Iop<'a,O,S,W> {
    pub fn commit_phase(&mut self) -> IopProof<O>{
	//zip together prover_functions and verifier functions
	let mut oracles = Vec::new();
	let mut challenges = Vec::new();
	let mut fns = self.verifier.verifier_challenges.iter().zip(self.prover.prover_functions.iter());
	for (v,p) in fns{
	    let challenge = v(&oracles,self.setup_params);
	    let s:S = (*self.setup_params).clone();
	    let next_oracle = p((challenge.clone(),oracles.clone(),s,self.prover.witness.clone()));
	    challenges.push(challenge);
	    oracles.push(next_oracle);
	}
	IopProof{
	    oracles: oracles,
	    challenges: challenges
	}

    }
    pub fn query_phase(&'a mut self,p : IopProof<O>) -> bool{
	let query_points  = (self.verifier.get_query_points)(&p.oracles);
	(self.verifier.verifier_query)(&query_points,self.setup_params,&p.challenges)
    }

}














