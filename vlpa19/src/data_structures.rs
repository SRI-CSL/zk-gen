use crate::vlpa19::{Vlpa19};
use ark_std::collections::BTreeMap;
use ark_ff::{PrimeField, Zero, FpParameters,One, BigInteger256, Field, FftField, FftParameters,ToBytes,FromBytes};
use ark_poly_commit::{PolynomialCommitment,data_structures::*};
use ark_poly::{domain::{EvaluationDomain,GeneralEvaluationDomain,Radix2EvaluationDomain},polynomial::{Polynomial,univariate::{DensePolynomial,SparsePolynomial}, UVPolynomial}};
use rand_core::RngCore;
use ark_std::{string::String,marker::PhantomData,io::{Read,Write}};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use fri::{RSCodeDomain,Round,setup,TerminalRound,Codeword,fri::niroa::{NiroaProof,NiroaBatchProof, MerkleRoot, prover_init},H,BlakeMerkleTreeParams,FRISetup};
use derivative::Derivative;
use ark_crypto_primitives::merkle_tree::{Digest,Path};


pub struct WitnessProof<F:PrimeField>{
    pub degree_bound:usize,
    pub proof: FriProof<F>,
    pub sim_query_points : Vec<(F,F)>,
    pub sim_paths: Vec<Path<BlakeMerkleTreeParams>>,
    pub eval: F,
    pub point : F
}
#[derive(CanonicalSerialize,CanonicalDeserialize,Clone)]
pub struct Proof<F:PrimeField>{
    pub proof:Vec<WitnessProof<F>>,
}
impl<F:PrimeField> CanonicalSerialize for WitnessProof<F>{
    fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	self.degree_bound.serialize(&mut writer);
	self.proof.serialize(&mut writer)?;
	self.sim_query_points.serialize(&mut writer)?;
	self.eval.serialize(&mut writer)?;
	self.point.serialize(&mut writer)?;
//	TODO self.sim_paths.serialize(&mut writer)?;
	Ok(())
    }
    fn serialized_size(&self) -> usize{
	0usize
    }
}
//stub
impl<F:PrimeField> CanonicalDeserialize for WitnessProof<F>{
    fn deserialize<R:Read>(mut reader:R)->Result<Self,SerializationError>{
	let degree_bound = usize::deserialize(&mut reader)?;
	let proof = FriProof::<F>::deserialize(&mut reader)?;
	let sim_query_points = Vec::<(F,F)>::deserialize(&mut reader)?;
	let eval = F::deserialize(&mut reader)?;
	let point = F::deserialize(&mut reader)?;
//	TODO let sim_paths = Vec::<Path<BlakeMerkleTreeParams>>::deserialize(&mut reader)?;
	Ok(WitnessProof{
	    degree_bound:degree_bound,
	    proof: proof,
	    sim_query_points: sim_query_points,
	    sim_paths: Vec::new(),
	    eval:eval,
	    point:point
	})
    }
}
impl<F:PrimeField> Clone for WitnessProof<F>{
    fn clone(&self) -> Self {
	Self{
	     proof:self.proof.clone(),
	    sim_query_points: self.sim_query_points.clone(),
	    sim_paths : Vec::new(),
	    degree_bound: self.degree_bound.clone(),
	    eval: self.eval.clone(),
	    point:self.point.clone()
	}
    }
}
impl<F:PrimeField> ToBytes for WitnessProof<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.proof.write(writer)
    }
}
impl<F:PrimeField> ToBytes for Proof<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.proof.write(writer)
    }
}
impl<F:PrimeField> PCProof for Proof<F>{
    fn size_in_bytes(&self)->usize{
	//stub
	0
    }
}


#[derive(CanonicalSerialize,CanonicalDeserialize)]
pub struct ProofLC<F:PrimeField>{
    pub proof:Proof<F>,
    pub lc_label: String
    
}
impl<F:PrimeField> ProofLC<F>{
    pub fn set_lc_label(&mut self,lc_label:String){
	self.lc_label = lc_label;
    }
    pub fn label(&self)->&String{
	&self.lc_label
    }
}
impl<F:PrimeField> Clone for ProofLC<F>{
    fn clone(&self) -> Self {
	Self{proof:self.proof.clone(),lc_label:self.lc_label.clone()}
    }
}
impl<F:PrimeField> ToBytes for ProofLC<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.proof.write(writer)
    }
}
impl<F:PrimeField> PCProof for ProofLC<F>{
    fn size_in_bytes(&self)->usize{
	//stub
	0
    }
} 
#[derive(Clone,Debug,CanonicalSerialize,CanonicalDeserialize,Default)]
pub struct Randomness{
}
impl PCRandomness for Randomness{
    fn empty()->Self{
	Randomness{}
    }

    fn rand<R:RngCore>(
	num_queries:usize,
	has_degree_bound:bool,
	num_vars:Option<usize>,
	rng:&mut R,
    ) -> Self{
	Randomness{}
    }
}
pub type TempProof<F:PrimeField> = NiroaProof<Round<F>>;
#[derive(Debug,CanonicalSerialize,CanonicalDeserialize,Default)]
pub struct FriProof<F:PrimeField>(
    pub NiroaProof<Round<F>>
);
impl<F:PrimeField> Clone for FriProof<F>{
    fn clone(&self) -> Self {
	let mut proof = prover_init::<Round<F>>();
	for i in &self.0.query_points {
	    proof.paths = Vec::new();
	    proof.query_points = self.0.query_points.clone();
	    proof.sigma = self.0.sigma.clone();
	    proof.challenges = self.0.challenges.clone();

	}
	Self(proof)
    }
}
impl<F:PrimeField> ToBytes for FriProof<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.0.write(writer)
    }
}
#[derive(Debug,CanonicalSerialize,CanonicalDeserialize,Clone)]
pub struct PreparedCommitment<F:PrimeField>{
    _f:F
}
impl<F:PrimeField> PCPreparedCommitment<Commitment<F>> for PreparedCommitment<F>{
    fn prepare(comm: &Commitment<F>) -> Self{
	Self{
	    _f:F::zero()
	}
    }
}
#[derive(Debug,Clone,Default)]
pub struct Commitment<F:PrimeField>{
    pub fri_proof: FriProof<F>,
    pub lc_eval_root: MerkleRoot<Round<F>>,
    pub degree_bound: usize,
    pub label: String
	
}

impl<F:PrimeField> CanonicalSerialize for Commitment<F>{
    fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	self.fri_proof.serialize(&mut writer);
	let mut bytes_writer = Vec::new();
	self.lc_eval_root.write(&mut bytes_writer);
	bytes_writer.serialize(&mut writer);
	self.degree_bound.serialize(&mut writer);
	self.label.serialize(&mut writer);
	Ok(())
    }
    fn serialized_size(&self) -> usize{
	0usize
    }
}

impl<F:PrimeField> CanonicalDeserialize for Commitment<F>{
    fn deserialize<R:Read>(mut reader:R) -> Result<Self,SerializationError>{
	let fri_proof = FriProof::<F>::deserialize(&mut reader).ok().unwrap();
	let bytes_lc_eval = Vec::<u8>::deserialize(&mut reader).ok().unwrap();
	let eval_root = MerkleRoot::<Round<F>>::read(&bytes_lc_eval[..]).ok().unwrap();
	let degree_bound = usize::deserialize(&mut reader).ok().unwrap();
	let label = String::deserialize(&mut reader).ok().unwrap();
	return Ok(Self{
	    fri_proof:fri_proof,
	    lc_eval_root: eval_root,
	    degree_bound: degree_bound,
	    label: label
	});
    }
	
}
//as a placeholder implement CS and CD manually
//but actually just implement it in merkle tree library, since you
//already have the code to do that!

impl<F:PrimeField> ToBytes for Commitment<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.fri_proof.write(writer)
    }
}
impl<F:PrimeField> PCCommitment for Commitment<F>{
    fn empty() -> Self {
	//stub
	Commitment{
	    fri_proof:FriProof(prover_init::<Round<F>>()),
	    lc_eval_root: [0;32],
	    degree_bound : 0usize,
	    label: "label".to_string()
	}
    }
    fn has_degree_bound(&self)->bool{
	//stub
	true
    }
    fn size_in_bytes(&self)->usize{
	//stub
	0
    }
}
#[derive(Debug,CanonicalSerialize,CanonicalDeserialize,Clone)]
pub struct CommitmentMulDegreeBounds<F:PrimeField>{
    pub commitment:Commitment<F>,
    pub shifted_commitment:Option<Commitment<F>>
}
impl<F:PrimeField> ToBytes for CommitmentMulDegreeBounds<F>{
    #[inline]
    fn write<W:Write>(&self,writer:W) -> ark_std::io::Result<()>{
	self.commitment.write(writer)
    }
}
impl<F:PrimeField> PCCommitment for CommitmentMulDegreeBounds<F>{
    fn empty() -> Self {
	//stub
	Self {
	    shifted_commitment: Some(Commitment::empty()),
	    commitment:Commitment::empty()
	}
    }
    fn has_degree_bound(&self)->bool{
	//stub
	true
    }
    fn size_in_bytes(&self)->usize{
	//stub
	0
    }
}
//PreparedVerifierKey is a stub
#[derive(Clone, Debug)]
pub struct PreparedVerifierKey<F:PrimeField>{
    _f:F
}
impl<F:PrimeField> PCPreparedVerifierKey<VerifierKey<F>> for PreparedVerifierKey<F>{
    fn prepare(vk: &VerifierKey<F>) -> Self{
	Self{_f:F::zero()}
    }
}
	
#[derive(Clone,Debug,CanonicalSerialize,CanonicalDeserialize)]
pub struct VerifierKey<F:PrimeField> {
    pub initial_domain:RSCodeDomain<F>,
    pub n:u32,
    pub r:u32,
    pub log_domain_size:u32
}

impl<F:PrimeField> PCVerifierKey for VerifierKey<F>{
    fn max_degree(&self) -> usize{
	//stub
	0
    }
    fn supported_degree(&self)->usize{
	//stub
	0
    }
	  
}



#[derive(Derivative,CanonicalSerialize,CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct CommitterKey<F:PrimeField> {
    pub setup: FRISetup<F>,
    pub log_domain_size : u32, //k
    pub initial_domain: RSCodeDomain<F>,
    pub n : u32,
    pub rate_param:u32,
    pub max_degree: usize,
    pub enforced_degree_bounds: Option<Vec<usize>>,
    pub c_alphas: BTreeMap<(usize,F),Vec<(F,F)>>
}

impl<F:PrimeField> PCCommitterKey for CommitterKey<F>{
    fn max_degree(&self) -> usize{
	self.max_degree
    }
    fn supported_degree(&self)->usize{
	self.max_degree()
    }
	  
}


#[derive(Derivative,CanonicalSerialize,CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
    Hash(bound = ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct UniversalParams<F:PrimeField> {
    pub log_domain_size : u32, //k
    pub initial_domain: RSCodeDomain<F>,
    pub n : u32,
    pub rate_param: u32,
    pub max_degree:usize
}

impl<F:PrimeField> PCUniversalParams for UniversalParams<F>{
    fn max_degree(&self) -> usize{
	self.max_degree
    }
}




