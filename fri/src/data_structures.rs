 use ark_std::collections::BTreeMap;
use ark_ff::{PrimeField,ToBytes};
use ark_poly::{domain::{Radix2EvaluationDomain},evaluations::{univariate::{Evaluations}},polynomial::{univariate::{DensePolynomial}}};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize};
use ark_std::{io::{Read,Write}};
use derivative::Derivative;
pub type RSCodeDomain<F:PrimeField> = Option<Radix2EvaluationDomain<F>>;

pub type Codeword<F:PrimeField> = Option<Evaluations<F,Radix2EvaluationDomain<F>>>;

#[derive(Derivative,CanonicalSerialize,CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct NonTerminalRound<F:PrimeField> {
    pub index : usize,
    pub codeword : Codeword<F>,
    pub challenge: Option<F>,
    pub n : u32,
    pub k : u32,
    pub r: u32
}
impl<F:PrimeField> ToBytes for NonTerminalRound<F>{
    fn write<W:Write>(&self,mut writer:W)->ark_std::io::Result<()>{
	self.challenge.unwrap().write(&mut writer)?;
	self.n.write(&mut writer)?;
	self.r.write(&mut writer)?;
	self.codeword.as_ref().unwrap().evals.write(&mut writer)
    }
}
#[derive(Derivative,CanonicalSerialize,CanonicalDeserialize)]
#[derivative(
    Default(bound= ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct TerminalRound<F: PrimeField> {
    pub poly: Option<DensePolynomial<F>>,
    pub domain : RSCodeDomain<F>
}
impl<F:PrimeField> ToBytes for TerminalRound<F>{
    fn write<W:Write>(&self,mut writer:W)->ark_std::io::Result<()>{
	self.domain.unwrap().size.write(&mut writer)?;
	self.poly.as_ref().unwrap().coeffs.write(&mut writer)
    }
}
#[derive(Debug)]
pub enum Round<F:PrimeField> {
    NonTerminalRound_(NonTerminalRound<F>),
    TerminalRound_(TerminalRound<F>)
}
impl<F:PrimeField> ToBytes for Round<F>{
    fn write<W:Write>(&self,mut writer:W)->ark_std::io::Result<()>{
	let round = match self{
	    Round::TerminalRound_(r) => r.write(&mut writer),
	    Round::NonTerminalRound_(r) => r.write(&mut writer)
	};
	round
    }
}
impl<F:PrimeField> Clone for Round<F>{
    fn clone(&self) -> Self{
	match self {
	    Round::NonTerminalRound_(r) => Round::NonTerminalRound_(r.clone()),
	    Round::TerminalRound_(r) => Round::TerminalRound_(r.clone())
	}
    }
}
impl<F:PrimeField> CanonicalDeserialize for Round<F>{
    fn deserialize<R:Read>(mut reader:R)->Result<Self,SerializationError>{
	let candidate_round = NonTerminalRound::deserialize(&mut reader);
	let round = match candidate_round{
	    Ok(_) => Round::NonTerminalRound_(candidate_round?),
	    _ => Round::TerminalRound_(TerminalRound::deserialize(&mut reader)?)
	};
	Ok(round)
    }
}
impl<F:PrimeField> CanonicalSerialize for Round<F>{
    fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	match self{
	    Round::NonTerminalRound_(r) => r.serialize(&mut writer)?,
	    Round::TerminalRound_(r) => r.serialize(&mut writer)?
	};
	Ok(())
    }
    fn serialized_size(&self) -> usize{
	0
    }
 }
