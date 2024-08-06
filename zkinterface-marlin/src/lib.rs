use std::{time::{Duration, Instant}};
use zkinterface::consumers::simulator::Simulator;
use zkinterface::ConstraintSystem;
use zkinterface::Messages;
use std::borrow::Borrow;
extern crate zkinterface;
extern crate ark_marlin;
use std::path::Path;
use ark_ff::{bytes::FromBytes, PrimeField};
use ark_relations::{lc,r1cs::{ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable as ZEXEVariable}};
use std::collections::HashMap;
use std::result::Result;
use zkinterface::{consumers::reader::{Reader,Variable as ZKIVariable}};
use vlpa19::data_structures::UniversalParams;
use ark_bls12_381::{Fr};
use ark_std::{marker::PhantomData,rand::{rngs::StdRng}};
use ark_std::{test_rng};
use ark_ff::{One};
use blake2::Blake2s;
use ark_marlin::{Marlin,AHPForR1CS,ahp::indexer::Index};//Error, Proof, UniversalSRS};
use vlpa19::vlpa19_marlin::Vlpa19_Marlin;
use ark_serialize::{CanonicalDeserialize,CanonicalSerialize};
use ark_marlin::{IndexVerifierKey,Proof};
#[derive(Copy, Clone, Debug)]
pub struct Circuit<'a> {
    reader: &'a Reader,
}

impl<'a> Circuit<'a>{
    pub fn set_circuit(reader:&'a Reader) -> Self{
	Circuit{
	    reader:reader
	}

    }
}
type MultiPC<F:PrimeField> = Vlpa19_Marlin<F>;/* MarlinKZG10<Bls12_381,DensePolynomial<Fr>>; */
type MarlinInst<F:PrimeField> = Marlin<F, MultiPC<F>, Blake2s>;

impl<'a,F: PrimeField> ConstraintSynthesizer<F> for Circuit<'a> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<F>,
    ) -> Result<(), SynthesisError> {
        let pub_vars = self.reader.instance_variables().unwrap();
        let priv_vars = self.reader.private_variables().unwrap();

        let mut all_vars = HashMap::<u64,ZEXEVariable>::new();

        all_vars.insert(0, ZEXEVariable::One);

        for var in pub_vars {
	    let field_elem = zkif_value_to_field_elem::<F>(var.value);
            all_vars.insert(var.id, cs.new_input_variable(
                || field_elem,
            )?);
       }

	// providing dummy inputs so num of pub inputs is a power of 2 as required by marlin

        while cs.num_instance_variables().count_ones() != 1 {
            cs.new_input_variable(|| Ok(F::one()))?;
        }

        for var in priv_vars {
            all_vars.insert(var.id, cs.new_witness_variable(
                || zkif_value_to_field_elem::<F>(var.value),
            )?);
        }

        for constraint in self.reader.iter_constraints() {
            cs.enforce_constraint(
                zkif_to_zexe_lc(&constraint.a, &all_vars),
                zkif_to_zexe_lc(&constraint.b, &all_vars),
                zkif_to_zexe_lc(&constraint.c, &all_vars),
            )?;
        }

        Ok(())
    }
}

pub fn zkif_to_zexe_lc<F: PrimeField>(vals: &Vec<ZKIVariable>, id_to_var: &HashMap<u64, ZEXEVariable>) -> LinearCombination<F> {
    let mut coeff_var = Vec::new();
    for var in vals {
	let field_coeff = zkif_value_to_field_elem(&var.value).ok().unwrap();
        match id_to_var.get(&var.id) {
            Some(zexe_var) => coeff_var.push((field_coeff,*zexe_var)),
            _ => println!("variable {} not found", var.id),
        }
    }
    LinearCombination(coeff_var)
}

// taken from Pratyush Mishra's code
pub fn zkif_value_to_field_elem<F: PrimeField>(val: &[u8]) -> Result<F,SynthesisError> {

    if val.len() == 0 {
        return Ok(F::zero());
    }

    let mut val = Vec::from(val);
    
    let words = (F::size_in_bits() + 63) / 64;
    val.resize(8 * words as usize, 0);
    
    let repr = FromBytes::read(val.as_slice()).unwrap();
    
    let ret = F::from_repr(repr).unwrap_or(F::zero());
    
    Ok(ret)
}

pub fn get_constraint_count<F:PrimeField>(reader:&Reader) -> usize{
    let mut constraints = Vec::new();
    for c in reader.iter_constraints(){
	constraints.push(c);
    }
    constraints.len()

}

pub fn get_variable_count<F:PrimeField>(reader:&Reader) -> usize{
    let mut count = 0;
    for v in reader.instance_variables().unwrap(){
	count = count + 1;
    }
    for v2 in reader.private_variables().unwrap(){
	count = count + 1;
    }
    count
}


pub fn get_pub_vars<F:PrimeField>(reader:&Reader) -> Vec<F>{
    let pub_vars = reader.instance_variables().unwrap();
    let mut pub_input = Vec::new();
    for var in pub_vars {
        pub_input.push(zkif_value_to_field_elem::<F>(var.value).unwrap());
    }
    // provide dummy inputs so num of inputs is a power of 2
    while (pub_input.len()+1).count_ones() != 1 {
        pub_input.push(F::one());
    }
    pub_input
}
pub fn verifier_setup<F:PrimeField>(rng:&mut StdRng, reader: &Reader) -> Vec<u8> {
    let circuit = Circuit::set_circuit(&reader);
    let index:Index<F> = AHPForR1CS::index(circuit.clone()).ok().unwrap();
        let universal_srs = MarlinInst::<F>::universal_setup(index.index_info.num_constraints, index.index_info.num_variables, index.index_info.num_non_zero, rng).unwrap();
	let mut writer = Vec::new();
	universal_srs.serialize(&mut writer);
	writer

}

pub fn serialize_vk<F:PrimeField>(vk:IndexVerifierKey<F,MultiPC<F>>) -> Vec<u8>{
	let mut writer = Vec::new();
	vk.serialize(&mut writer);
	writer
}
pub fn deserialize_srs<F:PrimeField>(srs:&Vec<u8>) -> UniversalParams<F>{
    let mut val:&[u8] = &srs[..];
    let tt_srs = UniversalParams::<F>::deserialize(val);//ok().unwrap();
    tt_srs.ok().unwrap()
}
pub fn get_proof_as_vec<F:PrimeField>(srs:Vec<u8>, rng: &mut StdRng, circ: &Circuit) ->(Vec<u8>,Vec<u8>) {
	let mut val:&[u8] = &srs[..];
    let tt_srs = UniversalParams::<F>::deserialize(val);//ok().unwrap();
    let t_srs = tt_srs.ok().unwrap();
	let (index_pk, index_vk) = MarlinInst::index(&t_srs, circ.clone()).unwrap();
        let proof = MarlinInst::prove(&index_pk, *circ,  rng).unwrap();
	let mut writer = Vec::new();
	proof.serialize(&mut writer); //serialize prover
	let mut val:&[u8] = &writer[..];

	let vkey_bytes = serialize_vk(index_vk);
	(val.to_vec(),vkey_bytes)
    }
  pub fn verify_proof_as_vec<F:PrimeField>(instance:Vec<F>,proof:Vec<u8>,mut rng:&mut StdRng,vk:Vec<u8>) -> bool{
	let mut keyval:&[u8] = &vk[..];
	let v_key:IndexVerifierKey<F,MultiPC<F>> = IndexVerifierKey::<F,MultiPC<F>>::deserialize(keyval).ok().unwrap();
	let mut val:&[u8] = &proof[..];
	let value:Option<Proof<F,MultiPC<F>>> = Proof::deserialize(val).ok();

	let mut is_valid:bool = false;
	//pass in read value as proof to verify
	assert_eq!(value.is_some(),true);
	if let Some(p) = value{
	    is_valid = MarlinInst::verify(&v_key, &instance[..], &p, &mut rng).unwrap();
	}
	is_valid
  }

pub fn verifier_reader<F:PrimeField>(relation_file: String, instance_file: String) -> Reader{
    let mut reader = Reader::new();
    reader.read_file(relation_file).unwrap();
    reader.read_file(instance_file).unwrap();

    reader
}

pub fn prover_reader<'a,F:PrimeField>(relation_file:String,witness_file:String,instance_file:String) -> Reader{
    let mut prover_input = Reader::new();
    prover_input.read_file(relation_file).unwrap();
    prover_input.read_file(witness_file).unwrap();
    prover_input.read_file(instance_file).unwrap();
    prover_input
}

#[cfg(test)]
mod tests {

    use super::*;

 //   use ark_test_curves::{bls12_381::Fr, Bls12_381};//, Field, FromBytes, UniformRand};
    use ark_std::{test_rng};
    use ark_bls12_377::{Fr};

    use ark_ff::{One};
    use blake2::Blake2s;
    use ark_marlin::Marlin;//Error, Proof, UniversalSRS};

    use std::path::Path;
    use zkinterface::Reader;
    use vlpa19::vlpa19_marlin::Vlpa19_Marlin;
    

    type MultiPC = Vlpa19_Marlin<Fr>;/* MarlinKZG10<Bls12_381,DensePolynomial<Fr>>; */
    type MarlinInst = Marlin<Fr, MultiPC, Blake2s>;


   
    fn test_circuit( witness:String,relation:String,instance:String){
	let setup_time_start = Instant::now();	
        let rng = &mut test_rng();
	let reader = verifier_reader::<Fr>(relation.clone(),instance.clone());
	let circuit = Circuit::set_circuit(&reader);	
        let index:Index<Fr> = AHPForR1CS::index(circuit.clone()).ok().unwrap();
        let universal_srs = MarlinInst::universal_setup(index.index_info.num_constraints, index.index_info.num_variables, index.index_info.num_non_zero, rng).unwrap();
        //TODO get numbers from messages
        println!("done with setup");

	let reader = prover_reader::<Fr>(relation.clone(),witness.clone(),instance.clone());
        let circ = Circuit{
	    reader: &reader
	};

        let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();

        println!("done with indexing");
	println!("setup time {:?}", setup_time_start.elapsed().as_millis());

	let proof_time_start = Instant::now();
        let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
	println!("proof time {:?}", proof_time_start.elapsed().as_millis());	

        println!("done with proving");


        let pub_input_func = verifier_reader::<Fr>(relation,instance);
	let pub_vars = get_pub_vars(&pub_input_func);
	let verify_time_start = Instant::now();	 	
        assert!(MarlinInst::verify(&index_vk, pub_vars.as_slice(), &proof, rng).unwrap());
	println!("verify time {:?}", verify_time_start.elapsed().as_millis());       
        // should fail since public inputs are now in the wrong order
        let mut wrong = pub_vars;
	wrong.reverse();
        assert!(!MarlinInst::verify(&index_vk, wrong.as_slice(), &proof, rng).unwrap());
        
        println!("done with verifying");
    }



    #[test]
    fn bellman_circuit_test(){
        test_circuit("./rand_five0_r1cs/witness.zkif".to_string(), "./rand_five0_r1cs/constraints.zkif".to_string(), "./rand_five0_r1cs/header.zkif".to_string());
    }


}
