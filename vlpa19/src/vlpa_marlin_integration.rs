use ark_std::str::from_utf8;
use serde_json::json;
use ark_marlin::Proof;
use ark_ff::ToBytes;
use ark_serialize::{CanonicalSerialize,CanonicalDeserialize};
use ark_ff::Field;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError},
};
use ark_std::{marker::PhantomData,rand::{rngs::StdRng}};

#[derive(Copy, Clone)]
pub struct Circuit<F: Field> {
    a: Option<F>,
    b: Option<F>,
    num_constraints: usize,
    num_variables: usize,
}

impl<ConstraintF: Field> ConstraintSynthesizer<ConstraintF> for Circuit<ConstraintF> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ConstraintF>,
    ) -> Result<(), SynthesisError> {
        let a = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        let b = cs.new_witness_variable(|| self.b.ok_or(SynthesisError::AssignmentMissing))?;
        let c = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            Ok(a)
        })?;
        let d = cs.new_input_variable(|| {
            let mut a = self.a.ok_or(SynthesisError::AssignmentMissing)?;
            let b = self.b.ok_or(SynthesisError::AssignmentMissing)?;

            a.mul_assign(&b);
            a.mul_assign(&b);
            Ok(a)
        })?;

        for _ in 0..(self.num_variables - 3) {
            let _ = cs.new_witness_variable(|| self.a.ok_or(SynthesisError::AssignmentMissing))?;
        }

        for _ in 0..(self.num_constraints - 1) {
            cs.enforce_constraint(lc!() + a, lc!() + b, lc!() + c)?;
        }
        cs.enforce_constraint(lc!() + c, lc!() + b, lc!() + d)?;

        Ok(())
    }
}

#[derive(Clone)]
/// Define a constraint system that would trigger outlining.
struct OutlineTestCircuit<F: Field> {
    field_phantom: PhantomData<F>,
}

impl<F: Field> ConstraintSynthesizer<F> for OutlineTestCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // This program checks if the input elements are between 0 and 9.
        //
        // Note that this constraint system is neither the most intuitive way nor
        // the most efficient way for such a task. It is for testing purposes,
        // as we want to trigger the outlining.
        //
        let mut inputs = Vec::new();
        for i in 0..5 {
            inputs.push(cs.new_input_variable(|| Ok(F::from(i as u128)))?);
        }

        for i in 0..5 {
            let mut total_count_for_this_input = cs.new_lc(lc!()).unwrap();

            for bucket in 0..10 {
                let count_increment_for_this_bucket =
                    cs.new_witness_variable(|| Ok(F::from(i == bucket)))?;

                total_count_for_this_input = cs
                    .new_lc(
                        lc!()
                            + (F::one(), total_count_for_this_input)
                            + (F::one(), count_increment_for_this_bucket.clone()),
                    )
                    .unwrap();

                // Only when `input[i]` equals `bucket` can `count_increment_for_this_bucket` be nonzero.
                //
                // A malicious prover can make `count_increment_for_this_bucket` neither 0 nor 1.
                // But the constraint on `total_count_for_this_input` will reject such case.
                //
                // At a high level, only one of the `count_increment_for_this_bucket` among all the buckets
                // could be nonzero, which equals `total_count_for_this_input`. Thus, by checking whether
                // `total_count_for_this_input` is 1, we know this input number is in the range.
                //
                cs.enforce_constraint(
                    lc!() + (F::one(), inputs[i].clone())
                        - (F::from(bucket as u128), ark_relations::r1cs::Variable::One),
                    lc!() + (F::one(), count_increment_for_this_bucket),
                    lc!(),
                )?;
            }

            // Enforce `total_count_for_this_input` to be one.
            cs.enforce_constraint(
                lc!(),
                lc!(),
                lc!() + (F::one(), total_count_for_this_input.clone())
                    - (F::one(), ark_relations::r1cs::Variable::One),
            )?;
        }

        Ok(())
    }
}

pub mod marlin {
    use super::*;
    use ark_ff::PrimeField;
    use ark_marlin::{Marlin,IndexVerifierKey,IndexProverKey};
    use crate::{vlpa19_marlin::Vlpa19_Marlin,data_structures::UniversalParams};
    use ark_bls12_381::{Bls12_381, Fr};
    use ark_ff::UniformRand;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly_commit::marlin_pc::MarlinKZG10;
    use ark_std::ops::MulAssign;
    use blake2::Blake2s;

    type MultiPC =  Vlpa19_Marlin<Fr>; 
//    type MultiPC = MarlinKZG10<Bls12_381, DensePolynomial<Fr>>;   
    type MarlinInst = Marlin<Fr, MultiPC, Blake2s>;
    pub fn get_circuit(rng:&mut StdRng,num_constraints:usize,num_variables:usize) -> Circuit<Fr>{
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };
	    circ
    }
    pub fn test_circuit(num_constraints: usize, num_variables: usize) {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinInst::universal_setup(num_constraints, num_variables , num_constraints, rng).unwrap();

        for _ in 0..1 {
            let a = Fr::rand(rng);
            let b = Fr::rand(rng);
            let mut c = a;
            c.mul_assign(&b);
            let mut d = c;
            d.mul_assign(&b);

            let circ = Circuit {
                a: Some(a),
                b: Some(b),
                num_constraints,
                num_variables,
            };

            let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();
            println!("Called index");

            let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
	    //have accomplished proof -> u8 -> proof : now need to do u8 -> string -> u
	    


	    //serialize proof for transmission
	    let mut writer = Vec::new();
	    proof.serialize(&mut writer);
	    let mut val:&[u8] = &writer[..];

	    //deserialize transmitted message and read as proof
	    let value = Proof::deserialize(val);
	    println!("{:?}",value.as_ref().err());
	    //pass in read value as proof to verify
	    if let Some(p) = value.ok(){
		println!("SERIALIZATION WORKED");
		assert!(MarlinInst::verify(&index_vk, &[c, d], &p, rng).unwrap());
		assert!(!MarlinInst::verify(&index_vk, &[a, a], &proof, rng).unwrap());
	    }
	    else{
		panic!("proof did not get deserialized");
	    }
	   

//           println!("Called verifier");
   //         println!("\nShould not verify (i.e. verifier messages should print below):");
// 
        }
    }


    pub fn verify_proof_as_vec(instance:Vec<Fr>,proof:Vec<u8>,mut rng:&mut StdRng,vk:Vec<u8>) -> bool{
	let mut keyval:&[u8] = &vk[..];
	let v_key:IndexVerifierKey<Fr,MultiPC> = IndexVerifierKey::deserialize(keyval).ok().unwrap();
	let mut val:&[u8] = &proof[..];
	let value:Option<Proof<Fr,MultiPC>> = Proof::deserialize(val).ok();

	let mut is_valid:bool = false;
	//pass in read value as proof to verify
	assert_eq!(value.is_some(),true);
	if let Some(p) = value{
	    is_valid = MarlinInst::verify(&v_key, &instance[..], &p, &mut rng).unwrap();
	}
	is_valid
    }
   
    pub fn verifier_setup(rng:&mut StdRng, num_constraints:usize,num_variables:usize) -> Vec<u8> {
        let universal_srs = MarlinInst::universal_setup(num_constraints, num_variables, num_constraints, rng).unwrap();
	let mut writer = Vec::new();
	universal_srs.serialize(&mut writer);
	writer

    }
    pub fn serialize_vk(vk:IndexVerifierKey<Fr,MultiPC>) -> Vec<u8>{
	let mut writer = Vec::new();
	vk.serialize(&mut writer);
	writer
    }
    pub fn deserialize_vk(vk:Vec<u8>) -> IndexVerifierKey<Fr,MultiPC>{
	let mut val:&[u8] = &vk[..];
	IndexVerifierKey::<Fr,MultiPC>::deserialize(val).ok().unwrap()
    }
    pub fn get_rng() -> StdRng{
        ark_std::test_rng()
    }


    #[test]
    fn prove_and_verify_with_tall_matrix_big() {
//	let num_constraints = 100; //n = 2 .53, n = 4 .43, n = 5 .43, n = 6 .45, n= 7 .51  MOST RECENT 7/24 : .56s 
//	  let num_constraints = 500; //n = 2 2.27, n = 4 1.24, n = 6 1.13, n = 8 1.8, n = 10 8.97 7/24: 1.18s
//	let num_constraints = 1000; //n = 2 7.47 , n = 4 3.17, n = 6 2.58 , n = 8 3.66, n = 10 9.2 UPDATED on 8 cores: 1.75 seconds with n = log(domain)/2  7/24: 1.73
	let num_constraints = 10000; //n = 4: 12 minutes // n = 5, 8 minutes// n = k / 2 : ~4 minutes, now less than a minute with parallelization , no 48 seconds, now 18!: 7/24 : 41.78, 29.90
//		let num_constraints = 100000; //n=10 4 hours (probably takes an hour now), last metric was .6 of an hour with parallelization - no 19 minutes
//	let num_constraints = 1000000;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_tall_matrix_small() {
        let num_constraints = 26;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_big() {
        let num_constraints = 25;
        let num_variables = 100;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_squat_matrix_small() {
        let num_constraints = 25;
        let num_variables = 26;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    fn prove_and_verify_with_square_matrix() {
        let num_constraints = 25;
        let num_variables = 25;

        test_circuit(num_constraints, num_variables);
    }

    #[test]
    /// Test on a constraint system that will trigger outlining.
    fn prove_and_test_outlining() {
        let rng = &mut ark_std::test_rng();

        let universal_srs = MarlinInst::universal_setup(150, 150, 150, rng).unwrap();

        let circ = OutlineTestCircuit {
            field_phantom: PhantomData,
        };

        let (index_pk, index_vk) = MarlinInst::index(&universal_srs, circ.clone()).unwrap();
        println!("Called index");

        let proof = MarlinInst::prove(&index_pk, circ, rng).unwrap();
        println!("Called prover");

        let mut inputs = Vec::new();
        for i in 0..5 {
            inputs.push(Fr::from(i as u128));
        }

        assert!(MarlinInst::verify(&index_vk, &inputs, &proof, rng).unwrap());
        println!("Called verifier");
    }
}
