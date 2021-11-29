use std::env;
use std::io::{Write,Error,Read};
use std::fs::{File,OpenOptions};
use sieve_fields::{Field}; //ark_bls12_381::{Fr};
use vlpa19::vlpa_marlin_integration::marlin::{verify_proof_as_vec,get_circuit,get_rng,verifier_setup,serialize_vk,deserialize_vk};
use zkinterface_marlin::{prover_reader,verifier_reader, get_constraint_count, get_variable_count,Circuit,get_proof_as_vec};
fn main() -> Result<(),Error> {
    //read file srs
    let mut file = File::open("srs")?;
    let mut srs_buff = Vec::new();
    file.read_to_end(&mut srs_buff);
    let mut rng = get_rng();
    //read circuit
    let args:Vec<String> = env::args().collect();
    let instance_file = args[1].clone();
    let relation_file = args[2].clone();
    let witness_file = args[3].clone();
    let key_path = args[4].clone();
    let proof_path = args[5].clone();
    let reader = prover_reader::<Field>(relation_file,witness_file,instance_file);

    let circuit = Circuit::set_circuit(&reader);
    
    let (proof,key) = get_proof_as_vec::<Field>(srs_buff, &mut rng, &circuit);
    //write proof to file
    let mut file = File::create(proof_path)?;
    file.write_all(&proof[..])?;
    
    //write key to different file
    let mut v_file = File::create(key_path)?;
    v_file.write_all(&key[..])?;

    Ok(())
}
       

