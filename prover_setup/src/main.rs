
use std::env;
use std::io::{Write,Error,Read};
use std::fs::{File,OpenOptions};
use sieve_fields::{Field};//ark_bls12_381::{Fr};
use vlpa19::vlpa_marlin_integration::marlin::{verify_proof_as_vec,get_circuit,get_rng,serialize_vk,deserialize_vk};
use zkinterface_marlin::{prover_reader,verifier_reader, get_constraint_count, get_variable_count,deserialize_srs,verifier_setup};
fn main() -> Result<(),Error>{
    //parse flatbuffers to get public input and number of constraints, num variables    //compute srs and store it in file `srs`
    let args:Vec<String> = env::args().collect();
    let instance_file = args[1].clone();
    let relation_file = args[2].clone();
    let reader = verifier_reader::<Field>(relation_file,instance_file);
    let mut rng = get_rng();
    let srs = verifier_setup::<Field>(&mut rng,&reader);
    
    let srs_d = deserialize_srs::<Field>(&srs);
    
    let mut file = File::create("srs")?;
    file.write_all(&srs[..])?;

    
    

    Ok(())

}
