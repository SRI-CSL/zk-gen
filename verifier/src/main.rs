use std::env;
use std::io::{Write,Error,Read};
use std::fs::{File,OpenOptions};
use sieve_fields::{Field}; //ark_bls12_381::{Fr};
use vlpa19::vlpa_marlin_integration::marlin::{get_rng};
use zkinterface_marlin::{verify_proof_as_vec, prover_reader,verifier_reader, get_constraint_count, get_variable_count,Circuit,get_proof_as_vec,get_pub_vars};
fn main() -> Result<(),Error>{
    //parse flatbuffers to get public input and number of constraints,
//    num variables
    //this is going to be common input
    let args:Vec<String> = env::args().collect();

    let mut rng = get_rng();
    let instance_file = args[1].clone();

    let relation_file = args[2].clone();

    let key_path = args[3].clone();
    let proof_path = args[4].clone();
    let output = args[5].clone();
    let pub_instance_reader = verifier_reader::<Field>(relation_file,instance_file);
    let pub_instance = get_pub_vars::<Field>(&pub_instance_reader);

    
    let mut same_key_file = File::open(key_path)?;
    let mut key_buff = Vec::new();
    same_key_file.read_to_end(&mut key_buff);


    let mut same_file = File::open(proof_path)?;
    let mut buffer = Vec::new();
    same_file.read_to_end(&mut buffer)?;

    let result = verify_proof_as_vec(pub_instance,buffer,&mut rng,key_buff);
    
    let mut output = File::create(output)?;
    let mut result_bytes:&[u8;1];
    if(result == true){
	result_bytes = b"1";
    }
    else{
	result_bytes = b"0";
    }
    output.write(&result_bytes[..]);
    
    Ok(())

}
