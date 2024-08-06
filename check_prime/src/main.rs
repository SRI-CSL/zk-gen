use std::fs::{File,OpenOptions};
use std::io::{Write,Error,Read};
use ark_ff::{biginteger::{BigInteger256,BigInteger},
	     fields::FftField,FpParameters};

use std::path::{Path, PathBuf};
use zki_sieve::structs::{header::Header,message::Message};
use zki_sieve::consumers::source::Source;
use std::env;
use sieve_fields::Field;
fn main() -> Result<(),Error>{
    let valid_prime = <Field as FftField>::FftParams::MODULUS.to_bytes_le();
    let args:Vec<String> = env::args().collect();    
    let relation_file = args[1].clone();
    let output_file_name = args[2].clone();
    let source:Source = Source::from_directory(&Path::new(&relation_file)).ok().unwrap();

    let mut header:Header = Header::default();
    for msg in source.iter_messages(){
	header = match msg.unwrap(){
	    Message::Instance(h) => h.header,
	    _ => Header::default()
	}
    }
    let mut result = true;
    if valid_prime != header.field_characteristic{
	result = false;
	println!("Incorrect Field - please use the field whose modulus is the prime associated with the BN128 curve");
    }
    let mut output = File::create(output_file_name)?;
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
