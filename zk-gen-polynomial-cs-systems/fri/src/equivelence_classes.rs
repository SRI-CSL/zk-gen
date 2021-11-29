#[path="data_structures.rs"] pub mod data_structures;
#[path="parallelize.rs"] pub mod parallelize;

use derivative::Derivative;
use std::time::{Duration, Instant};
use parallelize::{parallel_function};
use data_structures::{RSCodeDomain,Codeword};
use ark_ff::{PrimeField,ToBytes};
use ark_serialize::{CanonicalSerialize,SerializationError,CanonicalDeserialize,Write,Read};
use ark_poly::{domain::{EvaluationDomain,Radix2EvaluationDomain},evaluations::{univariate::{Evaluations}},polynomial::{Polynomial,univariate::{DensePolynomial,SparsePolynomial}, UVPolynomial}};
use std::collections::{BTreeMap,HashMap};
#[derive(Derivative)]
#[derivative(
    Default(bound= ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct EquivClass<F:PrimeField> {
    pub equiv_classes: HashMap<F,Vec<(F,F)>>
}

#[derive(Derivative)]
#[derivative(
    Default(bound= ""),
    Clone(bound = ""),
    Debug(bound= "")
)]
pub struct DomainEquivClass<F:PrimeField> {
    pub equiv_classes: HashMap<usize,HashMap<F,F>>
}
impl<F:PrimeField> CanonicalSerialize for DomainEquivClass<F>{
    fn serialize<W:Write>(&self,mut writer:W) -> Result<(),SerializationError>{
	Ok(())
    }
    fn serialized_size(&self) -> usize{
	0
    }

}
impl<F:PrimeField> CanonicalDeserialize for DomainEquivClass<F>{
    fn deserialize<R:Read>(mut reader:R) -> Result<Self,SerializationError>{
	Ok(DomainEquivClass{
	    equiv_classes: HashMap::new()
	})
    }
}
impl<F:PrimeField> DomainEquivClass<F>{
    pub fn new() -> Self{
	DomainEquivClass{
	    equiv_classes:HashMap::new()
	}
    }
}
fn add_restr_el<F : PrimeField >(restriction: &Vec<F>, index:usize,x:F) -> Option<usize>{
    let result = restriction.into_iter().find(|y| y == &&x);

    if result.is_none(){
	return None;
    }
    else{
	return Some(index);
    }	
}
fn hashmap_insert<F: PrimeField>(key : F, val: F, hm : &mut HashMap<F,Vec<F>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
fn get_restricted_indices<F:PrimeField>(restriction: &Vec<F>, d : RSCodeDomain<F>) -> Vec<Option<usize>> {
   d.unwrap().elements().enumerate().map(|(i,x)|-> Option<usize>{return add_restr_el(&restriction,i,x);}).collect()
}


fn get_restricted_codeword<F:PrimeField>(x : &Vec<F>, c: &Codeword<F>, domain: RSCodeDomain<F>) -> (Vec<F>){

    let indices = get_restricted_indices(&x,domain);

    let orig_y = &c.as_ref().unwrap().evals;
    let mut new_y = Vec::new();
    for i in indices{
	if i.is_some(){
	    new_y.push(orig_y[i.unwrap()]);
	}
    }
    new_y
}
fn insert<F: PrimeField>(key : F, val: (F,F), hm : &mut HashMap<F,Vec<(F,F)>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
impl<F:PrimeField> EquivClass<F>{
    //need to implement the following functions:
    //get_next_domain
    //get_restricted_codeword
    //but we will combine them into one function called
    //get_equiv_classes
    pub fn get_equiv_classes(/*q : &SparsePolynomial<F>, */prev_codeword: &Codeword<F>,challenge:F) -> (HashMap<F,Vec<F>>,EquivClass<F>){
	let mut subtract_map = HashMap::new();
	let mut equiv_classes = HashMap::new();
	let codeword = prev_codeword.as_ref().unwrap();
	let c:Vec<F> = codeword.domain().elements().collect();

	for (index,elem) in codeword.domain().elements().enumerate(){

	    let eval = Self::evaluate_q(&elem);

	    insert(eval,(elem.clone(),codeword.evals[index]),&mut equiv_classes);
	    hashmap_insert(eval, (challenge - elem.clone()), &mut subtract_map);
	}
	(subtract_map,EquivClass{equiv_classes })
    }
    pub fn evaluate_q(elem:&F) -> F{
	let mut e = *elem;
	*e.square_in_place();
	e * e
    }
   pub fn get_equiv_class_with_y(codeword:&Codeword<F>, ec_map:&DomainEquivClass<F>,round_num:usize) -> EquivClass<F>{
       let mut equiv_classes = HashMap::new();
       let map = ec_map.equiv_classes.get(&round_num).unwrap();
	let codeword = &codeword.as_ref().unwrap();
 
       for (index,elem) in codeword.domain().elements().enumerate(){
  	    insert(*map.get(&elem).unwrap(),(elem,codeword.evals[index]),&mut equiv_classes);
	}

       EquivClass{ equiv_classes }
   }
    pub fn get_equiv_classes_for_first_domain(domain: &Radix2EvaluationDomain<F>) -> HashMap<F,F>{
	let mut equiv_classes:HashMap<F,F> = HashMap::new();


        let now = Instant::now();
	for (elem) in domain.elements(){

	    let eval = Self::evaluate_q(&elem);
	    equiv_classes.insert(elem,eval);

	}
	equiv_classes 
    }

 pub fn get_domain_equiv_classes(domain: &Radix2EvaluationDomain<F>,num_round:usize) -> DomainEquivClass<F>{
	let mut equiv_classes = HashMap::new();
        let now = Instant::now();
        let first_round = Self::get_equiv_classes_for_first_domain(domain);
	equiv_classes.insert(0usize, first_round);
	for i in 0..num_round{
	    let mut round_map = HashMap::new();
	    for elem in equiv_classes.get(&i).unwrap().keys(){
		let eval = Self::evaluate_q(elem);
		round_map.insert(*elem,eval);

	    }
            equiv_classes.insert(i+1,round_map);
	}
	DomainEquivClass{ equiv_classes }
 }
}
