use ark_std::fmt::Debug;
use std::hash::Hash;
use std::collections::{BTreeMap,HashMap};
use std::time::{Duration, Instant};
extern crate num_cpus;
use std::thread;
use crossbeam_channel::bounded;
use ark_ff::{FftField, FftParameters, Field, One, PrimeField, Zero};
use ark_test_curves::bls12_381::{Fr};
type Func<In,Out> = fn(In) -> Out;
//I have a vector of things I want to run the same function on
//So split the vector into batches - and then in each core, execute function on each element of sub vector
//then recombine
fn insert<F: PrimeField>(key : F, val: F, hm : &mut BTreeMap<F,Vec<F>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
pub fn parallel_function<In: Clone + Send + Sync, Out: Clone + Send + Sync>(ys : &Vec<In>, fun : Func<In,Out>) -> Vec<(usize,Out)> {
    let cores:usize = num_cpus::get_physical();
     let max = ys.len();
     let (snd,rcv) = bounded(1);
    let mut results = Vec::new();
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);

	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let batches = &ys[next..(next + this_batch_size)]; // 0 to 2

	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		for (index,y) in batches.iter().enumerate(){
		    let mut local_results = Vec::new();
		    local_results.push((index + next,fun(y.clone())));
		    sen.send(local_results).unwrap();
		}
	    
	    });

	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		results.push(item);
	    }
	}

    }).unwrap();
    
    results
}

type FunAux<In,Out,Aux,Key> = fn(In,Key,Aux) -> Out;
//I have a vector of things I want to run the same function on
//So split the vector into batches - and then in each core, execute function on each element of sub vector
//then recombine
pub fn parallel_btreemap<Aux: Clone + Send + Sync, Key: Clone + Send + Sync + Ord, In: Clone + Send + Sync, Out: Clone + Send + Sync>(map : BTreeMap<Key,In>, aux: Vec<Aux>, fun : FunAux<In,Out,Aux,Key>) -> BTreeMap<Key,Out> {
    let mut new_map = BTreeMap::new();
    let cores:usize = num_cpus::get_physical();
    let keys:Vec<Key> = map.keys().map(|k| k.clone()).collect();
     let max = keys.len();
     let (snd,rcv) = bounded(1);
    let ref_map = &map;
    let ref_aux = &aux;
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let key_batches = &keys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		for (index,key) in key_batches.iter().enumerate(){
		    let mut local_results = Vec::new();
		    let counter = index + next;
		    if(ref_aux.len() > counter){
			local_results.push((key,fun(ref_map.get(key).unwrap().clone(),(key.clone()),ref_aux[index + next].clone())));
		    }
		    else{
			local_results.push((key,fun(ref_map.get(key).unwrap().clone(),(key.clone()),ref_aux[0].clone())));
		    }
		    sen.send(local_results).unwrap();
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		new_map.insert(item.0.clone(),item.1);
	    }
	}
    }).unwrap();
    new_map
}

//I have a vector of things I want to run the same function on
//So split the vector into batches - and then in each core, execute function on each element of sub vector
//then recombine
pub fn parallel_hashmap<Aux: Clone + Send + Sync, Key: Hash + Clone + Send + Sync + Ord, In: Clone + Send + Sync, Out: Clone + Send + Sync>(map : HashMap<Key,In>, aux: Vec<Aux>, fun : FunAux<In,Out,Aux,Key>) -> HashMap<Key,Out> {
    let mut new_map = HashMap::new();
    let cores:usize = num_cpus::get_physical();
    let keys:Vec<Key> = map.keys().map(|k| k.clone()).collect();
     let max = keys.len();
     let (snd,rcv) = bounded(1);
    let ref_map = &map;
    let ref_aux = &aux;
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let key_batches = &keys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		for (index,key) in key_batches.iter().enumerate(){
		    let mut local_results = Vec::new();
		    let counter = index + next;
		    if(ref_aux.len() > counter){
			local_results.push((key,fun(ref_map.get(key).unwrap().clone(),(key.clone()),ref_aux[index + next].clone())));
		    }
		    else{
			local_results.push((key,fun(ref_map.get(key).unwrap().clone(),(key.clone()),ref_aux[0].clone())));
		    }
		    sen.send(local_results).unwrap();
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		new_map.insert(item.0.clone(),item.1);
	    }
	}
    }).unwrap();
    new_map
}

pub fn parallel_btreemap_noaux<Key: Clone + Send + Sync + Ord, In: Clone + Send + Sync, Out: Clone + Send + Sync>(map : BTreeMap<Key,In>, fun : Func<In,Out>) -> BTreeMap<Key,Out> {
    let mut new_map = BTreeMap::new();
    let cores:usize = num_cpus::get_physical();
    let keys:Vec<Key> = map.keys().map(|k| k.clone()).collect();
     let max = keys.len();
     let (snd,rcv) = bounded(1);
    let ref_map = &map;
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let key_batches = &keys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		for (index,key) in key_batches.iter().enumerate(){
		    let mut local_results = Vec::new();
		    local_results.push((key,fun(ref_map.get(key).unwrap().clone())));
		    sen.send(local_results).unwrap();
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		new_map.insert(item.0.clone(),item.1);
	    }
	}
    }).unwrap();
    new_map
}
pub fn parallel_hashmap_noaux<Key: Clone + Send + Sync + Ord + Hash, In: Clone + Send + Sync, Out: Clone + Send + Sync>(map : HashMap<Key,In>, fun : Func<In,Out>) -> HashMap<Key,Out> {
    let mut new_map = HashMap::new();
    let cores:usize = num_cpus::get_physical();
    let keys:Vec<Key> = map.keys().map(|k| k.clone()).collect();
     let max = keys.len();
     let (snd,rcv) = bounded(1);
    let ref_map = &map;
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let key_batches = &keys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		for (index,key) in key_batches.iter().enumerate(){
		    let mut local_results = Vec::new();
		    local_results.push((key,fun(ref_map.get(key).unwrap().clone())));
		    sen.send(local_results).unwrap();
		}
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		new_map.insert(item.0.clone(),item.1);
	    }
	}
    }).unwrap();
    new_map
}
fn unflatten<K: Copy + Clone + Hash + Eq, F:Copy + Clone + Eq + Hash>(to_unflatten:Vec<F>,interval:usize,keys:Vec<K>) -> HashMap<K,Vec<F>>{
    let mut input_index = 0;
    let mut key_index = 0;
    let mut results = HashMap::new();
    loop{
	if input_index  >= to_unflatten.len(){
	    break;
	}
	let mut temp = Vec::new();
	for i in 0..interval{
	    temp.push(to_unflatten[input_index + i]);
	}
	results.insert(keys[key_index],temp);
	input_index = input_index + interval;
	key_index = key_index + 1;
    }
    assert_eq!(key_index,keys.len());
    results	
}
pub fn parallel_hashmap_flatten<Key: Clone + Debug + Send + Copy + Sync + Ord + Hash, In: Clone + Send + Sync + Copy + Debug, Out: Debug + Copy + Clone + Eq + Hash + Send + Sync>(map : &HashMap<Key,Vec<In>>, fun : VecFunc<In,Out>) -> HashMap<Key,Vec<Out>> {
    let mut new_map = HashMap::new();
    let cores:usize = num_cpus::get_physical();
    let keys:Vec<Key> = map.keys().map(|k| k.clone()).collect();
     let max = keys.len();
     let (snd,rcv) = bounded(1);
    let ref_map = &map;
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);
	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let key_batches = &keys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		let mut elems:Vec<In> = Vec::new();
		for (index,key) in key_batches.iter().enumerate(){
		    let mut temp = ref_map.get(key).unwrap().clone();
		    elems.append(&mut temp);
		    assert_eq!(elems.len() == 0,false);
		}
		if(elems.len() > 0){
		    let local_results = (key_batches,fun(elems.clone()));
		    sen.send(local_results).unwrap();
		}
		
	    });
	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
		let temp_map = unflatten(msg.1,4usize,msg.0.to_vec());
		for(key,val) in temp_map{
		    new_map.insert(key,val);
		}
	}
    }).unwrap();
    new_map
}
fn hashmap_insert<F: PrimeField>(key : F, val: F, hm : &mut HashMap<F,Vec<F>>){
    hm.entry(key).and_modify(|v| { v.push(val) }).or_insert(vec![val]);
}
type VecFunc<In,Out> = fn(Vec<In>) -> Vec<Out>;
//I have a vector of things and a function that accepts a vector of things as input,
//and produces an equally sized vector as output
//I want to split the vector up evenly across cores and execute this function on
//each vector and then recombine
//So split the vector into batches - and then in each core, execute function on each entire sub vector
//then recombine
pub fn parallel_vec_function<In: Clone + Send + Sync, Out: Clone + Send + Sync>(ys : &Vec<In>, fun : VecFunc<In,Out>) -> (Vec<(usize,Out)>) {
     let cores:usize = num_cpus::get_physical();
     let max = ys.len();
     let (snd,rcv) = bounded(1);
    let mut results = Vec::new();
    crossbeam::scope(|s| {
	let mut batch_size = max / (cores);

	let mut next = 0;
	let remainder = max % cores;
	for core in 0..cores{
	    let mut this_batch_size = 0usize;
	    if core < remainder{
		this_batch_size = batch_size + 1;
	    }
	    else{
		this_batch_size = batch_size;
	    }
	    let batches = &ys[next..(next + this_batch_size)]; // 0 to 2
	    let (sen,rec) = (snd.clone(),rcv.clone());
	    //inside ONE core
	    s.spawn(move |_| {
		let local_results:Vec<(usize,Out)> = fun(batches.to_vec()).iter().enumerate().map(|(i,x)| (next + i,x.clone())).collect();
		sen.send(local_results);
	    });

	 next = next + this_batch_size
	}
	drop(snd);
	for msg in rcv.iter(){
	    for item in msg{
		results.push(item);
	    }
	}

    }).unwrap();
    
    results
}

fn test_function<F:PrimeField>(input: F) -> F{
    input * F::from(3u32)
}
fn test_vec_function<F:PrimeField>(inputs:Vec<F>) -> Vec<F>{
    let mut results = Vec::new();
    for i in inputs{
	results.push(i * F::from(3u32));
    }
    results
}
#[test]
fn test_parallel_this(){
    let ys = vec![Fr::one(),Fr::from(2u32), Fr::from(3u32),Fr::one(),Fr::from(2u32), Fr::from(3u32),Fr::from(10u32)];
    let fun:Func<Fr,Fr> = test_function::<Fr>;
    let output = parallel_function::<Fr,Fr>(&ys,fun);
    let mut serial_results = Vec::new();
    for y in ys{
	serial_results.push(y * Fr::from(3u32));
    }
    let mut p_results = vec![Fr::one();7usize];
    for p in output{

	p_results[p.0] = p.1;
    }
    assert_eq!(p_results,serial_results);
}

#[test]
fn test_vec_parallel_this(){
    let ys = vec![Fr::one(),Fr::from(2u32), Fr::from(3u32),Fr::one(),Fr::from(2u32), Fr::from(3u32),Fr::from(10u32)];
    let fun:VecFunc<Fr,Fr> = test_vec_function::<Fr>;
    let output = parallel_vec_function::<Fr,Fr>(&ys,fun);
    let mut p_results = vec![Fr::one();7usize];
    for p in output{
	p_results[p.0] = p.1;
    }
    assert_eq!(p_results,fun(ys));
}
