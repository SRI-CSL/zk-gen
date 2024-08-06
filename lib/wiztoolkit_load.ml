open Ctypes_zarith
open Containers

open Evocrypt
open ZK
open LPZK
open EcLib

module Header = struct

  type z = Z.t [@@deriving eq]
  let pp_z = Z.pp_print
  
  type t = {
      version : string;
      profile : string;
      field_characteristic : z;
      field_degree : int
    } [@@deriving eq, show]
  end

type lpzk_statement = {
  lpzk_header : Header.t;
  lpzk_relation : topology_t * gates_t list;
  lpzk_instance : Z.t array }

type mith_statement = {
  mith_header : Header.t;
  mith_relation : topology_t * Circuit.ArithmeticCircuit.ArithmeticGates.gates_t ;
  mith_instance : Z.t array }

let gate_type_to_string = function
  | `assign -> "assign"
  | `copy -> "copy"
  | `add -> "add"
  | `mul -> "mul"
  | `addc -> "addc"
  | `mulc -> "mulc"
  | `publicIn -> "instance"
  | `privateIn -> "witness"
  | `assertZero -> "assertZero"

let c_gate_get_gid x = Wiztoolkit.Bindings.gate_value (Ctypes.(!@) (Wiztoolkit.Bindings.get_driver x)) 

let c_gate_to_string g =
  let typ = Wiztoolkit.Bindings.gate_type g in
  let wl = Wiztoolkit.Bindings.gate_left g in
  let wr = Wiztoolkit.Bindings.gate_right g in
  Format.sprintf "%s(%s, %s)@." (gate_type_to_string typ) (Z.to_string (c_gate_get_gid wl)) (Z.to_string (c_gate_get_gid wr))

let c_gates_to_mith_gates wire_gate_index inst_start wit_start gate_start ngates gates = 

  let witness_index  = ref wit_start in
  let witness_count  = ref wit_start in
  let instance_index = ref inst_start in
  let instance_count = ref inst_start in
  let gate_index    = ref gate_start in
  let mul_index      = ref 0 in
  let output_wires = ref [] in

  let read id =
    try 
      let g = Hashtbl.find wire_gate_index id in
      if Circuit.ArithmeticCircuit.ArithmeticGates.is_sinput g then witness_count := Z.succ !witness_count;
      if Circuit.ArithmeticCircuit.ArithmeticGates.is_pinput g then instance_count := Z.succ !instance_count;
      g
    with Not_found -> Circuit.ArithmeticCircuit.ArithmeticGates.SInput id
  in
  let write id g = Hashtbl.replace wire_gate_index id g in

  let parse g = 
    match Wiztoolkit.Bindings.gate_type g with
    | `privateIn -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let value = Wiztoolkit.Bindings.gate_value g in 
      let w = !witness_index in
      witness_index := Z.succ !witness_index;
      witness_count := Z.succ !witness_count;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.SInput w) 

    | `publicIn -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let w = !instance_index in
      instance_index := Z.succ !instance_index;
      instance_count := Z.succ !instance_count;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.PInput w) 

    | `copy -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let source = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      write out (read source)
    
    | `assign ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let w = !gate_index in
      gate_index := Z.succ !gate_index;
      let const = Wiztoolkit.Bindings.gate_value g in
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.Constant(w, const))
    
    | `mul ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let wr = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_right g)) in
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      mul_index  := !mul_index + 1;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.Multiplication(w, read wl, read wr))

    | `mulc ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in

      let const = Wiztoolkit.Bindings.gate_value g in
      let w_const = !gate_index in
      gate_index := Z.succ !gate_index; 
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.Multiplication(w, read wl, Circuit.ArithmeticCircuit.ArithmeticGates.Constant(w_const, const))) 

    | `add ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64(Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let wr = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_right g)) in
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      mul_index  := !mul_index + 1;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.Addition(w, read wl, read wr))

    | `addc ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let const = Wiztoolkit.Bindings.gate_value g in
      let w_const = !gate_index in
      gate_index := Z.succ !gate_index;
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      write out (Circuit.ArithmeticCircuit.ArithmeticGates.Addition(w, read wl, Circuit.ArithmeticCircuit.ArithmeticGates.Constant(w_const, const)))

    | `assertZero ->
      let w = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      gate_index := Z.succ !gate_index;
      output_wires := w :: !output_wires;
  in

  let aux ngates gates = 
    for i = 0 to ngates - 1 do
      parse (Ctypes.(!@) (Ctypes.(+@) gates i)) ;
    done;
    !output_wires
  in

  let rec join_out_wires = function
  | [] -> Circuit.ArithmeticCircuit.ArithmeticGates.Constant(!gate_index, Z.zero)
  | [x] -> read x
  | x :: xs -> 
      let w = !gate_index in
      gate_index := Z.succ !gate_index; 
      Circuit.ArithmeticCircuit.ArithmeticGates.Addition(w, read x, join_out_wires xs)
  in

  let out_wires = aux ngates gates in

  Z.sub !instance_index inst_start,
  Z.sub !witness_index wit_start,
  Z.add (Z.sub !gate_index gate_start) (Z.of_int (List.length out_wires)),
  !mul_index,
  join_out_wires out_wires,
  !gate_index,
  !witness_count,
  !instance_count

let c_gates_to_lpzk_gates wire_gate_index inst_start wit_start gate_start ngates gates = 

  let witness_index  = ref wit_start in
  let witness_count  = ref wit_start in
  let instance_index = ref inst_start in
  let instance_count = ref inst_start in
  let gate_index    = ref gate_start in
  let mul_index      = ref 0 in
  let output_wires = ref [] in

  let read id =
    try 
      let g = Hashtbl.find wire_gate_index id in
      if is_sinput g then witness_count := Z.succ !witness_count;
      if is_pinput g then instance_count := Z.succ !instance_count;
      g
    with Not_found -> SInput id
  in
  let write id g = Hashtbl.replace wire_gate_index id g in

  let parse g = 
    match Wiztoolkit.Bindings.gate_type g with
    | `privateIn -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let value = Wiztoolkit.Bindings.gate_value g in 
      let w = !witness_index in
      witness_index := Z.succ !witness_index;
      witness_count := Z.succ !witness_count;
      write out (SInput w) 

    | `publicIn -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let w = !instance_index in
      instance_index := Z.succ !instance_index;
      instance_count := Z.succ !instance_count;
      write out (PInput w) 

    | `copy -> 
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let source = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      write out (read source)
    
    | `assign ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let w = !gate_index in
      gate_index := Z.succ !gate_index;
      let const = Wiztoolkit.Bindings.gate_value g in
      write out (Constant(w, const))
    
    | `mul ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let wr = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_right g)) in
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      mul_index  := !mul_index + 1;
      write out (Multiplication(w, read wl, read wr))

    | `mulc ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in

      let const = Wiztoolkit.Bindings.gate_value g in
      let w_const = !gate_index in
      gate_index := Z.succ !gate_index; 
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      write out (Multiplication(w, read wl, Constant(w_const, const))) 

    | `add ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64(Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let wr = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_right g)) in
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      mul_index  := !mul_index + 1;
      write out (Addition(w, read wl, read wr))

    | `addc ->
      let out = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_out g)) in
      let wl = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      let const = Wiztoolkit.Bindings.gate_value g in
      let w_const = !gate_index in
      gate_index := Z.succ !gate_index;
      let w  = !gate_index in
      gate_index := Z.succ !gate_index;
      write out (Addition(w, read wl, Constant(w_const, const)))

    | `assertZero ->
      let w = Z.of_int64 (Unsigned.ULong.to_int64 (Wiztoolkit.Bindings.gate_left g)) in
      gate_index := Z.succ !gate_index;
      output_wires := w :: !output_wires;
  in

  let rec aux ngates gates = 
    for i = 0 to ngates - 1 do
      parse (Ctypes.(!@) (Ctypes.(+@) gates i)) ;
    done;
    !output_wires
  in

  let out_wires = aux ngates gates in

  Z.sub !instance_index inst_start,
  Z.sub !witness_index wit_start,
  Z.add (Z.sub !gate_index gate_start) (Z.of_int (List.length out_wires)),
  !mul_index,
  List.map read out_wires,
  !gate_index,
  !witness_count,
  !instance_count

let count_nsinputs noutputs outputs = 

  let witness_count  = ref 0 in
  let visited = ref [] in

  let rec aux x = 
    let g_ptr = Wiztoolkit.Bindings.get_driver x in
    let g = Ctypes.(!@) g_ptr  in
  
    match Wiztoolkit.Bindings.gate_type g with
    | `privateIn -> if List.mem g !visited then 0 else begin visited := g :: !visited ; 1 end
    | `publicIn -> 0
    | `copy -> aux (Wiztoolkit.Bindings.gate_left g)
    | `assign -> 0
    | `mul -> aux (Wiztoolkit.Bindings.gate_left g) + aux (Wiztoolkit.Bindings.gate_right g)
    | `mulc -> aux (Wiztoolkit.Bindings.gate_left g)
    | `add -> aux (Wiztoolkit.Bindings.gate_left g) + aux (Wiztoolkit.Bindings.gate_right g)
    | `addc -> aux (Wiztoolkit.Bindings.gate_left g)
  in

  for i = 0 to noutputs - 1 do 
    witness_count := !witness_count + aux (Ctypes.(!@) (Ctypes.(+@) outputs i)) 
  done;

  !witness_count

let rec lpzk_gates_to_string pad = function
  | PInput wid -> pad ^ "PInput(" ^ Z.to_string wid ^ ")"
  | SInput wid -> pad ^ "SInput(" ^ Z.to_string wid ^ ")"
  | Constant (gid, const) -> pad ^ "Constant(" ^ Z.to_string gid ^ ", " ^ Z.to_string const ^ ")"
  | Addition (gid, wl, wr) -> pad ^ "Addition(" ^ Z.to_string gid ^ ",\n" ^ lpzk_gates_to_string (pad^"\t") wl ^ ",\n" ^ lpzk_gates_to_string (pad^"\t") wr ^ ")"
  | Multiplication (gid, wl, wr) -> pad ^ "Multiplication(" ^ Z.to_string gid ^ ",\n" ^ lpzk_gates_to_string (pad^"\t") wl ^ ",\n" ^ lpzk_gates_to_string (pad^"\t") wr ^ ")"
 
let mpz_ptr_to_z_array size ptr = 
  let ret = Array.make size Z.zero in
  for i = 0 to size-1 do
    ret.(i) <- MPZ.to_z (Ctypes.addr (Ctypes.(!@) (Ctypes.(+@) ptr i))) 
  done;
  ret

let string_ptr_to_string_array size ptr = 
  let ret = Array.make size "" in
  for i = 0 to size-1 do
    ret.(i) <- Ctypes.(!@) (Ctypes.(+@) ptr i)
  done;
  ret

let z_array_to_string size arr = 
  let ret = ref "[" in
  for i = 0 to size-2 do
    ret := !ret ^ Z.to_string arr.(i) ^"; "
  done;
  !ret ^ Z.to_string arr.(size-1) ^"]"

let rec count_gates = function
  | PInput w -> 0
  | SInput w -> 0
  | Constant (gid, c) -> 1
  | Addition (gid, wl, wr) -> 1 + count_gates wl + count_gates wr
  | Multiplication (gid, wl, wr) -> 1 + count_gates wl + count_gates wr

let rec count_muls = function
  | PInput w -> 0
  | SInput w -> 0
  | Constant (gid, c) -> 0
  | Addition (gid, wl, wr) -> count_muls wl + count_muls wr
  | Multiplication (gid, wl, wr) -> 1 + count_muls wl + count_muls wr

let rec treat = function
  | [dir] ->
     let files = Sys.readdir dir |> Array.to_list in
     let filter suffix =
       let regexp = ".*\\."^suffix |> Str.regexp in
       let test filename = Str.string_match regexp filename 0 in
       List.filter test files
     in
     let path filename = Filename.(concat dir filename) in
     begin
     match filter "wit", filter "ins", filter "rel" with
     | [witness], [instance], [relation] -> treat [path witness; path instance; path relation]
     | _ -> failwith "Directory does not contain 1 file *.rel, 1 file *.ins, 1 file *.wit exactly."
     end
  | [witness; instance; relation] ->
     (
      if Wiztoolkit.Bindings.load_file relation instance witness
      then print_endline "SUCCESS"
      else print_endline "FAILURE"
     )
  | [instance; relation] ->
    (
      if Wiztoolkit.Bindings.load_file relation instance ""
      then print_endline "SUCCESS"
      else print_endline "FAILURE"
    )
  | _ -> print_endline "error reading files"

let timer_parsing_cpp = Timer.create "parsing_cpp"
let timer_parsing_ocaml = Timer.create "parsing_ocaml"

let parse_files_lpzk_prover l = 
  Timer.start timer_parsing_cpp;
  let parsing = treat l in
  Timer.transfer timer_parsing_cpp timer_parsing_ocaml;

  let nrPrimes = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let primes_ptr = Wiztoolkit.Bindings.get_primes nrPrimes in

  let version = "2.0.0-beta" in
  let profile = "" in
  let field_characteristic = MPZ.to_z (Ctypes.addr (Ctypes.(!@) (Ctypes.(+@) primes_ptr 0))) in
  let field_degree = 1 in
  let header = Header.{ version; profile; field_characteristic; field_degree } in

  let nsinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let witness_ptr = Wiztoolkit.Bindings.get_private_inputs nsinputs_ptr in
  let nsinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) nsinputs_ptr)) in
  let witness = mpz_ptr_to_z_array (Z.to_int nsinputs) witness_ptr in

  let npinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let instance_ptr = Wiztoolkit.Bindings.get_public_inputs npinputs_ptr in
  let npinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) npinputs_ptr)) in
  let instance = mpz_ptr_to_z_array (Z.to_int npinputs) instance_ptr in

  let nrGates_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let gates = Wiztoolkit.Bindings.get_gates nrGates_ptr in
  let nrGates = Unsigned.UInt64.to_int (Ctypes.(!@) nrGates_ptr) in
  let wire_gate_index = Hashtbl.create ~random:true 1000 in

  let npinputs, nsinputs, ngates, nmul, gg, max_id, wit_count, inst_count = c_gates_to_lpzk_gates wire_gate_index Z.zero npinputs (Z.add npinputs nsinputs) nrGates gates in

  let nrPlugins_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let plugins_ptr = Wiztoolkit.Bindings.get_plugins nrPlugins_ptr in
  let nrPlugins = Unsigned.UInt64.to_int (Ctypes.(!@) nrPlugins_ptr) in
  let plugins = string_ptr_to_string_array nrPlugins plugins_ptr in

  Timer.stop timer_parsing_ocaml;
  Format.printf "Time for core parsing is: C %f ms, OCaml %f ms, Total %f ms.\n" (Timer.read timer_parsing_cpp *. 1000.) (Timer.read timer_parsing_ocaml *. 1000.) (Timer.read timer_parsing_cpp +. Timer.read timer_parsing_ocaml *. 1000.);

  let topology = {
    npinputs = npinputs ;
    nsinputs = nsinputs ;
    noutputs = Z.of_int (List.length gg) ;
    ngates = ngates }
  in
  
  let relation = topology, gg in
  { lpzk_header = header; lpzk_relation = relation; lpzk_instance = instance }, witness, nmul, plugins, max_id

let parse_files_lpzk_verifier l = 
  Timer.start timer_parsing_cpp;
  let parsing = treat l in
  Timer.transfer timer_parsing_cpp timer_parsing_ocaml;

  let nrPrimes = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let primes_ptr = Wiztoolkit.Bindings.get_primes nrPrimes in

  let version = "2.0.0-beta" in
  let profile = "" in
  let field_characteristic = MPZ.to_z (Ctypes.addr (Ctypes.(!@) (Ctypes.(+@) primes_ptr 0))) in
  let field_degree = 1 in
  let header = Header.{ version; profile; field_characteristic; field_degree } in

  let nsinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let witness_ptr = Wiztoolkit.Bindings.get_private_inputs nsinputs_ptr in
  let nsinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) nsinputs_ptr)) in

  let npinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let instance_ptr = Wiztoolkit.Bindings.get_public_inputs npinputs_ptr in
  let npinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) npinputs_ptr)) in
  let instance = mpz_ptr_to_z_array (Z.to_int npinputs) instance_ptr in

  let nrGates_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let gates = Wiztoolkit.Bindings.get_gates nrGates_ptr in
  let nrGates = Unsigned.UInt64.to_int (Ctypes.(!@) nrGates_ptr) in
  let wire_gate_index = Hashtbl.create ~random:true 1000 in

  let npinputs, nsinputs, ngates, nmul, gg, max_id, wit_count, inst_count = c_gates_to_lpzk_gates wire_gate_index Z.zero npinputs (Z.add npinputs nsinputs) nrGates gates in

  let nrPlugins_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let plugins_ptr = Wiztoolkit.Bindings.get_plugins nrPlugins_ptr in
  let nrPlugins = Unsigned.UInt64.to_int (Ctypes.(!@) nrPlugins_ptr) in
  let plugins = string_ptr_to_string_array nrPlugins plugins_ptr in

  Timer.stop timer_parsing_ocaml;
  Format.printf "Time for core parsing is: C %f ms, OCaml %f ms, Total %f ms.\n" (Timer.read timer_parsing_cpp *. 1000.) (Timer.read timer_parsing_ocaml*. 1000.) (Timer.read timer_parsing_cpp +. Timer.read timer_parsing_ocaml *. 1000.);

  let topology = {
    npinputs = npinputs ;
    nsinputs = nsinputs ;
    noutputs = Z.of_int (List.length gg) ;
    ngates = ngates }
  in
  
  let relation = topology, gg in
  { lpzk_header = header; lpzk_relation = relation; lpzk_instance = instance }, (Obj.magic None), nmul, plugins, max_id

let parse_files_lpzk l =
  if List.length l = 3 then parse_files_lpzk_prover l
  else parse_files_lpzk_verifier l

let parse_files_mith_prover l = 
  Timer.start timer_parsing_cpp;
  let parsing = treat l in
  Timer.transfer timer_parsing_cpp timer_parsing_ocaml;

  let nrPrimes = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let primes_ptr = Wiztoolkit.Bindings.get_primes nrPrimes in

  let version = "2.0.0-beta" in
  let profile = "" in
  let field_characteristic = MPZ.to_z (Ctypes.addr (Ctypes.(!@) (Ctypes.(+@) primes_ptr 0))) in
  let field_degree = 1 in
  let header = Header.{ version; profile; field_characteristic; field_degree } in

  let nsinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let witness_ptr = Wiztoolkit.Bindings.get_private_inputs nsinputs_ptr in
  let nsinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) nsinputs_ptr)) in
  let witness = mpz_ptr_to_z_array (Z.to_int nsinputs) witness_ptr in

  let npinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let instance_ptr = Wiztoolkit.Bindings.get_public_inputs npinputs_ptr in
  let npinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) npinputs_ptr)) in
  let instance = mpz_ptr_to_z_array (Z.to_int npinputs) instance_ptr in

  let nrGates_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let gates = Wiztoolkit.Bindings.get_gates nrGates_ptr in
  let nrGates = Unsigned.UInt64.to_int (Ctypes.(!@) nrGates_ptr) in
  let wire_gate_index = Hashtbl.create ~random:true 1000 in

  let npinputs, nsinputs, ngates, nmul, gg, max_id, wit_count, inst_count = c_gates_to_mith_gates wire_gate_index Z.zero npinputs (Z.add npinputs nsinputs) nrGates gates in

  let nrPlugins_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let plugins_ptr = Wiztoolkit.Bindings.get_plugins nrPlugins_ptr in
  let nrPlugins = Unsigned.UInt64.to_int (Ctypes.(!@) nrPlugins_ptr) in
  let plugins = string_ptr_to_string_array nrPlugins plugins_ptr in

  Timer.stop timer_parsing_ocaml;
  Format.printf "Time for core parsing is: C %f ms, OCaml %f ms, Total %f ms.\n" (Timer.read timer_parsing_cpp *. 1000.) (Timer.read timer_parsing_ocaml *. 1000.) (Timer.read timer_parsing_cpp +. Timer.read timer_parsing_ocaml *. 1000.);

  let topology = {
    npinputs = npinputs ;
    nsinputs = nsinputs ;
    noutputs = Z.one ;
    ngates = ngates }
  in
  
  let relation = topology, gg in
  { mith_header = header; mith_relation = relation; mith_instance = instance }, witness, nmul, plugins, max_id

let parse_files_mith_verifier l = 
  Timer.start timer_parsing_cpp;
  let parsing = treat l in
  Timer.transfer timer_parsing_cpp timer_parsing_ocaml;

  let nrPrimes = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let primes_ptr = Wiztoolkit.Bindings.get_primes nrPrimes in

  let version = "2.0.0-beta" in
  let profile = "" in
  let field_characteristic = MPZ.to_z (Ctypes.addr (Ctypes.(!@) (Ctypes.(+@) primes_ptr 0))) in
  let field_degree = 1 in
  let header = Header.{ version; profile; field_characteristic; field_degree } in

  let nsinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let witness_ptr = Wiztoolkit.Bindings.get_private_inputs nsinputs_ptr in
  let nsinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) nsinputs_ptr)) in

  let npinputs_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let instance_ptr = Wiztoolkit.Bindings.get_public_inputs npinputs_ptr in
  let npinputs = Z.of_int (Unsigned.UInt64.to_int (Ctypes.(!@) npinputs_ptr)) in
  let instance = mpz_ptr_to_z_array (Z.to_int npinputs) instance_ptr in

  let nrGates_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let gates = Wiztoolkit.Bindings.get_gates nrGates_ptr in
  let nrGates = Unsigned.UInt64.to_int (Ctypes.(!@) nrGates_ptr) in
  let wire_gate_index = Hashtbl.create ~random:true 1000 in

  let npinputs, nsinputs, ngates, nmul, gg, max_id, wit_count, inst_count = c_gates_to_mith_gates wire_gate_index Z.zero npinputs (Z.add npinputs nsinputs) nrGates gates in

  let nrPlugins_ptr = Ctypes.allocate Ctypes.uint64_t Unsigned.UInt64.one in
  let plugins_ptr = Wiztoolkit.Bindings.get_plugins nrPlugins_ptr in
  let nrPlugins = Unsigned.UInt64.to_int (Ctypes.(!@) nrPlugins_ptr) in
  let plugins = string_ptr_to_string_array nrPlugins plugins_ptr in

  Timer.stop timer_parsing_ocaml;
  Format.printf "Time for core parsing is: C %f ms, OCaml %f ms, Total %f ms.\n" (Timer.read timer_parsing_cpp *. 1000.) (Timer.read timer_parsing_ocaml*. 1000.) (Timer.read timer_parsing_cpp +. Timer.read timer_parsing_ocaml *. 1000.);

  let topology = {
    npinputs = npinputs ;
    nsinputs = nsinputs ;
    noutputs = Z.one ;
    ngates = ngates }
  in
  
  let relation = topology, gg in
  { mith_header = header; mith_relation = relation; mith_instance = instance }, (Obj.magic None), nmul, plugins, max_id

let parse_files_mith l =
  if List.length l = 3 then parse_files_mith_prover l
  else parse_files_mith_verifier l