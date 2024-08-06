open Containers

let size = fun x -> Z.of_int (Array.length x)

let z_array_to_string (rp : Z.t Array.t) : string =
  let s = ref "" in
  for i = 0 to Z.to_int (size rp) - 1 do
    s := !s ^ Z.to_string (rp.(i)) ^ ", " ;
  done ;
  !s

let print s i = Tracing.print Format.stdout s i

let args : string list ref = ref [] (* Where the command-line argument will be stacked *)

let parse_val s =
  let colon_split = String.split_on_char ':' s in
  let s = List.nth colon_split 1 in
  let comma_split = String.split_on_char ',' s in
  let s = List.nth comma_split 0 in
  let aspas_split = String.split_on_char '\"' s in
  Z.of_string (List.nth aspas_split 1)

let read_val ic =
  let line = input_line ic in
  parse_val line, ic

let create_jobs_for circ job_array =
  let nb_outputs = List.length circ in
  let n = Array.length job_array in
  let gates_per_job = nb_outputs / n in
  print "create_jobs" 1
    "@,@[%i output wires for %i jobs makes %i output wires per job@]@,"
    nb_outputs n gates_per_job;
  let () = if gates_per_job <= 0 then
             job_array.(0) <- circ
           else
             let circ = ref circ in
             for i = 0 to n-1 do
               let out, rest = List.take_drop gates_per_job !circ in
               job_array.(i) <- out;
               circ := rest
             done
  in
  gates_per_job

open Evocrypt.EcLib
open EcList

let rec pad_witness' l i ws =
  if Z.equal i l then ws
  else pad_witness' l (Z.add i Z.one) (concat (Cons (EcOption.witness, Nil)) ws)
  
let pad_witness l ws = pad_witness' l Z.zero ws

let array_to_eclist v =
  let ecl = ref Nil in
  for i = 0 to Array.length v - 1 do
    ecl := Cons(v.(i), !ecl) ;
  done;
  !ecl  

module JSON = Yojson.Safe

exception BadJSON of string

let bad json s = raise (BadJSON(JSON.to_string json^" should be a "^s))

let json_to_string : JSON.t -> String.t = function
  | `String s -> s
  | json -> bad json "string"

let json_to_int : JSON.t -> int = function
  | `Int s -> s
  | json -> bad json "int"

let json_to_Z : JSON.t -> Z.t = function
  | `Int s -> Z.of_int s
  | `Intlit s -> Z.of_string s
  | json -> bad json "int"

let json_to_dico : JSON.t -> (String.t * JSON.t) List.t = function
  | `Assoc s -> s
  | json -> bad json "dictionary"

let json_to_list : JSON.t -> JSON.t List.t = function
  | `List s -> s
  | json -> bad json "list"

let json_to_array : JSON.t -> JSON.t Array.t = function
  | `List s -> Array.of_list s
  | json -> bad json "list"