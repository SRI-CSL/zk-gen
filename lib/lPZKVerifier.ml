open Evocrypt
open ZK
open ZK.LPZK

open Wiztoolkit_load

open Domainslib

let relation_file = ref ""
let instance_file = ref ""

let tasks = ref 32

let timer_recv   = Timer.create "recv"
let timer_input  = Timer.create "inputs"
let timer_random = Timer.create "random"
let timer_prove  = Timer.create "prove"

let decide statement cs plugins =

  let instance      = statement.lpzk_instance in
  let topo, circuit = statement.lpzk_relation in
  let header        = statement.lpzk_header in
  q := header.field_characteristic ;

  Timer.start timer_random;
  Format.printf "Generating verifier randomness...@." ;

  let nrand = Z.to_int (Z.(topo.npinputs + topo.nsinputs + topo.ngates)) in
  let rv = Evocrypt.Random.LPZK.generate_lpzk_verifier_randomness nrand in
  Timer.transfer timer_random timer_prove;
  Format.printf "Randomness generated in %f ms.@." (Timer.read timer_random *. 1000.) ;
  Format.printf "Checking proof...@." ;

  let pool = Task.setup_pool ~num_domains:(!tasks-1) () in
  let n    = Array.length cs in
  let jobs = Array.make n [] in
  let _chunk_size = Utils.create_jobs_for circuit jobs in

  let aux job cs =
    let cs = Marshal.from_bytes cs 0 in
    List.fold_left2 (fun b gg ci -> prove rv ((topo, gg), instance) ci && b) true job cs
  in

  let multitask () =
    Task.parallel_for_reduce ~start:0 ~finish:(n-1)
      ~body:(fun i -> aux (jobs.(i)) (cs.(i))) pool (&&) true;
  in

  let final = Task.run pool multitask in

  Timer.stop timer_prove;  
  Format.printf "Proof checked in %f ms.@." (Timer.read timer_prove *. 1000.);
  Format.printf "Decision = %s@." (if final then "TRUE" else "FALSE");
  Task.teardown_pool pool

let handle_service ic oc =
  let send json =
    let json = json |> Yojson.Safe.to_string in
    output_string oc (json^"\n") ;
    flush oc
  in
  try

    let _ = input_line ic in

    Timer.start timer_input;
    Format.printf "Parsing relation, instance files...@." ;
    let statement, witness, nmul, plugins, max_id = Wiztoolkit_load.parse_files_lpzk [!relation_file; !instance_file] in
    Timer.stop timer_input;
    Format.printf "Relation and instance (%i multiplications) parsed in %f ms.@."
      nmul
      (Timer.read timer_input *. 1000.) ;
    let instance      = statement.lpzk_instance in
    let topo, circuit = statement.lpzk_relation in
    let header        = statement.lpzk_header in
    LPZK.q := header.field_characteristic ;
    Format.printf "Field size: %s@." (Z.to_string !LPZK.q) ;

    Format.printf "Notifying the prover that I am ready...@." ;
    `Assoc [("action", `String "start")] |> send;
    
    let json = input_line ic |> Yojson.Safe.from_string in

    Timer.start timer_recv;
    Format.printf "Receiving commitment from prover.@." ;
    let n = json |> Yojson.Safe.Util.member "data" |> Utils.json_to_int in
    let commitment = Array.make n Bytes.empty in
    for i = 0 to n-1 do
      let s = input_line ic in
      let l = s |> Yojson.Safe.from_string |> Utils.json_to_int in
      Utils.print "receive" 1 "Receiving %i bytes.@." l;
      let bytes = Bytes.make l '0' in
      really_input ic bytes 0 l;
      commitment.(i) <- bytes
    done;
    Timer.stop timer_recv;
    Format.printf "Commitment message parsed in %f ms.@."
      ((Timer.read timer_recv) *. 1000.) ;

    decide statement commitment plugins;
    `Assoc [("action", `String "done")] |> send;
    let _ = input_line ic in
    ()
    
  with
  | End_of_file -> exit 0
  | e ->
     Printf.printf "End of text\n" ;
     raise e 

let establish_server server_fun sockaddr =
  let domain = Unix.domain_of_sockaddr sockaddr in
  let sock = Unix.socket domain Unix.SOCK_STREAM 0 in
  Unix.bind sock sockaddr ;
  Unix.listen sock 3;
  let s, _caller = Unix.accept sock in
  let inchan = Unix.in_channel_of_descr s in
  let outchan = Unix.out_channel_of_descr s in
  server_fun inchan outchan ;
  close_in inchan ;
  close_out outchan ;
  Unix.close s    
       
let main_server serv_fun port rel inst cores =
  try
    let port = port in
    
    relation_file := rel ;
    instance_file := inst ;
    tasks := cores ;

    Format.printf "Files:@." ;
    Format.printf "\tRelation file: %s@." !relation_file ;
    Format.printf "\tInstance file: %s@." !instance_file ;

    Format.printf "Waiting for the prover boot...@." ;
          
    let my_address = Unix.inet_addr_any in
    establish_server serv_fun (Unix.ADDR_INET(my_address, port)) 
  with
  | Sys.Break -> exit 0       
  | Failure "int_of_string" -> 
      Printf.eprintf "serv_up : bad port number\n"
  | Not_found -> Printf.eprintf "what?\n"

let lpzk_verifier_exec port rel inst cores =
  Unix.handle_unix_error main_server handle_service port rel inst cores