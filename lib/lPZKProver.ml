open Evocrypt
open ZK
open ZK.LPZK

open Wiztoolkit_load

open Domainslib

let relation_file = ref ""
let instance_file = ref ""
let witness_file = ref ""

let pad_witness l ws = 
  let pad = Array.make (Z.to_int l) Z.zero in
  Array.append pad ws

let tasks = ref 32

let timer_send   = Timer.create "send"
let timer_input  = Timer.create "inputs"
let timer_random = Timer.create "random"
let timer_commit = Timer.create "commit"

let commitment_msg () =

  Timer.start timer_input;

  Format.printf "Parsing relation, instance and witness files...@." ;
  let statement, witness, nmul, plugins, max_id =
    Wiztoolkit_load.parse_files_lpzk [!relation_file; !instance_file; !witness_file]
  in
  let instance      = statement.lpzk_instance in
  let topo, circuit = statement.lpzk_relation in
  let header        = statement.lpzk_header in
  LPZK.q := header.field_characteristic ;
  
  let witness = pad_witness topo.npinputs witness in

  Timer.transfer timer_input timer_random;
  Format.printf "Relation, instance and witness (%i multiplications) parsed in %f ms.@."
    nmul
    (Timer.read timer_input *. 1000.) ;
  Format.printf "Field size: %s@." (Z.to_string !q) ;
  Format.printf "Generating prover randomness...@." ;

  let nrand = Z.to_int (Z.(topo.npinputs + topo.nsinputs + topo.ngates)) in
  let prover_rand = Evocrypt.Random.LPZK.generate_lpzk_prover_randomness nrand in

  Timer.transfer timer_random timer_commit;
  Format.printf "Prover randomness generated in %f ms@." (Timer.read timer_random *. 1000.);
  Format.printf "Producing commitment message...@." ;

  tasks := if Array.mem "iter_v0" plugins then !tasks else 1 ;
  let pool        = Task.setup_pool ~num_domains:(!tasks-1) () in
  let jobs        = Array.make !tasks [] in
  let _chunk_size = Utils.create_jobs_for circuit jobs in
  let treat1gate gg = LPZK.commit prover_rand (witness, ((topo, gg), instance)) in
  let aux i job =
    Utils.print "commit" 1 "@,@[Task %i starting@]@]%!@[<v>" i;
    let chunk = List.map treat1gate job in
    Marshal.to_bytes chunk []
  in

  let results = List.init !tasks (fun i -> Task.async pool (fun () -> aux i jobs.(i))) in

  (* While we wait we might as well compute this: *)
  let commitment_msg = `Assoc [("action", `String "commitment") ; ("data", `Int !tasks)] in

  let c = Task.run pool (fun () -> List.map (Task.await pool) results) in

  Timer.stop timer_commit;
  (*Format.printf "nmuls = %d@." (!LPZK.nmuls) ;*)
  Format.printf "Commitment message generated in %f ms@." (Timer.read timer_commit *. 1000.);

  commitment_msg,c

exception Protocol of string

let client_fun ic oc =
  let send json =
    let json = json |> Yojson.Safe.to_string in
    output_string oc (json^"\n") ;
    flush oc
  in
  `Assoc [("action", `String "ready")] |> send;
  let pmsg, cs = commitment_msg () in
  try
    let _ = input_line ic in
    send pmsg;
    let aux s =
      let l = Bytes.length s in
      Utils.print "send" 1 "Sending %i bytes\n" l;
      (* Format.printf "Hash %i\n" (s |> Bytes.to_string |> String.hash); *)
      `Int l |> send;
      output_bytes oc s;
      flush oc
    in
    Timer.start timer_send;
    List.iter aux cs;
    Timer.stop timer_send;
    Format.printf "Sending message in %f ms@." (Timer.read timer_send *. 1000.);

    let _ = input_line ic in
    Format.printf "Finalizing LPZK protocol...@."
  with 
  | Exit -> exit 0
  | End_of_file -> exit 0
  | exn -> Format.printf "%s@." (Printexc.to_string exn) ;
           Unix.shutdown_connection ic

let main_client client_fun verip verport rel inst wit cores =
  let server = verip in
  let server_addr =
    try Unix.inet_addr_of_string server 
    with Failure "inet_addr_of_string" -> 
      try (Unix.gethostbyname server).Unix.h_addr_list.(0) 
      with Not_found ->
        Printf.eprintf "%s : Unknown server\n" server ;
        exit 2
  in try 
    let port = verport in
    let sockaddr = Unix.ADDR_INET(server_addr,port) in

    Format.printf "Files:@." ;
    
    relation_file := rel ;
    instance_file := inst ;
    witness_file  := wit ;
    tasks := cores ;

    Format.printf "\tRelation file: %s@." !relation_file ;
    Format.printf "\tInstance file: %s@." !instance_file ;
    Format.printf "\tRelation file: %s@." !witness_file ;

    let ic,oc = Unix.open_connection sockaddr in
    client_fun ic oc ;
    (* close_in ic ; *)
    (* close_out oc ; *)
    Unix.shutdown_connection ic
  with Failure "int_of_string" ->
    Printf.eprintf "bad port number";
    exit 2

let lpzk_prover_exec verip verport rel inst wit cores =
  main_client client_fun verip verport rel inst wit cores

(*let () = Arg.parse Tracing.options (fun s -> Utils.args := s::!Utils.args) "Prover"
let () = Tracing.compile();;*)