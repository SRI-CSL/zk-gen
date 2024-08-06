open Format

open Evocrypt

open EcLib
open EcOption
open EcList
open EcPrimeField

open ZK.ShamirBGWSha3MitH
open Zarith.FieldPolynomial
open SecretSharing.Shamir
open MPC.BGW.BGWAddition
open MPC.BGW.BGWMultiplication
open MPC.BGW.BGWSMultiplication
open MPC.BGW.BGWRefresh
open MPC.BGW.BGWProtocol
open MPC.ArithmeticProtocol

type pid_mpc_t = Z.t

let p1 = ref (Z.of_string "1")
let p2 = ref (Z.of_string "2")
let p3 = ref (Z.of_string "3")
let p4 = ref (Z.of_string "4")
let p5 = ref (Z.of_string "5")

let pid_mpc_set : pid_mpc_t list = Cons (!p1, Cons (!p2, Cons (!p3, Cons (!p4, Cons (!p5, Nil)))))

module PC5 = struct
  let n = Z.of_string "5"
  let t = Z.of_string "2"
  type pid_t = pid_mpc_t
  let pid_set = pid_mpc_set
end

module Shamir = Shamir (PC5)
module BGWAdd = BGWAdditionGate (PC5)
module BGWMul = BGWMultiplicationGate (PC5)
module BGWSMul = BGWSMultiplicationGate (PC5)
module BGWRefresh = BGWRefreshGate (PC5)

module BGWData = ArithmeticProtocolData (ShamirData (PC5)) (BGWAdditionData (PC5)) (BGWMultiplicationData (PC5)) (BGWSMultiplicationData (PC5))

module ShamirBGW5Sha3MitH = ShamirBGWSha3MitHData (PC5)

(** 
    the following three references allow us to avoid having to reload the circuit in
    order to build the Maurer protocol MitH OCaml module
 *)
(** keeping a reference to the circuit gates *)
let gg_ref = ref witness
(** keeping a reference to the number of public inputs *)
let npinputs_ref = ref Z.zero
(** keeping a reference to the number of secret inputs *)
let nsinputs_ref = ref Z.zero
(** keeping a reference to the number of inputs *)
let ninputs_ref = ref Z.zero
(** keeping a reference to the number of gates *)
let ngates_ref = ref Z.zero
(** keeping a reference to the instance *)
let instance_ref = ref Nil

(** keeping a global reference of the circuit file *)
let relation_file = ref ""
let witness_file = ref ""
let instance_file = ref ""

let circuit_ref = ref ((Z.zero, Z.zero, Z.zero, Z.zero), witness) ;;

let challenge_to_json chl =
  let (i,j) = chl in
  `Assoc [("action", `String "challenge"); ("data", `List [`Int (Z.to_int i); `Int (Z.to_int j)])]

let parse_commitment_msg comm_msg =
  let rec aux i = function
    | [] -> Nil
    | x :: xs -> Cons ((Z.of_int i, Utils.json_to_string x), aux (i+1) xs)
  in
  aux 1 (Utils.json_to_list comm_msg)

let chl_ref = ref (Z.zero, Z.zero);;
  
let vs_ref = ref (Nil, Nil, (Z.zero, Z.zero)) ;;
  
let challenge_msg ns cs =

  nsinputs_ref := Z.add (Z.of_int ns) !nsinputs_ref ;

  circuit_ref := ((!npinputs_ref, !nsinputs_ref, Z.one, !ngates_ref), !gg_ref) ;
  
  let cs = parse_commitment_msg cs in
  
  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGW5Sha3MitH = ShamirBGW5Sha3MitH (RELC) in

  let module MITHBGWR = Evocrypt.Random.MITHBGW(PC5) in

  Format.printf "Producing challenge message...@." ;
  let t0 = Sys.time () in
  let (i,j) = MITHBGWR.generate_verifier_randomness () in
  let t1 = Sys.time () in
  Format.printf "Challenge message generated in %f ms.@." ((t1 -. t0) *. 1000.) ;
  
  let (vs, chl) = ShamirBGW5Sha3MitH.challenge (i,j) !instance_ref cs in
  chl_ref := chl ;
  vs_ref := vs ;

  Yojson.to_string (challenge_to_json chl)

let json_to_pinputs xp =
  let rec aux = function
    | [] -> Nil
    | x :: xs -> Cons (Z.of_string (Utils.json_to_string x), aux xs)
  in
  aux (Utils.json_to_list xp)
  
let json_to_input x =
  let open Yojson.Safe.Util in
  let pinputs = x |> member "pinputs" in
  let sinputs = x |> member "sinputs" in
  (json_to_pinputs pinputs, json_to_pinputs sinputs)

let json_to_monomial m =
  let open Yojson.Safe.Util in
  let coef = m |> member "coef" |> Utils.json_to_string in
  let expo = m |> member "expo" |> Utils.json_to_string in
  { coef = Z.of_string coef ; expo = Z.of_string expo }
  
let rec json_to_polynomial = function
  | [] -> Nil
  | m :: ms -> Cons (json_to_monomial m, json_to_polynomial ms)
  
let json_to_rand r =
  let open Yojson.Safe.Util in
  let r_mpc = r |> member "r_mpc" |> Utils.json_to_list in
  let r_ref = r |> member "r_ref" |> Utils.json_to_list in
  
  let json_to_gate_rand obj =
    match keys obj with
    | ["Add"] -> BGWData.AdditionRand ()
    | ["Mul"] -> BGWData.MultiplicationRand (obj |> member "Mul" |> Utils.json_to_list |> json_to_polynomial)
    | ["SMul"] -> BGWData.SMultiplicationRand ()
  in

  let rec aux = function
    | [] -> Nil
    | x :: xs ->
       let gid = x |> member "gid" |> Utils.json_to_int in
       let r = x |> member "r" in
       Cons ((Z.of_int gid, json_to_gate_rand r), aux xs)
  in

  (aux r_mpc, json_to_polynomial r_ref)

let rec json_to_shares = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Safe.Util in
     let pid = x |> member "pid" |> Utils.json_to_int in
     let sh = x |> member "sh" |> Utils.json_to_string in
     Cons ((Z.of_int pid, Z.of_string sh), json_to_shares xs)

let rec json_to_addition_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Safe.Util in
     let pid = x |> member "pid" |> Utils.json_to_int in
     Cons ((Z.of_int pid, ()), json_to_addition_in_messages xs)
     
let rec json_to_multiplication_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Safe.Util in
     let pid = x |> member "pid" |> Utils.json_to_int in
     let ims = x |> member "msg" |> Utils.json_to_string in
     Cons ((Z.of_int pid, Z.of_string ims), json_to_multiplication_in_messages xs)

let rec json_to_smultiplication_in_messages = function
  | [] -> Nil
  | x :: xs ->
     let open Yojson.Safe.Util in
     let pid = x |> member "pid" |> Utils.json_to_int in
     Cons ((Z.of_int pid, ()), json_to_smultiplication_in_messages xs)

let rec json_to_in_messages = function
  | [("PInputLT", json)] -> BGWData.PInputLT (Z.of_string (Utils.json_to_string json))
  | [("SInputLT", json)] -> BGWData.SInputLT (Z.of_int (Utils.json_to_int json))
  | [("ConstantLT", json)] ->
     let open Yojson.Safe.Util in
     let gid = json |> member "gid" |> Utils.json_to_int in
     let c = json |> member "c" |> Utils.json_to_string in
     BGWData.ConstantLT (Z.of_int gid, Z.of_string c)
  | [("AdditionLT", json)] ->
     let open Yojson.Safe.Util in
     let gid = json |> member "gid" |> Utils.json_to_int in
     let ims = json |> member "ims" |> Utils.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.AdditionLT (Z.of_int gid, json_to_addition_in_messages ims, json_to_in_messages (Utils.json_to_dico lt), json_to_in_messages (Utils.json_to_dico rt))
  | [("MultiplicationLT", json)] ->
     let open Yojson.Safe.Util in
     let gid = json |> member "gid" |> Utils.json_to_int in
     let ims = json |> member "ims" |> Utils.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.MultiplicationLT (Z.of_int gid, json_to_multiplication_in_messages ims, json_to_in_messages (Utils.json_to_dico lt), json_to_in_messages (Utils.json_to_dico rt))
  | [("SMultiplicationLT", json)] ->
     let open Yojson.Safe.Util in
     let gid = json |> member "gid" |> Utils.json_to_int in
     let ims = json |> member "ims" |> Utils.json_to_list in
     let lt = json |> member "lt" in
     let rt = json |> member "rt" in
     BGWData.SMultiplicationLT (Z.of_int gid, json_to_smultiplication_in_messages ims, json_to_in_messages (Utils.json_to_dico lt), json_to_in_messages (Utils.json_to_dico rt))
  | _ -> assert (false)
        
let json_to_trace t =
  let open Yojson.Safe.Util in
  let pouts = t |> member "pouts" |> Utils.json_to_list in
  let mpc_ims = t |> member "mpc_ims" |> Utils.json_to_dico in
  let ref_ims = t |> member "ref_ims" |> Utils.json_to_list in
  (json_to_shares pouts, (json_to_in_messages mpc_ims, json_to_multiplication_in_messages ref_ims))

let json_to_view v =
  let open Yojson.Safe.Util in
  let x = v |> member "input" in
  let r = v |> member "rand" in
  let t = v |> member "trace" in

  (json_to_input x, json_to_rand r, json_to_trace t)

let decide resp_msg =
  let open Yojson.Safe.Util in

  Format.printf "Parsing response message...@." ;
  let t0 = Sys.time () in

  let viewi = resp_msg |> member "viewi" in
  let viewj = resp_msg |> member "viewj" in
  
  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGW5Sha3MitH = ShamirBGW5Sha3MitH (RELC) in

  let resp = ((json_to_view viewi, ()), (json_to_view viewj, ())) in
  let t1 = Sys.time () in
  Format.printf "Response message parsed in %f ms.@." ((t1 -. t0) *. 1000.) ;

  Format.printf "Checking proof...@." ;
  let t0 = Sys.time () in

  let final = ShamirBGW5Sha3MitH.check !vs_ref resp in
  
  let t1 = Sys.time () in
  
  Format.printf "Proof checked in %f ms.@." ((t1 -. t0) *. 1000.) ;
  Format.printf "Decision = %s@." (if final then "TRUE" else "FALSE")

let get_my_addr () =
  (Unix.gethostbyname(Unix.gethostname())).Unix.h_addr_list.(0) ;;

let handle_service ic oc =
  try while true do

        let pmsg = input_line ic in

        let json = Yojson.Safe.from_string pmsg in
        let open Yojson.Safe.Util in
        let action = json |> member "action" |> to_string in
        
        let vmsg =
          if (action = "ready") then
            begin
              Format.printf "Notifying the prover that I am ready...@." ;
              Yojson.to_string (`Assoc [("action", `String "start")])
            end
          else
            if (action = "commitment") then
              begin
                Format.printf "Received commitment from prover.@." ;
                Format.printf "Generating challenge...@." ;
          
                let data = json |> member "data" in
                let ns = json |> member "ns" |> Utils.json_to_int in
                let chmsg = challenge_msg ns data in
                
                Format.printf "Finished challenge generation@." ;
                chmsg
              end
            else
              if (action = "response") then
                begin
                  Format.printf "Received response from prover.@." ;
                  Format.printf "Generating final decision...@." ;
                  let data = json |> member "data" in
                  decide data ;
                  Yojson.to_string (`Assoc [("action", `String "done")])
                end
              else
                if (action = "done") then raise Sys.Break
                else
                  begin Format.eprintf "Bad query!" ; Unix.shutdown_connection ic ; exit 2 end ;
        in
        
        output_string oc (vmsg^"\n") ; flush oc

      done ;
  with
  | Sys.Break -> raise Sys.Break
  | _ ->
     begin
       Printf.printf "End of text\n" ;
       let _ = Sys.sigint in
       flush stdout ; Unix.shutdown (Unix.descr_of_in_channel ic) Unix.SHUTDOWN_ALL ; Unix.shutdown (Unix.descr_of_out_channel oc) Unix.SHUTDOWN_ALL ; exit 1 
     end

let establish_server server_fun sockaddr =
  let domain = Unix.domain_of_sockaddr sockaddr in
  let sock = Unix.socket domain Unix.SOCK_STREAM 0 
  in Unix.bind sock sockaddr ;
     Unix.listen sock 3;
     let (s, caller) = Unix.accept sock 
     in match Unix.fork() with
          0 -> if Unix.fork() <> 0 then exit 0 ; 
               let inchan = Unix.in_channel_of_descr s 
               and outchan = Unix.out_channel_of_descr s 
               in server_fun inchan outchan ;
                  close_in inchan ;
                  close_out outchan ;
                  Unix.close s ;
                  exit 0
          | id -> Unix.close s; ignore(Unix.waitpid [] id)
    
       
let main_server serv_fun port rel inst =
  try
    let port = port in
    
    relation_file := rel ;
    instance_file := inst ;

    Format.printf "Files:@." ;
    Format.printf "\tRelation file: %s@." !relation_file ;
    Format.printf "\tInstance file: %s@." !instance_file ;

    Format.printf "Parsing relation, instance files...@." ;
    let t0 = Sys.time () in
    
    let statement, witness, nmul, plugins, max_id =
      Wiztoolkit_load.parse_files_mith [!relation_file; !instance_file; !witness_file] in

    let t1 = Sys.time () in
    Format.printf "Relation, instance and witness parsed in %f ms.@." ((t1 -. t0) *. 1000.) ;

    let instance      = statement.mith_instance in
    let circuit = statement.mith_relation in
    let header        = statement.mith_header in
    let (topo, gg) = circuit in
    let (np,ns,m,q) = (topo.npinputs, topo.nsinputs, topo.ngates, topo.noutputs) in
    
    let instance = Utils.array_to_eclist instance in

    let ns = Z.add ns np in
    let topo = (np,ns,m,q) in
    let circuit = (topo,gg) in

    EcPrimeField.q := header.field_characteristic ;
    
    circuit_ref := circuit ;
    
    npinputs_ref := np ;
    nsinputs_ref := ns ;
    ngates_ref := q ;

    gg_ref := gg ;

    instance_ref := instance ;

    Format.printf "Waiting for the prover boot...@." ;
          
    let my_address = Unix.inet_addr_loopback in
    establish_server serv_fun (Unix.ADDR_INET(my_address, port)) 
  with
  | Sys.Break ->
      Unix.kill (Unix.getpid ()) Sys.sigkill ; 
      Unix.kill (Unix.getpid ()) Sys.sigquit ; 
      
  (*Unix.kill (Unix.getpid ()) 0 ; (Format.printf "i am here@." ; exit 0)*)
      
  | Failure("int_of_string") -> 
      Printf.eprintf "serv_up : bad port number\n"
  | Not_found -> Printf.eprintf "what?\n"

let mith_bgw_verifier_exec port rel inst cores =
  Unix.handle_unix_error main_server handle_service port rel inst