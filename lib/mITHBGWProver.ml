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

let relation_file = ref ""
let witness_file = ref ""
let instance_file = ref ""

let state = ref Nil ;;

let circuit_ref = ref ((Z.zero, Z.zero, Z.zero, Z.zero), witness) ;;

(** produces the commitment json *)
let commitment_to_json ns cs =

  let c0 = oget (assoc cs !p1) in 
  let c1 = oget (assoc cs !p2) in 
  let c2 = oget (assoc cs !p3) in 
  let c3 = oget (assoc cs !p4) in 
  let c4 = oget (assoc cs !p5) in 
  
  `Assoc [("action", `String "commitment"); ("data", `List [`String c0; `String c1; `String c2; `String c3; `String c4]); ("ns", `Int (Z.to_int ns))]

let commitment_msg (x : unit) =

  Format.printf "Parsing relation, instance and witness files...@." ;
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
  
  let witness = Utils.pad_witness np (Utils.array_to_eclist witness) in
  let instance = Utils.array_to_eclist instance in

  let ns = Z.add ns np in
  let topo = (np,ns,m,q) in
  let circuit = (topo,gg) in

  EcPrimeField.q := header.field_characteristic ;

  circuit_ref := circuit ;
  
  Format.printf "Generating prover randomness...@." ;
  let t0 = Sys.time () in

  let module MITHBGWR = Evocrypt.Random.MITHBGW(PC5) in
  let prover_rand = MITHBGWR.generate_prover_randomness gg (Z.add np ns) in

  let t1 = Sys.time () in

  Format.printf "Randomness generated in %f ms@." ((t1 -. t0) *. 1000.) ;

  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGW5Sha3MitH = ShamirBGW5Sha3MitH (RELC) in

  Format.printf "Producing commitment message...@." ;
  let t0 = Sys.time () in
  let (ps, cs) = ShamirBGW5Sha3MitH.commitment prover_rand (witness, instance) in
  let t1 = Sys.time () in
  Format.printf "Commitment message generated in %f ms@." ((t1 -. t0) *. 1000.) ;
  
  state := ps ;
  let commitment_msg = Yojson.to_string (commitment_to_json ns cs) in

  commitment_msg

let pinputs_to_json xp =
  let rec aux = function
    | Nil -> []
    | Cons (x, xs) -> `String (Z.to_string x) :: aux xs
  in
  `List (aux xp)
  
let input_to_json x =
  let (xp, xs) = x in
  `Assoc [("pinputs", pinputs_to_json xp); ("sinputs", pinputs_to_json xs)]

let monomial_to_json m =
  `Assoc [("coef", `String (Z.to_string m.coef)); ("expo", `String (Z.to_string m.expo))]
  
let rec polynomial_to_json = function
  | Nil -> []
  | Cons (m, ms) -> monomial_to_json m :: polynomial_to_json ms
  
let rand_to_json r =
  let (r_mpc, r_ref) = r in
  
  let gate_rand_to_json = function
    | BGWData.AdditionRand r -> `Assoc [("Add", `List [])]
    | BGWData.MultiplicationRand r -> `Assoc [("Mul", `List (polynomial_to_json r))]
    | BGWData.SMultiplicationRand r -> `Assoc [("SMul", `List [])]
  in
    
  let rec aux = function
    | Nil -> []
    | Cons (x, xs) ->
       let (gid, gr) = x in
       (`Assoc [("gid", `Int (Z.to_int gid)); ("r", gate_rand_to_json gr)]) :: aux xs
  in
  
  `Assoc [ ("r_mpc", `List (aux r_mpc)); ("r_ref", `List (polynomial_to_json r_ref)) ]

let rec shares_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, sh) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("sh", `String (Z.to_string sh))]) :: shares_to_json xs

let rec addition_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `Null)]) :: addition_in_messages_to_json xs

let rec multiplication_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `String (Z.to_string ims))]) :: multiplication_in_messages_to_json xs

let rec smultiplication_in_messages_to_json = function
  | Nil -> []
  | Cons (x, xs) ->
     let (pid, ims) = x in
     (`Assoc [("pid", `Int (Z.to_int pid)) ; ("msg", `Null)]) :: smultiplication_in_messages_to_json xs
     
let rec in_messages_to_json = function
  | BGWData.PInputLT x -> `Assoc [("PInputLT", `String (Z.to_string x))]
  | SInputLT wid -> `Assoc [("SInputLT", `Int (Z.to_int wid))]
  | ConstantLT (gid, x) -> `Assoc [("ConstantLT", `Assoc [("gid", `Int (Z.to_int gid)); ("c", `String (Z.to_string x))])]
  | AdditionLT (gid, ims, lt, rt) ->
     `Assoc [("AdditionLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (addition_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  | MultiplicationLT (gid, ims, lt, rt) ->
     `Assoc [("MultiplicationLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (multiplication_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  | SMultiplicationLT (gid, ims, lt, rt) ->
     `Assoc [("SMultiplicationLT", `Assoc [("gid", `Int (Z.to_int gid)); ("ims", `List (smultiplication_in_messages_to_json ims)) ; ("lt", in_messages_to_json lt) ; ("rt", in_messages_to_json rt)])]
  
let trace_to_json t = 
  let (pouts, ims) = t in
  let (mpc_ims, ref_ims) = ims in
  `Assoc [ ("pouts", `List (shares_to_json pouts)) ; ("mpc_ims", in_messages_to_json mpc_ims) ; ("ref_ims", `List (multiplication_in_messages_to_json ref_ims)) ]
  
let view_to_json v =
  let (x, r, t) = v in
  `Assoc [ ("input", input_to_json x) ; ("rand", rand_to_json r); ("trace", trace_to_json t) ]
  
(** produces the response message *)
let response_msg ch =

  let (i, j) = ch in

  let module RELC = struct let relc = !circuit_ref end in
  let module ShamirBGW5Sha3MitH = ShamirBGW5Sha3MitH (RELC) in

  Format.printf "Producing response message...@." ;
  let t0 = Sys.time () in
  
  let (vi, cii) = oget (assoc !state i) in
  let (ci, osi) = cii in
  let (vj, cij) = oget (assoc !state j) in
  let (cj, osj) = cij in

  let vi_json = view_to_json vi in
  let vj_json = view_to_json vj in
  
  let resp_json = `Assoc [ ("action", `String "response"); ("data", `Assoc [("viewi", vi_json) ; ("viewj", vj_json)])] in

  let t1 = Sys.time () in
  Format.printf "Response message generated in %f ms@." ((t1 -. t0) *. 1000.) ;

  Yojson.to_string (resp_json)
  
let client_fun ic oc =
  let initial_json = `Assoc [("action", `String "ready")] in
  let pmsg = ref (Yojson.to_string initial_json) in
  try
    while true do  
      flush oc ;
      output_string oc (!pmsg^"\n") ;
      flush oc ;
      
      let vmsg = input_line ic in

      let json = Yojson.Safe.from_string vmsg in
      let open Yojson.Safe.Util in
      let action = json |> member "action" |> to_string in
      
      pmsg :=
        if (action = "start") then
          begin
            Format.printf "Generating commitment...@." ;
            let cmsg = commitment_msg () in
            Format.printf "Finished commitment generation@." ;
            cmsg
          end
        else
          if (action = "challenge") then
            begin
              Format.printf "Received challenge from verifier.@." ;
              Format.printf "Generating response...@." ;
              
              let data = json |> member "data" in
              let chl = Utils.json_to_list data in
              let i = Utils.json_to_int (List.nth chl 0) in
              let j = Utils.json_to_int (List.nth chl 1) in
              
              let rmsg = response_msg (Z.of_int i, Z.of_int j) in
              Format.printf "Finished response generation@." ;
              rmsg 
            end
          else
            if (action = "done") then
              begin
                Format.printf "Finalizing MitH protocol...@." ;
                Yojson.to_string (`Assoc [("action", `String "done")])
              end
            else "Bad query!" ;      
    done
  with 
    Exit -> exit 0
  | End_of_file -> exit 0
  | exn -> Unix.shutdown_connection ic ; raise exn  ;;

let main_client client_fun verip verport rel inst wit =
  let server = verip in
  let server_addr =
    try Unix.inet_addr_of_string server 
    with Failure("inet_addr_of_string") -> 
      try  (Unix.gethostbyname server).Unix.h_addr_list.(0) 
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

    Format.printf "\tRelation file: %s@." !relation_file ;
    Format.printf "\tInstance file: %s@." !instance_file ;
    Format.printf "\tRelation file: %s@." !witness_file ;
         
    let ic,oc = Unix.open_connection sockaddr in 
    client_fun ic oc ;
    Unix.shutdown_connection ic
  with Failure("int_of_string") -> 
    Printf.eprintf "bad port number";
    exit 2 ;;

let mith_bgw_prover_exec verip verport rel inst wit cores =
  main_client client_fun verip verport rel inst wit