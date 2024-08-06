let backend = ref ""
let cores = ref 0
let relation = ref ""
let instance = ref ""
let witness = ref ""
let verip = ref ""
let verport = ref 0

exception Invalid_backend of string

let options = [
  ("--backend", Arg.Set_string backend, "ZK backend");
  ("--cores", Arg.Set_int cores, "Parallel cores");
  ("--relation", Arg.Set_string relation, "Relation file");
  ("--instance", Arg.Set_string instance, "Instance file");
  ("--witness", Arg.Set_string witness, "Witness file");
  ("--verip", Arg.Set_string verip, "Verifier IP");
  ("--verport", Arg.Set_int verport, "Verifier port")
]

let get_backend_name bck =
    match bck with
    | "mith-bgw" -> "BGW MPC-in-the-Head"
    | "vole-lpzk" -> "Paillier VOLE + LPZK"
    | "lpzk" -> "LPZK"
    | _ -> "not supported"

let usage_message = "zk-gen-prover --backend [BACKEND] --cores [# PARALLEL CORES] --relation [RELATION FILE] --instance [INSTANCE FILE] --witness [WITNESS FILE] --verip [DESTINATION IP] --verport [DESTINATION PORT]\n\n" ^ 
                    "Backend options:\n" ^
                      "\tmith-bgw - " ^ get_backend_name "mith-bgw" ^ "\n" ^
                      "\tlpzk - " ^ get_backend_name "lpzk" ^ ""
let args = ref []

let is_valid_backend = function
  | "mith-bgw" -> true
  | "lpzk" -> true
  | _ -> false

let check () =
  if not (is_valid_backend !backend) then
    begin raise (Invalid_backend !backend) end

let () =
  if Array.length Sys.argv < 15 then
    begin Format.eprintf "%s@." usage_message ; exit(1) end
  else
    Arg.parse options (fun a->args := a::!args) usage_message;
    check () ;
  
    match !backend with
    | "lpzk" -> ZKGenLib.LPZKProver.lpzk_prover_exec !verip !verport !relation !instance !witness !cores
    | "mith-bgw" -> ZKGenLib.MITHBGWProver.mith_bgw_prover_exec !verip !verport !relation !instance !witness !cores
  
(*end*)
