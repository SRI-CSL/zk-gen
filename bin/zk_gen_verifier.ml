let backend = ref ""
let cores = ref 0
let relation = ref ""
let instance = ref ""
let witness = ref ""
let port = ref 0

exception Invalid_backend of string

let options = [
  ("--backend", Arg.Set_string backend, "ZK backend");
  ("--cores", Arg.Set_int cores, "Parallel cores");
  ("--relation", Arg.Set_string relation, "Relation file");
  ("--instance", Arg.Set_string instance, "Instance file");
  ("--port", Arg.Set_int port, "Listening port")
]

let get_backend_name bck =
    match bck with
    | "mith-bgw" -> "BGW MPC-in-the-Head"
    | "vole-lpzk" -> "Paillier VOLE + LPZK"
    | "lpzk" -> "LPZK"
    | _ -> "not supported"

let usage_message = "zk-gen-verifier --backend [BACKEND] --cores [# PARALLEL CORES] --relation [RELATION FILE] --instance [INSTANCE FILE] --port [LISTENING PORT]\n\n" ^ 
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
  if Array.length Sys.argv < 11 then
    begin Format.eprintf "%s@." usage_message ; exit(1) end
  else
    Arg.parse options (fun a->args := a::!args) usage_message;
    check () ;
    
    match !backend with
    | "lpzk" -> ZKGenLib.LPZKVerifier.lpzk_verifier_exec !port !relation !instance !cores
    | "mith-bgw" -> ZKGenLib.MITHBGWVerifier.mith_bgw_verifier_exec !port !relation !instance !cores
  
(*end*)
