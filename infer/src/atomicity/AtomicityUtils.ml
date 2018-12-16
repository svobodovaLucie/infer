(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module L = Logging
module Set = Caml.Set

(** Atomicity violations analysis utilities implementation. *)

(* ************************************ Modules ************************************************* *)

module SSet = Set.Make (String)

(* ************************************ Constants *********************************************** *)

let inferDir : string = CommandLineOption.init_work_dir ^ "/infer-atomicity-out"

let atomicSetsFile : string = inferDir ^ "/atomic-sets"

(* ************************************ Functions *********************************************** *)

let str_contains ~(haystack : string) ~(needle : string) : bool =
  try
    ignore (Str.search_forward (Str.regexp_string needle) haystack 0) ;
    true
  with Caml.Not_found -> false


(** A type of a structure that holds function names loaded from a file. *)
type functionsFromFile = {initialised: bool; names: SSet.t} [@@deriving compare]

(** A reference to a structure that holds functions whose calls should be ignored. *)
let ignoredFunctionCalls : functionsFromFile ref = ref {initialised= false; names= SSet.empty}

(** A reference to a structure that holds functions whose analysis should be ignored. *)
let ignoredFunctionAnalyses : functionsFromFile ref = ref {initialised= false; names= SSet.empty}

(** A reference to a structure that holds functions whose calls should be allowed. *)
let allowedFunctionCalls : functionsFromFile ref = ref {initialised= false; names= SSet.empty}

(** A reference to a structure that holds functions whose analysis should be allowed. *)
let allowedFunctionAnalyses : functionsFromFile ref = ref {initialised= false; names= SSet.empty}

(** An initialisation of a structure that holds function names loaded from a file. *)
let initialise_functions_from_file (functions : functionsFromFile ref) (fileOpt : string option) :
    unit =
  if not !functions.initialised then (
    let names : SSet.t ref = ref SSet.empty in
    ( match fileOpt with
    | Some (file : string) ->
        ( match Sys.file_exists file with
        | `Yes ->
            ()
        | _ ->
            L.(die UserError) "File '%s' that should contain function names does not exist." file ) ;
        let ic : In_channel.t = In_channel.create ~binary:false file in
        In_channel.iter_lines ~fix_win_eol:true ic ~f:(fun (f : string) ->
            names := SSet.add f !names) ;
        In_channel.close ic
    | None ->
        () ) ;
    functions := {initialised= true; names= !names} )


let f_is_ignored ?actuals:(actualsOpt : HilExp.t list option = None) (f : Procname.t) : bool =
  initialise_functions_from_file ignoredFunctionCalls Config.atomicity_ignored_function_calls_file ;
  initialise_functions_from_file ignoredFunctionAnalyses
    Config.atomicity_ignored_function_analyses_file ;
  initialise_functions_from_file allowedFunctionCalls Config.atomicity_allowed_function_calls_file ;
  initialise_functions_from_file allowedFunctionAnalyses
    Config.atomicity_allowed_function_analyses_file ;
  let fString : string = Procname.to_string f
  and isCall : bool = Option.is_some actualsOpt
  and isLockUnlock : bool =
    if Procname.equal f BuiltinDecl.__set_locked_attribute then true
    else if Procname.equal f BuiltinDecl.__delete_locked_attribute then true
    else
      match actualsOpt with
      | Some (actuals : HilExp.t list) -> (
        match ConcurrencyModels.get_lock_effect f actuals with
        | Lock (_ : HilExp.t list)
        | Unlock (_ : HilExp.t list)
        | GuardConstruct {guard= _; lock= _; acquire_now= _}
        | GuardLock (_ : HilExp.t)
        | GuardDestroy (_ : HilExp.t)
        | GuardUnlock (_ : HilExp.t)
        | LockedIfTrue (_ : HilExp.t list)
        | GuardLockedIfTrue (_ : HilExp.t) ->
            true
        | _ ->
            false )
      | None ->
          false
  in
  if isLockUnlock then false
  else if (not isCall) && SSet.mem fString !ignoredFunctionAnalyses.names then true
  else if isCall && SSet.mem fString !ignoredFunctionCalls.names then true
  else if
    isCall
    && ( Procname.is_constructor f
       || str_contains ~haystack:fString ~needle:Config.clang_inner_destructor_prefix )
  then true
  else if str_contains ~haystack:fString ~needle:Config.clang_initializer_prefix then true
  else if str_contains ~haystack:fString ~needle:"__" && BuiltinDecl.is_declared f then true
  else if
    (not isCall)
    && (not (SSet.is_empty !allowedFunctionAnalyses.names))
    && not (SSet.mem fString !allowedFunctionAnalyses.names)
  then true
  else if
    isCall
    && (not (SSet.is_empty !allowedFunctionCalls.names))
    && not (SSet.mem fString !allowedFunctionCalls.names)
  then true
  else false


let get_lock_path (exp : HilExp.t) : AccessPath.t option =
  match HilExp.get_access_exprs exp with
  | (accessExp :: _ : HilExp.AccessExpression.t list) ->
      Some (HilExp.AccessExpression.to_access_path accessExp)
  | _ ->
      None
