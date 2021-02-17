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

let fileCommentChar : char = '#'

let is_line_empty (l : string) : bool =
  Str.string_match (Str.regexp "^[ \t]*$") l 0
  || Str.string_match (Str.regexp ("^[ \t]*" ^ Char.to_string fileCommentChar)) l 0


(* ************************************ Classes ************************************************* *)

(** A class that works with functions loaded from a file. *)
class functions_from_file (file : string option) =
  object (self)
    (** Is the class initialised? *)
    val mutable initialised : bool = false

    (** A list of regular expressions that represent functions loaded from a file. *)
    val mutable functions : Str.regexp list = []

    (** Initialises the class. *)
    method init : unit =
      if not initialised then (
        initialised <- true ;
        match file with
        | Some (file : string) ->
            ( match Sys.file_exists file with
            | `Yes ->
                ()
            | _ ->
                L.(die UserError)
                  "File '%s' that should contain function names does not exist." file ) ;
            let ic : In_channel.t = In_channel.create ~binary:false file in
            let iterator (l : string) : unit =
              let l : string = String.strip l in
              if is_line_empty l then ()
              else if Str.string_match (Str.regexp "^R[ \t]+") l 0 then
                let pattern : string = Str.replace_first (Str.regexp "^R[ \t]+") "" l in
                functions <- functions @ [Str.regexp_case_fold (".*" ^ pattern ^ ".*")]
              else functions <- functions @ [Str.regexp_string l]
            in
            In_channel.iter_lines ~fix_win_eol:true ic ~f:iterator ;
            In_channel.close ic
        | None ->
            () )

    (** Checks whether the list of functions is empty. *)
    method is_empty : bool =
      self#init ;
      List.is_empty functions

    (** Checks whether a given function is on the list of functions. *)
    method contains (f : string) : bool =
      self#init ;
      List.exists functions ~f:(fun (r : Str.regexp) -> Str.string_match r f 0)
  end

(** An instance of the 'functions_from_file' class that holds functions whose calls should be
    ignored.. *)
let ignoredFunctionCalls : functions_from_file =
  new functions_from_file Config.atomicity_ignored_function_calls_file


(** An instance of the 'functions_from_file' class that holds functions whose analysis should be
    ignored. *)
let ignoredFunctionAnalyses : functions_from_file =
  new functions_from_file Config.atomicity_ignored_function_analyses_file


(** An instance of the 'functions_from_file' class that holds functions whose calls should be
    allowed. *)
let allowedFunctionCalls : functions_from_file =
  new functions_from_file Config.atomicity_allowed_function_calls_file


(** An instance of the 'functions_from_file' class that holds functions whose analysis should be
    allowed. *)
let allowedFunctionAnalyses : functions_from_file =
  new functions_from_file Config.atomicity_allowed_function_analyses_file


(* ************************************ Functions *********************************************** *)

let str_contains ~(haystack : string) ~(needle : string) : bool =
  try
    ignore (Str.search_forward (Str.regexp_string needle) haystack 0) ;
    true
  with Caml.Not_found -> false


let f_is_ignored ?actuals:(actualsOpt : HilExp.t list option = None) (f : Procname.t) : bool =
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
  else if (not isCall) && ignoredFunctionAnalyses#contains fString then true
  else if isCall && ignoredFunctionCalls#contains fString then true
  else if
    isCall
    && ( Procname.is_constructor f
       || str_contains ~haystack:fString ~needle:Config.clang_inner_destructor_prefix )
  then true
  else if str_contains ~haystack:fString ~needle:Config.clang_initializer_prefix then true
  else if str_contains ~haystack:fString ~needle:"__" && BuiltinDecl.is_declared f then true
  else if
    (not isCall)
    && (not allowedFunctionAnalyses#is_empty)
    && not (allowedFunctionAnalyses#contains fString)
  then true
  else if
    isCall && (not allowedFunctionCalls#is_empty) && not (allowedFunctionCalls#contains fString)
  then true
  else false


let get_locks_paths (locks : HilExp.t list) : AccessPath.t option list =
  let mapper (lock : HilExp.t) : AccessPath.t option =
    match HilExp.get_access_exprs lock with
    | (exp :: _ : HilExp.AccessExpression.t list) ->
        Some (HilExp.AccessExpression.to_access_path exp)
    | _ ->
        None
  in
  List.map locks ~f:mapper
