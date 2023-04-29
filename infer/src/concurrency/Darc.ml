(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(* Data Race Checker *)

open! IStd
module F = Format
(* module L = Logging *)
module Domain = DarcDomain

type extras_t =
{
  last_loc: Location.t;
  heap_tmp: (HilExp.AccessExpression.t * Location.t) list;
}

let initial_extras =
{
  last_loc = Location.dummy;
  heap_tmp = [];
}

type analysis_data = {interproc: DarcDomain.summary InterproceduralAnalysis.t; extras : extras_t ref}

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type nonrec analysis_data = analysis_data

  (* READ access handle_load tenv id e typ ~lhs:(Var.of_id id, typ) loc astate *)
  let handle_load _tenv id e typ ~lhs loc (astate : Domain.t) pname =
    let lhs_var = fst lhs in
    let add_deref = match (lhs_var : Var.t) with LogicalVar _ -> true | ProgramVar _ -> false in
    let e_hil_exp = Domain.transform_sil_expr_to_hil e typ add_deref in
    match e_hil_exp with
    | HilExp.AccessExpression e_ae -> (
      let id_ae = HilExp.AccessExpression.of_id id typ in
      Domain.load id_ae e_ae e typ loc astate pname
    )
    | _ -> astate

let handle_store_after_malloc e1 typ e2 loc astate (extras : extras_t ref) pname =
  let add_deref_e1 =
    match e1 with
    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> true
    | _ -> false
  in
  let e1_hil = Domain.transform_sil_expr_to_hil e1 typ add_deref_e1 in
    match e1_hil with
    | AccessExpression e1_ae -> (
      (* if e2 is Cast (e.g. in malloc), get only the cast_exp, e.g. n$0 *)
      let e2_exp =
        match e2 with
        | Exp.Cast (_, cast_exp) -> cast_exp
        | _ -> e2
      in
      let e2_hil = Domain.transform_sil_expr_to_hil e2_exp typ false in
      match e2_hil with
      | AccessExpression e2_ae -> (
        (* update heap aliases and heap_tmp, return updated astate *)
        let (astate_with_new_access_and_heap_alias, updated_heap_tmp) = Domain.add_access_with_heap_alias_when_malloc e1_ae e2_ae loc astate !(extras).heap_tmp pname in
        extras := { !(extras) with heap_tmp=updated_heap_tmp };
        astate_with_new_access_and_heap_alias
      )
      | _ -> astate
    )
    | _ -> astate

  let handle_store e1 typ e2 loc astate pname (extras : extras_t ref)  =
   match !(extras).heap_tmp with
   | [] -> (* simple store *)
     Domain.store e1 typ e2 loc astate pname
   | _ -> ( (* the list of heap_tmp is not empty -> add dynamically allocated variable *)
     handle_store_after_malloc e1 typ e2 loc astate extras pname
   )

  let handle_pthread_create _callee_pname pname loc actuals sil_actual_argument analyze_dependency astate =
    (* get first argument - the thread to be added *)
    match List.nth actuals 0 with
    | Some HilExp.AccessExpression th_load_ae -> (
      (* create new thread *)
      let new_thread =
        (* find the thread in threads_active *)
        Domain.new_thread th_load_ae loc astate
      in
      (* add the thread to astate *)
      let astate_with_new_thread = Domain.add_thread new_thread astate in
      (* add summary of the callback function (third argument) *)
      match List.nth actuals 2 with
      | Some HilExp.Constant Cfun f -> (
        (* analyze the dependency on demand *)
        analyze_dependency f
        |> Option.value_map ~default:(astate_with_new_thread) ~f: (
        fun (_, summary) ->
          (* get callee formals *)
          let callee_formals =
            match AnalysisCallbacks.proc_resolve_attributes f with
            | Some callee_attr -> callee_attr.ProcAttributes.formals
            | None -> []
          in
          (* update callee accesses and add them to astate *)
          Domain.integrate_pthread_summary astate_with_new_thread new_thread f loc summary callee_formals actuals sil_actual_argument pname
        )
      )
      | _ -> astate
    )
    | _ -> astate

  (* remove thread from threads_active *)
  let handle_pthread_join _callee_pname _loc actuals astate =
    match List.nth actuals 0 with
    | Some HilExp.AccessExpression th_ae -> Domain.remove_thread th_ae astate
    | _ -> astate

  let clear_load_aliases_if_new_loc astate (last_loc : Location.t) (loc : Location.t) =
    if (loc.line > last_loc.line) then
      begin
        Domain.astate_with_clear_load_aliases astate (last_loc.line - 10) (* save load aliases of the last 10 loc *)
      end
    else
      begin
        astate
      end

  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr (astate : Domain.t) ({interproc= {proc_desc; tenv; analyze_dependency}} as analysis_data) _ _ instr =
    let pname = Procdesc.get_proc_name proc_desc in
    match (instr : Sil.instr) with
    | Load {id; e; typ; loc} -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* update last_loc *)
      analysis_data.extras := { last_loc = loc; heap_tmp = !(analysis_data.extras).heap_tmp };
      (* compute the result (add new access, load_aliases etc.) *)
      handle_load tenv id e typ ~lhs:(Var.of_id id, typ) loc astate pname
    )
    | Store {e1; typ; e2; loc} -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* update last_loc in extras *)
      analysis_data.extras := { last_loc = loc; heap_tmp = !(analysis_data.extras).heap_tmp };
      (* compute the result (add new access, load_aliases etc.) *)
      handle_store e1 typ e2 loc astate pname analysis_data.extras
    )
    | Call ((ret_id, ret_typ), Const (Cfun callee_pname), sil_actuals, loc, _call_flags) -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* update last_loc in extras *)
      analysis_data.extras := { last_loc = loc; heap_tmp = !(analysis_data.extras).heap_tmp };
      (* get list of hil actuals *)
      let hil_actuals = Domain.transform_sil_exprs_to_hil_list sil_actuals false in
      if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_create") 0) then
        (* handle the creation of a new thread *)
        let sil_actual_argument = List.nth sil_actuals 3 in (* variable passed to the function *)
        match sil_actual_argument with
        | Some sil_actual ->
          handle_pthread_create callee_pname pname loc hil_actuals sil_actual analyze_dependency astate
        | None -> astate (* invalid argument *)
      else if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_join") 0) then
        (* handle pthread_join *)
        handle_pthread_join callee_pname loc hil_actuals astate
      else if (phys_equal (String.compare (Procname.to_string callee_pname) "malloc") 0)
        || (phys_equal (String.compare (Procname.to_string callee_pname) "calloc") 0)
        || (phys_equal (String.compare (Procname.to_string callee_pname) "__new") 0) then
        (* handle dynamic memory allocation on heap *)
        (* get load expression (e.g. n$1) *)
        let ret_id_ae = HilExp.AccessExpression.of_id ret_id ret_typ in
        (* save it to extras.heap_tmp for the use in STORE instruction,
           new heap alias will be added in STORE *)
        let new_heap_tmp = (ret_id_ae, loc) in
        let heap_tmp = new_heap_tmp :: !(analysis_data.extras).heap_tmp in
        analysis_data.extras := { last_loc = loc; heap_tmp };
        (* return the unchanged astate *)
        astate
      else
        (* LOCKS *)
        match ConcurrencyModels.get_lock_effect callee_pname hil_actuals with
        | Lock _ -> (
          (* pthread_mutex_lock(mutex) - one argument *)
          match hil_actuals with
          | actual :: [] -> Domain.acquire_lock actual astate loc
          | _ -> astate (* invalid argument *)
        )
        | Unlock _ -> (
          (* pthread_mutex_unlock(mutex) - one argument *)
          match hil_actuals with
          | actual :: [] -> Domain.release_lock actual astate loc
          | _ -> astate (* shouldn't happen *)
        )
        | NoEffect -> (
          (* user defined function -> get summary of callee and integrate it to the current astate *)
          analyze_dependency callee_pname
          |> Option.value_map ~default:(astate) ~f:(
            fun (_, summary) ->
              let callee_formals =
                match AnalysisCallbacks.proc_resolve_attributes callee_pname with
                | Some callee_attr -> callee_attr.ProcAttributes.formals
                | None -> []
              in
              Domain.integrate_summary astate callee_pname loc summary callee_formals hil_actuals pname
          )
        )
        | _ -> astate
    )
    | _ -> (* Metadata, Prune... -> astate is not updated *)
      astate

  let pp_session_name _node fmt = F.pp_print_string fmt "darc" (* checker name in the debug html *)
end


(* function adds all locals to the locals list *)
let add_locals_to_list proc_attributes_list pname =
(*  F.printf "locals...\n";*)
  let locals_empty = Domain.LocalsSet.empty in
  let rec add_local proc_attributes_list locals_set : Domain.LocalsSet.t =
    match proc_attributes_list with
    | [] -> locals_set
    | (var : ProcAttributes.var_data) :: t ->
      (* add the variable to the locals list *)
      let pvar_mk = Pvar.mk var.name pname in
      let access_path_base = AccessPath.base_of_pvar pvar_mk var.typ in
      let ae = HilExp.AccessExpression.base access_path_base in
      let locals_set_new = Domain.add_var_to_locals ae locals_set in
      add_local t locals_set_new
  in
  add_local proc_attributes_list locals_empty

(* function adds non-pointer formals to the locals list *)
let add_nonpointer_formals_to_list formals locals_set pname =
  (* TODO predelat na access_expressions!!! *)
(*  F.printf "formals...\n";*)
  let rec loop lst locals =
    match lst with
    | [] -> locals
    | var :: tl ->
      (* create access expression from var *)
      let var_pvar = Pvar.mk (fst var) pname in
      let var_base = AccessPath.base_of_pvar var_pvar (snd var) in
      let var_base_ae = HilExp.AccessExpression.base var_base in
      (* if typ is not a pointer, add the variable to locals list *)
      let locals_set_new =
        if not (Typ.is_pointer (snd var)) then
          Domain.add_var_to_locals var_base_ae locals
        else
          locals
      in
      loop tl locals_set_new
  in
  loop formals locals_set

let add_formal_to_heap_aliases formal heap_aliases pname line_num =
  (* (Mangled.t * Typ.t) -> HilExp.AccessExpression.t formal *)
  let formal_pvar = Pvar.mk (fst formal) pname in
  let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
  let formal_ae = HilExp.AccessExpression.base formal_access_path_base in
  (* make dummy Location *)
  let loc_dummy = Location.dummy in
  let loc_dummy = { loc_dummy with line=line_num } in
  (* add formal to the list *)
  let new_heap_aliases = (formal_ae, loc_dummy) :: heap_aliases in
  new_heap_aliases

let add_formals_to_heap_aliases astate formals pname =
  let rec add_each_formal_to_heap_aliases formals_lst heap_aliases_lst (line_num : int) =
    match formals_lst with
    | [] -> heap_aliases_lst
    | formal :: t -> (
      let updated_heap_aliases_lst = add_formal_to_heap_aliases formal heap_aliases_lst pname line_num in
      add_each_formal_to_heap_aliases t updated_heap_aliases_lst (line_num - 1)
    )
  in
  let heap_aliases_with_formals = add_each_formal_to_heap_aliases formals [] (-1) in
  Domain.add_heap_aliases_to_astate astate heap_aliases_with_formals

(** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to ignore them *)
(*module CFG = ProcCfg.Normal*)

(* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
(*module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))*)
module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (ProcCfg.Normal))

(* COMPUTE THE RESULT AND REPORT ERRORS *)
let report {InterproceduralAnalysis.proc_desc; err_log; _} post =
(*  F.printf "REPORTING AND COMPUTING ----------------------------------------\n";*)
  let data_races_list = (Domain.compute_data_races post) in
  let rec report_all_data_races lst =
    match lst with
    | [] -> ()
    | (fst, snd) :: t -> (
      let fst_message = F.asprintf "Data race between \t%a\n\t\t\t%a\n" DarcDomain.AccessEvent.pp_report_long fst DarcDomain.AccessEvent.pp_report_long snd in
      (* let snd_message = F.asprintf "Potential data race between \t%a\n\t\t\t%a\n" DarcDomain.AccessEvent.pp_report_short snd DarcDomain.AccessEvent.pp_report_short fst in *)
      let fst_loc = Domain.AccessEvent.get_loc fst in
      (* let snd_loc = Domain.AccessEvent.get_loc snd in *)
      Reporting.log_issue proc_desc err_log ~loc:fst_loc DarcChecker IssueType.darc_error fst_message;
      (* Reporting.log_issue proc_desc err_log ~loc:snd_loc DarcChecker IssueType.darc_error snd_message *)
      report_all_data_races t
    )
  in
  report_all_data_races data_races_list

(** Main function into the checker--registered in RegisterCheckers *)
let checker ({InterproceduralAnalysis.proc_desc; tenv=_; err_log=_} as interproc) =
  let data = {interproc; extras = ref initial_extras} in
  let pname = Procdesc.get_proc_name proc_desc in
  F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s START >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));

  (* create a list of locals and add all the locals and non-pointer formals to the list *)
  let proc_desc_locals = Procdesc.get_locals proc_desc in   (* locals declared in the function *)
  let locals_set = add_locals_to_list proc_desc_locals pname in
  let formals = Procdesc.get_formals proc_desc in (* formals of the function *)
  let locals_set = add_nonpointer_formals_to_list formals locals_set pname in

  (* If the analysed function is main -> we need to do few changes -> add main thread to threads... *)
  let init_astate : DarcDomain.t =
    if (phys_equal (String.compare (Procname.to_string (Procdesc.get_proc_name proc_desc)) "main") 0) then
      DarcDomain.initial_main locals_set
    else
      DarcDomain.empty_with_locals locals_set
    in
    (* add formals to heap_aliases *)
    let init_astate = add_formals_to_heap_aliases init_astate formals pname in
    (* compute function summary *)
    let result = Analyzer.compute_post data ~initial:init_astate proc_desc in
    F.printf "result: Domain.print_astate:\n";
    let _print_result =
      match result with
      | None -> F.printf "None\n"
      | Some res -> Domain.print_astate res
    in
    F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s END >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
    (* compute data races in main *)
    if (phys_equal (String.compare (Procname.to_string (Procdesc.get_proc_name proc_desc)) "main") 0) then
      Option.iter result ~f:(fun post -> report interproc post);
    (* final summary *)
    result