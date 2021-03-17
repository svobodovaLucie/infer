(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
open AtomicityUtils
module Domain = AtomicityViolationsDomain
module F = Format
module L = Logging

(** Detection of atomicity violations implementation. *)

(** A transfer function for abstract states of an analysed function. *)
module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type analysis_data = Domain.Summary.t InterproceduralAnalysis.t

  let exec_instr (astate : Domain.t) (analysis_data : analysis_data) (_ : CFG.Node.t) :
      HilInstr.t -> Domain.t = function
    | Call
        ( (_ : AccessPath.base)
        , (Direct (calleePname : Procname.t) : HilInstr.call)
        , (actuals : HilExp.t list)
        , (_ : CallFlags.t)
        , (_ : Location.t) )
      when f_is_ignored calleePname ~actuals:(Some actuals) ->
        astate
    (* Update the abstract state on function calls. *)
    | Call
        ( (_ : AccessPath.base)
        , (Direct (calleePname : Procname.t) : HilInstr.call)
        , (actuals : HilExp.t list)
        , (_ : CallFlags.t)
        , (loc : Location.t) ) -> (
      match
        ConcurrencyModels.get_lock_effect ~tenv:(Some analysis_data.tenv) calleePname actuals
      with
      (* lock *)
      | Lock (locks : HilExp.t list) ->
          Domain.apply_locks (get_exps_paths locks) astate
      (* unlock *)
      | Unlock (locks : HilExp.t list) ->
          Domain.apply_unlocks (get_exps_paths locks) astate
      (* guard construct *)
      | GuardConstruct {guard: HilExp.t; locks: HilExp.t list; strategy= Default} ->
          Domain.apply_guard_construct (get_exp_path guard) (get_exps_paths locks) ~acquire:true
            astate
      | GuardConstruct {guard: HilExp.t; locks: HilExp.t list; strategy= DeferLock | AdoptLock} ->
          Domain.apply_guard_construct (get_exp_path guard) (get_exps_paths locks) ~acquire:false
            astate
      (* guard release *)
      | GuardRelease (guard : HilExp.t) ->
          Domain.apply_guard_release (get_exp_path guard) astate
      (* guard destroy *)
      | GuardDestroy (guard : HilExp.t) ->
          Domain.apply_guard_destroy (get_exp_path guard) astate
      (* guard lock *)
      | GuardLock (guard : HilExp.t) ->
          Domain.apply_locks [get_exp_path guard] astate
      (* guard unlock *)
      | GuardUnlock (guard : HilExp.t) ->
          Domain.apply_unlocks [get_exp_path guard] astate
      (* TODO: trylock *)
      | LockedIfTrue (_ : HilExp.t list) ->
          astate
      (* TODO: guard trylock via constructor *)
      | GuardConstruct {guard: HilExp.t = _; locks: HilExp.t list = _; strategy= TryToLock} ->
          astate
      (* TODO: guard trylock *)
      | GuardLockedIfTrue (_ : HilExp.t) ->
          astate
      (* function call *)
      | NoEffect -> (
          let astate : Domain.t =
            Domain.apply_call ~fName:(Procname.to_string calleePname) loc astate
          in
          (* Update the abstract state with the function summary as well if it is possible. *)
          match analysis_data.analyze_dependency calleePname with
          | Some ((_ : Procdesc.t), (summary : Domain.Summary.t)) ->
              Domain.apply_summary summary loc astate
          | None ->
              astate ) )
    | _ ->
        astate


  let pp_session_name (node : CFG.Node.t) (fmt : F.formatter) : unit =
    F.fprintf fmt "AtomicityViolations: %a" CFG.Node.pp_id (CFG.Node.id node)
end

(** An analyser definition. *)
module Analyser = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Normal))

let analyse_procedure (analysis_data : Domain.Summary.t InterproceduralAnalysis.t) :
    Domain.Summary.t option =
  let pName : Procname.t = Procdesc.get_proc_name analysis_data.proc_desc in
  if f_is_ignored pName then None
  else
    let pre : Domain.t =
      if Procdesc.is_java_synchronized analysis_data.proc_desc then
        Domain.apply_locks [proc_name_to_access_path pName] Domain.initial
      else Domain.initial
    in
    (* Compute the abstract state for a given function. *)
    match Analyser.compute_post analysis_data ~initial:pre analysis_data.proc_desc with
    | Some (post : Domain.t) ->
        (* Convert the abstract state to the function summary. *)
        let summary : Domain.Summary.t = Domain.Summary.create post in
        (* Debug log. *)
        let fmt : F.formatter = F.str_formatter and (_ : string) = F.flush_str_formatter () in
        F.fprintf fmt "\n\nFunction: %a\n%a%a\n\n" Procname.pp pName Domain.pp post
          Domain.Summary.pp summary ;
        L.(debug Capture Verbose) "%s" (F.flush_str_formatter ()) ;
        (* Report atomicity violations. *)
        Domain.report_atomicity_violations post ~f:(fun (loc : Location.t) ~(msg : string) : unit ->
            Reporting.log_issue analysis_data.proc_desc analysis_data.err_log ~loc
              AtomicityViolations IssueType.atomicity_violation msg) ;
        Some summary
    | None ->
        L.die InternalError
          "The detection of atomicity violations failed to compute a post for '%a'." Procname.pp
          pName
