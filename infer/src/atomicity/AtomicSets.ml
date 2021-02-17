(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module Domain = AtomicSetsDomain
module F = Format
module L = Logging

(** Detection of atomic sets implementation. *)

(** A transfer function for abstract states of an analysed function. *)
module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type analysis_data = Domain.Summary.t InterproceduralAnalysis.t

  let exec_instr (astate : Domain.t) (analysis_data : analysis_data) (_ : CFG.Node.t)
      (instr : HilInstr.t) : Domain.t =
    match instr with
    | Call
        ( (_ : AccessPath.base)
        , (Direct (calleePname : Procname.t) : HilInstr.call)
        , (actuals : HilExp.t list)
        , (_ : CallFlags.t)
        , (_ : Location.t) )
      when AtomicityUtils.f_is_ignored calleePname ~actuals:(Some actuals) ->
        astate
    (* Update the abstract state on function calls. *)
    | Call
        ( (_ : AccessPath.base)
        , (Direct (calleePname : Procname.t) : HilInstr.call)
        , (actuals : HilExp.t list)
        , (_ : CallFlags.t)
        , (_ : Location.t) ) -> (
      match ConcurrencyModels.get_lock_effect calleePname actuals with
      (* lock *)
      | Lock (locks : HilExp.t list) ->
          Domain.apply_lock ~locks:(AtomicityUtils.get_locks_paths locks) astate
      | GuardConstruct {guard; acquire_now= true} | GuardLock (guard : HilExp.t) ->
          Domain.apply_lock ~locks:(AtomicityUtils.get_locks_paths [guard]) astate
      (* unlock *)
      | Unlock (locks : HilExp.t list) ->
          Domain.apply_unlock ~locks:(AtomicityUtils.get_locks_paths locks) astate
      | GuardUnlock (guard : HilExp.t) | GuardDestroy (guard : HilExp.t) ->
          Domain.apply_unlock ~locks:(AtomicityUtils.get_locks_paths [guard]) astate
      (* TODO: try lock *)
      | LockedIfTrue (_ : HilExp.t list) ->
          astate
      | GuardLockedIfTrue (_ : HilExp.t) ->
          astate
      (* function call *)
      | NoEffect -> (
          let astate : Domain.t = Domain.apply_call astate (Procname.to_string calleePname) in
          (* Update the abstract state with the function summary as well if it is possible. *)
          match analysis_data.analyze_dependency calleePname with
          | Some ((_ : Procdesc.t), (summary : Domain.Summary.t)) ->
              Domain.apply_summary astate summary
          | None ->
              astate )
      | _ ->
          astate )
    | _ ->
        astate


  let pp_session_name (_ : CFG.Node.t) (fmt : F.formatter) : unit =
    F.pp_print_string fmt "AtomicSets"
end

(** An analyser definition. *)
module Analyser = LowerHil.MakeAbstractInterpreter (TransferFunctions (ProcCfg.Normal))

let analyse_procedure (analysis_data : Domain.Summary.t InterproceduralAnalysis.t) :
    Domain.Summary.t option =
  let pName : Procname.t = Procdesc.get_proc_name analysis_data.proc_desc in
  if AtomicityUtils.f_is_ignored pName then None
  else
    let pre : Domain.t =
      if Procdesc.is_java_synchronized analysis_data.proc_desc then Domain.apply_lock Domain.initial
      else Domain.initial
    in
    (* Compute the abstract state for a given function. *)
    match Analyser.compute_post analysis_data ~initial:pre analysis_data.proc_desc with
    | Some (post : Domain.t) ->
        (* Update the abstract state at the end of a function and convert the abstract state to the
           function summary. *)
        let updatedPost : Domain.t = Domain.update_at_the_end_of_function post in
        let summary : Domain.Summary.t = Domain.Summary.make updatedPost in
        (* Debug log. *)
        let fmt : F.formatter = F.str_formatter and (_ : string) = F.flush_str_formatter () in
        F.fprintf fmt "\n\nFunction: %a\n%a%a\n\n" Procname.pp pName Domain.pp updatedPost
          Domain.Summary.pp summary ;
        L.(debug Capture Verbose) "%s" (F.flush_str_formatter ()) ;
        Some summary
    | None ->
        L.(die InternalError)
          "The detection of atomic sets failed to compute a post for '%a'." Procname.pp pName


let print_atomic_sets (analysis_data : AtomicSetsDomain.Summary.t InterproceduralAnalysis.file_t) :
    IssueLog.t =
  (* Create a directory for printing. *)
  Utils.create_dir AtomicityUtils.inferDir ;
  (* Print to a file. *)
  let oc : Out_channel.t =
    Out_channel.create ~binary:false ~append:Config.atomic_sets_file_append ~fail_if_exists:false
      AtomicityUtils.atomicSetsFile
  and proceduresCount : int ref = ref 0
  and atomicSetsCount : int ref = ref 0
  and atomicFunctionsCount : int ref = ref 0 in
  let print_atomic_sets (pName : Procname.t) : unit =
    let iterator ((_ : Procdesc.t), (summary : Domain.Summary.t)) : unit =
      let (atomicSetsCount' : int), (atomicFunctionsCount' : int) =
        Domain.Summary.print_atomic_sets summary ~f_name:(Procname.to_string pName) oc
      in
      if not (Int.equal atomicSetsCount' 0) then proceduresCount := !proceduresCount + 1 ;
      atomicSetsCount := !atomicSetsCount + atomicSetsCount' ;
      atomicFunctionsCount := !atomicFunctionsCount + atomicFunctionsCount'
    in
    Option.iter (analysis_data.analyze_file_dependency pName) ~f:iterator
  in
  List.iter analysis_data.procedures ~f:print_atomic_sets ;
  (* Print stats. *)
  if not (Int.equal !proceduresCount 0) then Out_channel.newline oc ;
  Out_channel.fprintf oc
    "%c Number of (analysed functions; atomic sets; atomic functions): (%i; %i; %i)\n"
    AtomicityUtils.fileCommentChar !proceduresCount !atomicSetsCount !atomicFunctionsCount ;
  Out_channel.close oc ;
  F.fprintf F.std_formatter "The detection of atomic sets produced an output into the file '%s'.\n"
    AtomicityUtils.atomicSetsFile ;
  IssueLog.empty
