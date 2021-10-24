(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format
(*module L = Logging *)

(*
module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  (* module Domain = IntervalCheckerDomain *)

  type analysis_data = IntervalCheckerDomain.t InterproceduralAnalysis.t

  (** Take an abstract state and instruction, produce a new abstract state *)
  let _exec_instr (astate : IntervalCheckerDomain.t)
      {InterproceduralAnalysis.proc_desc=_; tenv=_; analyze_dependency= _; _} _ _ (instr : HilInstr.t)
      =
    match instr with
    | Call (_return_opt, Direct _callee_procname, _actuals, _, _loc) ->
        (* function call [return_opt] := invoke [callee_procname]([actuals]) *)
        (* if acquires_resource tenv callee_procname then IntervalCheckerDomain.acquire_resource astate
        else if releases_resource tenv callee_procname then
          IntervalCheckerDomain.release_resource astate
        else astate *)
        astate
    | Assign (_lhs_access_path, _rhs_exp, _loc) ->
        (* an assignment [lhs_access_path] := [rhs_exp] *)
        astate
    | Assume (_assume_exp, _, _, _loc) ->
        (* a conditional assume([assume_exp]). blocks if [assume_exp] evaluates to false *)
        astate
    | Call (_, Indirect _, _, _, _) ->
        (* This should never happen in Java. Fail if it does. *)
        L.(die InternalError) "Unexpected indirect call %a" HilInstr.pp instr
    | Metadata _ ->
        astate


  let _pp_session_name _node fmt = F.pp_print_string fmt "Interval Checker"
end
*)

(** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to
    ignore them *)
(* module CFG = ProcCfg.Normal *)

(* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
(* module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG)) *)

(** Report an error when we have acquired more resources than we have released *)
let _report_if_leak {InterproceduralAnalysis.proc_desc; err_log; _} post =
  (*if IntervalCheckerDomain.has_leak post then
    let last_loc = Procdesc.Node.get_loc (Procdesc.get_exit_node proc_desc) in
    let message = F.asprintf "Leaked %a resource(s) in Interval Checker" IntervalCheckerDomain.pp post in
    Reporting.log_issue proc_desc err_log ~loc:last_loc IntervalExperimentalChecker
      IssueType.interval_issue message;; *)
    let last_loc = Procdesc.Node.get_loc (Procdesc.get_exit_node proc_desc) in
    let message = F.asprintf "Leaked %a resource(s) in Interval Checker" IntervalCheckerDomain.pp post in
    Reporting.log_issue proc_desc err_log ~loc:last_loc IntervalExperimentalChecker
      IssueType.interval_issue message;;


(** Main function into the checker--registered in RegisterCheckers *)
let checker ({InterproceduralAnalysis.proc_desc=_} as _analysis_data : int InterproceduralAnalysis.t) : int option =
  Some 100

  (* Analyzer.compute_post analysis_data ~initial:IntervalCheckerDomain.initial proc_desc in
  Option.iter result ~f:(fun post -> report_if_leak analysis_data post) ; *);
