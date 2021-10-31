(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format
(* module L = Logging *)
module Domain = IntervalCheckerDomain

module TransferFunctions (CFG : ProcCfg.S) = struct
    module CFG = CFG
    module Domain = Domain

    type analysis_data = IntervalCheckerDomain.t InterproceduralAnalysis.t

    (** Take an abstract state and instruction, produce a new abstract state *)
    let exec_instr (astate : IntervalCheckerDomain.t)
        {InterproceduralAnalysis.proc_desc= _; tenv=_; analyze_dependency; _} _ _ (instr : HilInstr.t)
        =
        match instr with
        | Call (_return_opt, Direct callee_procname, _actuals, _, loc) -> (
            if (phys_equal (String.compare (Procname.to_string callee_procname) "printf") 0) then
            (
                F.printf "PrintChecker: Print function call %s at line %a\n"
                         (Procname.to_string callee_procname) Location.pp loc;
                Domain.inc astate
            )
            else
                match analyze_dependency callee_procname with
                | Some (_callee_proc_desc, callee_summary) ->
                    Domain.apply_summary ~summary:callee_summary astate
                | None ->
                    astate
            )
        | _ ->
            astate

        let pp_session_name _node fmt = F.pp_print_string fmt "Interval Checker"
end

(** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to
    ignore them *)
module CFG = ProcCfg.Normal

(* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))

let report_if_printf {InterproceduralAnalysis.proc_desc; err_log; _} post =
    if Domain.has_printf post then
        let last_loc = Procdesc.Node.get_loc (Procdesc.get_exit_node proc_desc) in
        let message = F.asprintf "Number of printf: %a in Interval Checker\n" IntervalCheckerDomain.pp post in
        Reporting.log_issue proc_desc err_log ~loc:last_loc IntervalExperimentalChecker
            IssueType.interval_issue message;;

(** Main function into the checker--registered in RegisterCheckers *)
let checker ({InterproceduralAnalysis.proc_desc; tenv=_} as analysis_data) =
    let _convert_to_summary (post : Domain.astate) : Domain.summary =
        post
    in
    let _extras = FormalMap.make proc_desc in
    F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Interval Checker: function %s START >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
    let result = Analyzer.compute_post analysis_data ~initial:IntervalCheckerDomain.initial proc_desc in
        Option.iter result ~f:(fun post -> report_if_printf analysis_data post);
    F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Interval Checker: function %s END >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
    result
