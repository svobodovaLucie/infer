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

  type analysis_data =
    {interproc: DarcDomain.summary InterproceduralAnalysis.t; extras : int}

  module TransferFunctions (CFG : ProcCfg.S) = struct
      module CFG = CFG
      module Domain = Domain
      (* module Lockset = DarcDomain.Lockset *)

      type nonrec analysis_data = analysis_data

      (** Take an abstract state and instruction, produce a new abstract state *)
      let exec_instr astate {interproc={proc_desc=_; analyze_dependency=_}; extras=_} (_cfg_node : CFG.Node.t) _idx (instr: HilInstr.t)
          (* {InterproceduralAnalysis.proc_desc= _; tenv=_; analyze_dependency; _} _ _ (instr : HilInstr.t) *)
          =
          match instr with
          | Call (_return_opt, Direct callee_procname, _actuals, _, loc) -> (
              if (phys_equal (String.compare (Procname.to_string callee_procname) "printf") 0) then
              (
                  F.printf "DarcChecker: Print function call %s at line %a\n"
                           (Procname.to_string callee_procname) Location.pp loc;
                  astate
              )
              (*
              else
                  match analyze_dependency callee_procname with
                  | Some (_callee_proc_desc, callee_summary) ->
                      Domain.apply_summary ~summary:callee_summary astate
                  | None ->
                      astate
              *)
              else (astate)
            )

          | _ ->
                  F.printf "DarcChecker: Another something function than printf call\n";
                  astate



          let pp_session_name _node fmt = F.pp_print_string fmt "darc" (* checker name in the debug html *)
  end

  (** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to
      ignore them *)
  module CFG = ProcCfg.Normal

  (* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
  module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))

  let report_if_printf {InterproceduralAnalysis.proc_desc; err_log; _} post =
    let last_loc = Procdesc.Node.get_loc (Procdesc.get_exit_node proc_desc) in
    let message = F.asprintf "Number of printf: %a in Data Race Checker\n" DarcDomain.pp post in
    Reporting.log_issue proc_desc err_log ~loc:last_loc DarcChecker IssueType.darc_error message;;

  (** Main function into the checker--registered in RegisterCheckers *)
  let checker ({InterproceduralAnalysis.proc_desc; tenv=_; err_log=_} as interproc) =
      let data = {interproc; extras = 0} in
      F.printf "Hello from Darc Checker.\n";
      F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s START >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
      let result = Analyzer.compute_post data ~initial:DarcDomain.empty proc_desc in
          Option.iter result ~f:(fun post -> report_if_printf interproc post);
      F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s END >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
      result