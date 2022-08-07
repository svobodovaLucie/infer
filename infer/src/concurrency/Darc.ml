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

  let assign_expr lhs_access_expr rhs_expr loc {interproc={tenv=_}; extras=_} (astate : Domain.t) =
    F.printf "Access lhs: %a at line %a\n" HilExp.AccessExpression.pp lhs_access_expr Location.pp loc;
    let lhs_access_path = HilExp.AccessExpression.to_access_path lhs_access_expr in
    let new_astate = Domain.assign_expr lhs_access_path astate loc in
    let rhs_access_expr = HilExp.get_access_exprs rhs_expr in
    let rhs_access_expr_first = List.hd rhs_access_expr in
    match rhs_access_expr_first with
    | Some rhs_access_expr_first ->
        F.printf "Access rhs_first: %a\n" HilExp.AccessExpression.pp rhs_access_expr_first;
        astate
    | None -> F.printf "Access rhs_first: None on loc %a\n" Location.pp loc;
    new_astate

  module TransferFunctions (CFG : ProcCfg.S) = struct
      module CFG = CFG
      module Domain = Domain

      type nonrec analysis_data = analysis_data

      (** Take an abstract state and instruction, produce a new abstract state *)
      let exec_instr astate ({interproc={proc_desc; analyze_dependency}; extras=_} as analysis_data) (_cfg_node : CFG.Node.t) _idx (instr: HilInstr.t)
          =
          let pname = Procdesc.get_proc_name proc_desc
              in
              (* l1 + l2 / l3 -> [l1] *)
              let get_path actuals =
                List.hd actuals |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs |> List.hd
                |> Option.map ~f:HilExp.AccessExpression.to_access_path
              in
          match instr with
          | Call (_return_opt, Direct callee_pname, actuals, _, loc) -> (
              (* pthread_create(thread, retval, start_routine, args) *)
              if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_create") 0) then
              (
                  F.printf "DarcChecker: Pthread_create function call %s at line %a\n"
                           (Procname.to_string callee_pname) Location.pp loc;
                  (* print actuals function *)
                  let print_raw num : unit = (
                      match List.nth actuals num with
                          | Some arg ->
                          (
                              F.printf "DarcChecker: arg %d %a at line %a\n" num HilExp.pp arg Location.pp loc;
                              ()
                          )
                          | None ->
                          (
                              F.printf "None\n";
                              ()
                          )
                  )
                  in
                  (* print raw actuals *)
                  print_raw 0;
                  print_raw 1;
                  print_raw 2;
                  print_raw 3;
                  (* TODO add thread to the astate.thread and to threads_active *)
                  (* returns new thread *)
                  let _new_thread : (AccessPath.t * Location.t) = (
                    match List.nth actuals 0 with
                    | Some th ->
                    (
                      match th with
                      | AccessExpression ae ->
                          F.printf "YEAH %a ---------------------\n" HilExp.AccessExpression.pp ae;
                          (* )F.printf "YEAH %a ---------------------\n" AccessPath.pp th_access_path; *)

                          let th_access_path = HilExp.AccessExpression.to_access_path ae in
                          (th_access_path, loc)

                      | _ -> F.printf "NAAAH ----------------\n"; assert false
                    )
                    | None -> assert false
                  )
                  in
                  (*
                  let new_threadset
                  let get_thread actuals =
                    let thread = ThreadSet.empty in
                    match List.nth actuals 0 with
                      | Some th ->
                      (
                        (* add to threads_active *)
                        let th_access_path = HilExp.to_access_path th in
                        let new_thread = (th, loc) in
                        ThreadSet.add new_thread thread
                      )
                      | None -> thread
                  in
                  *)
                  (* add thread to active threads *)
                  (* Domain.ThreadSet.add new_thread astate.threads_active;
                  in *)
                  (* )Domain.add_thread new_thread astate in )*)
                  (* analyze dependency - 3rd argument *)
                  match List.nth actuals 2 with
                      | Some pname_act ->
                      (
                          match pname_act with
                              | Constant c ->
                              (
                                  match c with
                                      | Cfun f ->
                                          F.printf "pname_act %a c=s f=%a matched\n" HilExp.pp pname_act Procname.pp f;
                                          F.printf "-----> function call %a at line %a\n" Procname.pp f Location.pp loc;
                                          (* analyze the dependency on demand *)
                                          analyze_dependency f
                                          (* converting actuals to formals - FIXME will be different in this case - argument is the 4th param of pthread_create() *)
                                          (* TODO add new_thread to the thread in each record in callee_summary.accesses *)
                                          |> Option.value_map ~default:(astate) ~f:(fun (_, summary) ->
                                              let callee_formals =
                                                  match AnalysisCallbacks.proc_resolve_attributes f with
                                                      | Some callee_attr -> callee_attr.ProcAttributes.formals
                                                      | None -> []
                                                  in
                                                  Domain.integrate_summary astate f loc summary callee_formals actuals pname
                                          )
                                      | _ -> astate
                              )
                              | _ -> astate
                      )
                      | None -> astate
                    (*
                        F.printf "DarcChecker: arg2 %a at line %a\n"
                             HilExp.pp snd Location.pp loc;
                        F.printf "DarcChecker: arg3 %a at line %a\n"
                             HilExp.pp trd Location.pp loc;
                        F.printf "DarcChecker: arg4 %a at line %a\n"
                             HilExp.pp ftr Location.pp loc;
                    *)
              ) else if (phys_equal (String.compare (Procname.to_string callee_pname) "printf") 0) then
              (
                 F.printf "DarcChecker: Print function call %s at line %a\n"
                            (Procname.to_string callee_pname) Location.pp loc;
                 astate
              ) else (
              (* LOCKS *)
              match ConcurrencyModels.get_lock_effect callee_pname actuals with
                    | Lock _ ->
                      (
                      (* lock(l1) *)

                      F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
                      F.printf "lock at line %a\n" Location.pp loc;

                      get_path actuals
                      |> Option.value_map ~default:astate ~f:(fun path -> Domain.acquire path astate loc (* extras *) pname)
                      )
                    | Unlock _ ->
                      (
                      F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
                      F.printf "unlock at line %a\n" Location.pp loc;

                      get_path actuals
                      |> Option.value_map ~default:astate ~f:(fun path -> Domain.release path astate loc (* extras *) pname)
                    (* TODO try_lock *)
                      )
                   | NoEffect ->
                       F.printf "User defined function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
                       analyze_dependency callee_pname
                       |> Option.value_map ~default:(astate) ~f:(fun (_, summary) ->
                         let callee_formals =
                           match AnalysisCallbacks.proc_resolve_attributes callee_pname with
                           | Some callee_attr -> callee_attr.ProcAttributes.formals
                           | None -> []
                         in
                         Domain.integrate_summary astate callee_pname loc summary callee_formals actuals pname
                       )
                   | _ ->
                       F.printf "Function that probably should not be here %a at line %a\n" Procname.pp callee_pname Location.pp loc;
                       astate
                       (* assert(false) *)
                  )
                  )
              (* END LOCKS *)
          | Assign (lhs_access_expr, rhs_exp, loc) ->
              assign_expr lhs_access_expr rhs_exp loc analysis_data astate
          | _ ->
            (
                  F.printf "DarcChecker: Another something function than printf call\n";
                  astate
            )

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