(*
 * Copyright (c) 2018-present
 *
 * Vladimir Marcin (xmarci10@stud.fit.vutbr.cz)
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Brno University of Technology, Czech Republic
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
open! IStd
module F = Format
module Domain = DeadlockDomain

type analysis_data =
  {interproc: DeadlockDomain.summary InterproceduralAnalysis.t; extras: FormalMap.t}

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = DeadlockDomain
  module Lockset = DeadlockDomain.Lockset

  type nonrec analysis_data = analysis_data

  let exec_instr astate {interproc= {proc_desc; analyze_dependency}; extras} (_cfg_node : CFG.Node.t) _idx (instr: HilInstr.t) =
    let pname = Procdesc.get_proc_name proc_desc
    in
    (* l1 + l2 / l3 -> [l1] *)
    let get_path actuals =
      List.hd actuals |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs |> List.hd
      |> Option.map ~f:HilExp.AccessExpression.to_access_path
    in
    match instr with
    | Call (_, Direct callee_pname, actuals, _, loc) -> (
      match ConcurrencyModels.get_lock_effect callee_pname actuals with
      | Lock _ ->
        (* lock(l1) *)
        (*
        F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
        F.printf "lock at line %a\n" Location.pp loc;
        *)
        get_path actuals
        |> Option.value_map ~default:astate ~f:(fun path -> Domain.acquire path astate loc extras pname)
      | Unlock _ ->
        (*
        F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
        F.printf "unlock at line %a\n" Location.pp loc;
        *)
        get_path actuals
        |> Option.value_map ~default:astate ~f:(fun path -> Domain.release path astate loc extras pname)
      (* TODO try_lock *)
      | LockedIfTrue _ ->
          astate
      (* User function call *)
      | NoEffect ->
        (* F.printf "User defined function %a at line %a\n" Procname.pp callee_pname Location.pp loc; *)
        analyze_dependency callee_pname
        |> Option.value_map ~default:(astate) ~f:(fun (_, summary) ->
          let callee_formals =
            match AnalysisCallbacks.proc_resolve_attributes callee_pname with
            | Some callee_attr -> callee_attr.ProcAttributes.formals
            | None -> []
          in
          Domain.integrate_summary astate callee_pname loc summary callee_formals actuals pname
        )
      | _ -> assert(false)
    )
    | _ -> astate

  let pp_session_name _node fmt = F.pp_print_string fmt "deadlock";
end

module CFG = ProcCfg.Normal

(* An analyser definition *)
module L2D2 = LowerHil.MakeAbstractInterpreter (TransferFunctions(ProcCfg.Normal))
let checker ({InterproceduralAnalysis.proc_desc; tenv=_; err_log} as interproc) =
  let formals = FormalMap.make proc_desc in
  let data = {interproc; extras= formals} in
  let proc_name = Procdesc.get_proc_name proc_desc in
  (* Compute the abstract state for a given function *)
  match L2D2.compute_post data ~initial:Domain.empty proc_desc with
  | Some post ->
      (* Remove local locks *)
      let post_without_locals : Domain.t =
        { 
          lockset = (Domain.Lockset.inter post.lockset post.wereLocked); 
          unlockset = post.unlockset; 
          dependencies = post.dependencies; 
          locked = post.locked; 
          unlocked = post.unlocked; 
          order = post.order; 
          wereLocked = post.wereLocked
        }
      in
      (* Report warnings *)
      DeadlockDomain.ReportSet.iter
      (fun (dllock, dlloc, dlpname, dlstr, dltype) ->
        let locks : string list = List.fold dllock ~init:[] ~f:(fun accum elem ->
          accum@[(DeadlockDomain.LockWarning.make_string_of_lock elem)])
        in
        let message = F.asprintf "%s of '%s' at function '%s'\n"
          dlstr (String.concat ~sep:", " locks)
          (Procname.to_string dlpname)
        in
        let ltr : Errlog.loc_trace_elem list =
          [Errlog.make_trace_element 0 dlloc "" [Errlog.Procedure_start dlpname]]
        in
        let err_desc = Localise.verbatim_desc message
        in
        let issue_to_report : IssueToReport.t = {issue_type=dltype; description=err_desc; ocaml_pos=None}
        in
        Reporting.log_issue_from_summary ~severity_override:Warning proc_desc err_log
          ~node:UnknownNode ~session:0 ~loc:dlloc ~ltr DeadlockChecker issue_to_report
      ) !DeadlockDomain.reportMap;
      DeadlockDomain.reportMap := DeadlockDomain.ReportSet.empty;
      Some post_without_locals
  | None ->
    Logging.die InternalError
    "The detection of deadlock failed to compute a post for '%a'." Procname.pp proc_name

(**
 * Deadlocks reporting by first creating a relation of all dependencies and 
 * computing the transitive closure of that relation. Deadlock is reported if 
 * some lock depends on itself in the transitive closure. Every deadlock found
 * by our analyser is reported twice, at each trace starting point.
 *)
let report_deadlocks dependencies : IssueLog.t=
  (* Returns set of all locks used in an analysed program. *)
  let get_all_locks : Domain.Edges.t -> Domain.Lockset.t =
    fun dependencies ->
      let set_of_all_locks = Domain.Lockset.empty in
      let f : Domain.Edges.elt -> Domain.Lockset.t -> Domain.Lockset.t =
        fun pair acc ->
          let first = Domain.Lockset.add (fst pair.edge) acc in
          let second = Domain.Lockset.add (snd pair.edge) acc in
          Domain.Lockset.union first second
      in
      Domain.Edges.fold f dependencies set_of_all_locks
  in
  (**
   * Creates a list from a set of locks used in an analysed program.
   * The lock index in this list serves as a lock index in the formed matrix. 
   *)
  let list_of_all_locks = Domain.Lockset.elements (get_all_locks dependencies) in
  let rec find : Domain.Lockset.elt -> Domain.Lockset.elt list -> int =
    fun x lst ->
      match lst with
      | [] -> raise (Failure "Not Found")
      | h :: t -> if Domain.LockEvent.equal x h then 0 else 1 + find x t
  in
  (* number of locks (matrix dimension) *)
  let n = (Domain.Lockset.cardinal (get_all_locks dependencies)) in
  let m = Array.make_matrix ~dimx:n ~dimy:n false in
  (* A matrix representing dependencies between locks. *)
  let matrix = Domain.Edges.fold (fun pair acc ->
        let first = find (fst pair.edge) list_of_all_locks in
        let second = find (snd pair.edge) list_of_all_locks in
        acc.(first).(second) <- true;
        acc) 
    dependencies m 
  in
  let deadlocks_list = ref []
  in
  (* A Computing of transitive closure and reporting of deadlocks. *)
  for k = 0 to (n - 1) do
    for i = 0 to (n - 1) do
      for j = 0 to (n - 1) do
        matrix.(i).(j) <- matrix.(i).(j) || (matrix.(i).(k) && matrix.(k).(j));
        (* if there is (L, L) in the closure, we report deadlock *)
        if(matrix.(i).(j) && (phys_equal i j)) then
          deadlocks_list := (j, k) :: !deadlocks_list
      done;
    done;
  done;
  let fold issue_log (j, k) : IssueLog.t =
    (* Finding the first pair that is causing a deadlock. *)
    let first_pair =
      let e : Domain.Edge.t =
        {edge = ((List.nth_exn list_of_all_locks k),(List.nth_exn list_of_all_locks j)); pname = Procname.empty_block}
      in
      try Some (Domain.Edges.find e dependencies)
      with Caml.Not_found -> None
    in
    (* Finding the second pair that is causing a deadlock. *)
    let second_pair =
      let e : Domain.Edge.t =
        {edge = ((List.nth_exn list_of_all_locks j),(List.nth_exn list_of_all_locks k)); pname = Procname.empty_block}
      in
      try Some (Domain.Edges.find e dependencies)
      with Caml.Not_found -> None
    in
    match (first_pair, second_pair) with
    | (Some a, Some b) ->
      if not(Domain.Edge.equal a.edge b.edge) then (
        let message = F.asprintf "Deadlock between:\t%a\n\t\t\t%a\n"
          Domain.Edge.pp a Domain.Edge.pp b;
        in
        let loc = (snd(fst(a.edge)))
        in
        let ltr : Errlog.loc_trace_elem list =
          [Errlog.make_trace_element 0 (snd(fst(a.edge))) "" [Errlog.Procedure_start a.pname]]
        in
        Reporting.log_issue_external a.pname ~issue_log ~severity_override:Error ~loc ~ltr
          DeadlockChecker IssueType.deadlock_L2D2 message
      ) else issue_log
    | (_, _) -> issue_log
  in
  List.fold !deadlocks_list ~init:IssueLog.empty ~f:fold

let reporting (analysis_data : Domain.t InterproceduralAnalysis.file_t) : IssueLog.t =
  (* Getting all lock dependencies in the analysed program. *)
  let locks_dependencies =
    List.fold analysis_data.procedures ~f:(fun acc procname ->
      match analysis_data.analyze_file_dependency procname with
      | Some (summary : Domain.t) -> Domain.Edges.union summary.dependencies acc
      | None -> acc
    ) ~init:Domain.Edges.empty
  in
  (* debug log
  let g =
    let e : Domain.Edge.t -> Domain.LocksGraph.t -> Domain.LocksGraph.t =
      fun edge acc ->
        DeadlockDomain.LocksGraph.add_edge_e acc (edge.edge); 
        acc
    in
    DeadlockDomain.Edges.fold e locks_dependencies (DeadlockDomain.LocksGraph.create ())   
  in
  let print_graph = 
    let print_edge e e' = F.printf "edge: %a -> %a\n" Domain.LockEvent.pp e Domain.LockEvent.pp e' in
    Domain.LocksGraph.iter_edges print_edge g
  in
  print_graph;
  F.printf "has cycle: %b\n" (DeadlockDomain.DfsLG.has_cycle g);
  let print_pre : Domain.LockEvent.t -> unit =
    fun eve ->
      F.printf "pre: %a\n" Domain.LockEvent.pp eve
  in
  let print_post : Domain.LockEvent.t -> unit =
    fun eve ->
      F.printf "post: %a\n" Domain.LockEvent.pp eve
  in
  Domain.DfsLG.iter g ~pre:print_pre ~post:print_post;
  *)
  report_deadlocks locks_dependencies
