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

type analysis_data = {interproc: DarcDomain.summary InterproceduralAnalysis.t; extras : int}

let assign_expr lhs_access_expr rhs_expr loc {interproc={tenv=_}; extras=_} (astate : Domain.t) pname =
  F.printf "Access lhs: %a at line %a\n" HilExp.AccessExpression.pp lhs_access_expr Location.pp loc;
  let lhs_access_path = HilExp.AccessExpression.to_access_path lhs_access_expr in
  F.printf "Access lhs access path: %a at line %a\n" AccessPath.pp lhs_access_path Location.pp loc;
  let get_base (a, _) = a in
  let get_access_list (_, b) = b in
  let lhs_base = get_base (lhs_access_path) in
  let lhs_access_list = get_access_list (lhs_access_path) in
  let _lhs_accesses = HilExp.AccessExpression.to_accesses lhs_access_expr in
  F.printf "AccessPath: pp: |%a|, pp_base: |%a|, pp_access: , pp_access_list: |%a|\n" AccessPath.pp lhs_access_path AccessPath.pp_base lhs_base AccessPath.pp_access_list lhs_access_list;
  (* access expression type: *)
  let new_astate = Domain.assign_expr lhs_access_expr astate loc pname in
  let rhs_access_expr = HilExp.get_access_exprs rhs_expr in
  let rhs_access_expr_first = List.hd rhs_access_expr in
  match rhs_access_expr_first with
  | Some rhs_access_expr ->
    Domain.update_aliases lhs_access_expr rhs_access_expr new_astate
  | None -> new_astate

let read_write_expr loc {interproc={tenv=_}; extras=_} pname actuals (astate : Domain.t) =
  F.printf "Access READ at line %a in pname=%a\n" Location.pp loc Procname.pp pname;
  (* get effect a pak postupne ten list projizdet a podle toho pridavat pristupy *)
  let pname_string = Procname.to_string pname in
  let num_of_actuals = List.length actuals in
  let read_write_effects = Domain.ReadWriteModels.get_read_write_effect pname_string num_of_actuals in
  (* mame napr. "printf"  -> [(1, Read); (2, Read)] *)
  let insert_access (nth, effect) astate =
    let var =
      match List.nth actuals nth with
      | Some actual -> ( (* HilExp.t -> AccessPath.t *)
        match actual with
        | HilExp.AccessExpression ae ->
          F.printf "read_write_expr: AccessExpression: %a\n" HilExp.AccessExpression.pp ae;
          (* HilExp.AccessExpression.to_access_path ae *)
          ae
        | _ -> assert false (* TODO check *)
      )
      | None ->
        F.printf "read_write_expr: asserted nth=%d\n" nth;
        assert false (* TODO check *)
    in
    (* return new astate: *)
    Domain.add_access_to_astate var effect astate loc pname
    in
    (* new access with access_type effect and var List.nth nth actuals *)  
    let rec list_fold lst astate = 
      match lst with 
      | [] -> astate
      | h::t -> 
        let new_astate = insert_access h astate in
        list_fold t new_astate
    in
    list_fold read_write_effects astate

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type nonrec analysis_data = analysis_data

  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr astate ({interproc={proc_desc; analyze_dependency}; extras=_} as analysis_data) (_cfg_node : CFG.Node.t) _idx (instr: HilInstr.t) =
  let pname = Procdesc.get_proc_name proc_desc in
  (* l1 + l2 / l3 -> [l1] *)
  let get_path actuals =
    List.hd actuals |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs |> List.hd
    |> Option.map ~f:HilExp.AccessExpression.to_access_path
  in
  match instr with
  | Call (_return_opt, Direct callee_pname, actuals, _, loc) -> (
    if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_create") 0) then
      begin
        F.printf "DarcChecker: Pthread_create function call %s at %a\n" (Procname.to_string callee_pname) Location.pp loc;
        (* print actuals function *)
        let print_raw num : unit = (
          match List.nth actuals num with
          | Some arg -> (
            F.printf "DarcChecker: arg %d %a at line %a\n" num HilExp.pp arg Location.pp loc;
            ()
          )
          | None -> (
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
        (* let lock : LockEvent.t = (lockid, loc) in *)
        let new_thread : Domain.ThreadEvent.t option = (
          match List.nth actuals 0 with
          | Some th -> (
            match th with
            | AccessExpression ae ->
              let th_access_path : AccessPath.t = HilExp.AccessExpression.to_access_path ae in
              Some (th_access_path, loc)
            | _ -> assert false
          )
          | None -> assert false
        )
        in
        (* TODO: add thread to threads_active *)
        let new_astate = Domain.add_thread new_thread astate in
        (* analyze dependency - 3rd argument *)
        match List.nth actuals 2 with
        | Some pname_act -> (
          match pname_act with
          | Constant c -> (
            match c with
            | Cfun f ->
              F.printf "-----> function call %a at %a\n" Procname.pp f Location.pp loc;
              (* analyze the dependency on demand *)
              analyze_dependency f

              (* converting actuals to formals - FIXME will be different in this case - argument is the 4th param of pthread_create() *)
              (* TODO add new_thread to the thread in each record in callee_summary.accesses *)
              |> Option.value_map ~default:(astate) ~f: (
                fun (_, summary) ->
                  let callee_formals =
                    match AnalysisCallbacks.proc_resolve_attributes f with
                    | Some callee_attr -> callee_attr.ProcAttributes.formals
                    | None -> []
                  in
                  Domain.integrate_pthread_summary new_astate new_thread f loc summary callee_formals actuals pname
               )
            | _ -> astate
          )
         | _ -> astate
        )
        | None -> astate
        (* pthread_join() -> remove thread *)
      end
    else if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_join") 0) then
      begin
        let new_thread : Domain.ThreadEvent.t option = (
          match List.nth actuals 0 with
          | Some th -> (
            match th with
            | AccessExpression ae ->
              let th_access_path : AccessPath.t = HilExp.AccessExpression.to_access_path ae in
              Some (th_access_path, loc)
            | _ -> assert false
          )
          | None -> assert false
        )
        in
        F.printf "DarcChecker: pthread_join function call %s at %a\n" (Procname.to_string callee_pname) Location.pp loc;
        Domain.remove_thread new_thread astate (* arg 2 -> the thread to be removed *)
        (* read or write effect*)
      end
    else if (Domain.ReadWriteModels.has_effect (Procname.to_string callee_pname)) then
      begin
        read_write_expr loc analysis_data callee_pname actuals astate
      end
    else
      begin
        (* LOCKS *)
        match ConcurrencyModels.get_lock_effect callee_pname actuals with
        | Lock _ -> (
          (* lock(l1) *)
          F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
          F.printf "lock at line %a\n" Location.pp loc;
          get_path actuals
          |> Option.value_map ~default:astate ~f:(fun path -> Domain.acquire path astate loc (* extras *) pname)
        )
        | Unlock _ -> (
          F.printf "Function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
          F.printf "unlock at line %a\n" Location.pp loc;
          get_path actuals
          |> Option.value_map ~default:astate ~f:(fun path -> Domain.release path astate loc (* extras *) pname)
        )
        (* TODO try_lock *)
        | NoEffect -> (
          F.printf "User defined function %a at line %a\n" Procname.pp callee_pname Location.pp loc;
          Domain.print_astate astate loc pname;
          analyze_dependency callee_pname
          |> Option.value_map ~default:(astate) ~f:(
            fun (_, summary) ->
              let callee_formals =
                match AnalysisCallbacks.proc_resolve_attributes callee_pname with
                | Some callee_attr -> callee_attr.ProcAttributes.formals
                | None -> []
              in
              Domain.integrate_summary astate callee_pname loc summary callee_formals actuals pname
          )
        )
        | _ ->
          F.printf "Function that probably should not be here %a at line %a\n" Procname.pp callee_pname Location.pp loc;
          astate
      end
  )
  (* END LOCKS *)
  | Assign (lhs_access_expr, rhs_exp, loc) ->
    F.printf "Assigning expression...\n";
    Domain.print_astate astate loc pname;
    assign_expr lhs_access_expr rhs_exp loc analysis_data astate pname
  | _ -> (
    F.printf "DarcChecker: Another something function than threads etc.call\n";
    astate (* integrate summary? *)
  )
  let pp_session_name _node fmt = F.pp_print_string fmt "darc" (* checker name in the debug html *)
end

(** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to ignore them *)
module CFG = ProcCfg.Normal

(* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))

(* COMPUTE THE RESULT AND REPORT ERRORS *)
let report {InterproceduralAnalysis.proc_desc; err_log; _} post =
  F.printf "REPORTING AND COMPUTING??? ----------------------------------------";
  let _idk = Domain.compute_data_races post in
  let last_loc = Procdesc.Node.get_loc (Procdesc.get_exit_node proc_desc) in
  let message = F.asprintf "Number of printf: %a in Data Race Checker\n" DarcDomain.pp post in
  Reporting.log_issue proc_desc err_log ~loc:last_loc DarcChecker IssueType.darc_error message;;

(** Main function into the checker--registered in RegisterCheckers *)
let checker ({InterproceduralAnalysis.proc_desc; tenv=_; err_log=_} as interproc) =
  let data = {interproc; extras = 0} in
  F.printf "Hello from Darc Checker.\n";
  F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s START >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));

  (* If the analysed function is main -> we need to do few changes -> add main thread to threads... *)

  (* vytvorime list vars_declared, ktery pak posleme do inicializace astate *)
  let vars_declared_ref = ref [] in


let print_vars_declared vars =
  F.printf "darc_vars_declared: {";
  let rec print_vars = function
    | [] -> F.printf "}\n"
    (* | hd :: tl -> F.printf "%a, " HilExp.AccessExpression.pp hd; print_vars tl *)
    | hd :: tl ->
      let typ_string = Typ.to_string (snd hd) in
      F.printf "|(%a, %s)|" Mangled.pp (fst hd) typ_string; print_vars tl
  in
  print_vars vars
  in

  (* a pridame do nej formals passed by value + lokalni promenne (TODO na to pozor - opravdu je vsechny muzu pridat rovnou uz ted? asi jo,
     pokud se pak vytvori vlakno, tak pokud nejaka promenna byla poslana dal, tak ji ze seznamu odstranime (pozor ale -> jak poslana dal?
     dana do struktury, ktera je pak predana do vlakna?)) *)
  (* locals deklarovane v dane funkci: *)
  let locals = Procdesc.get_locals proc_desc in
  let print_locals =
    F.printf "locals: {";
    let rec print : ProcAttributes.var_data list -> unit = function
      | [] -> F.printf "}\n"
      | hd :: tl ->
        F.printf "%a, " Mangled.pp hd.name;
        let new_local = (hd.name, hd.typ) in
        vars_declared_ref := new_local :: !vars_declared_ref;
        print tl (* da se vytisknout i Typ.t atd. *)
    in
    print locals
  in
  print_locals;

  (* formals dane funkce: *)
  let formals = Procdesc.get_formals proc_desc in
  let print_formals =
    F.printf "formals: {";
    let rec print : (Mangled.t * Typ.t) list -> unit = function
      | [] -> F.printf "}\n"
      | hd :: tl ->
        (* F.printf "%a, " Mangled.pp (fst hd); *)
        let typ_string = Typ.to_string (snd hd) in
          (* F.printf "typ: %s\n" (Typ.to_string typ); *)
          let _is_ptr =
            (* if typ is not a pointer, add the variable to vars_declared list *)
            if not (Typ.is_pointer (snd hd)) then
              vars_declared_ref := hd :: !vars_declared_ref
            in
            F.printf "| (%a," IR.Mangled.pp (fst hd); F.printf " %s) |" typ_string;
            print_vars_declared !vars_declared_ref;
        print tl
    in
    print formals
  in
  print_formals;

  let vars_declared = !vars_declared_ref in

  (* zF.printf "Procdesc: %a\n" Procdesc.pp proc_desc;*)
  let init_astate : DarcDomain.t =
    if (phys_equal (String.compare (Procname.to_string (Procdesc.get_proc_name proc_desc)) "main") 0) then
      begin
        DarcDomain.initial_main vars_declared
      end
    else
      begin
        DarcDomain.empty_with_vars vars_declared
      end
    in
    let result = Analyzer.compute_post data ~initial:init_astate proc_desc in
    if (phys_equal (String.compare (Procname.to_string (Procdesc.get_proc_name proc_desc)) "main") 0) then
      (* maybe this is not okay *)
      (* computing the result *)
      (* Option.iter result ~f:(fun post -> report_if_printf interproc post); *)
      Option.iter result ~f:(fun post -> report interproc post);
      F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s END >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));
      result