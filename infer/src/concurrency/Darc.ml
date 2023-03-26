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
  random_int: int;
}

let initial_extras =
{
  last_loc = Location.dummy;
  heap_tmp = [];
  random_int = 0;
}

type analysis_data = {interproc: DarcDomain.summary InterproceduralAnalysis.t; extras : extras_t ref}

let _assign_expr lhs_access_expr rhs_expr loc (astate : Domain.t) pname =
  F.printf "Access lhs: %a at %a\n" HilExp.AccessExpression.pp lhs_access_expr Location.pp loc;
  let lhs_access_path = HilExp.AccessExpression.to_access_path lhs_access_expr in
  F.printf "Access lhs access path: %a at %a\n" AccessPath.pp lhs_access_path Location.pp loc;
  let get_base (a, _) = a in
  let get_access_list (_, b) = b in
  let lhs_base = get_base (lhs_access_path) in
  let lhs_access_list = get_access_list (lhs_access_path) in
  let _lhs_accesses = HilExp.AccessExpression.to_accesses lhs_access_expr in
  F.printf "AccessPath: pp: |%a|, pp_base: |%a|, pp_access: , pp_access_list: |%a|\n" AccessPath.pp lhs_access_path AccessPath.pp_base lhs_base AccessPath.pp_access_list lhs_access_list;
  (* access expression type: *)
  let new_astate = Domain.assign_expr lhs_access_expr astate loc pname Domain.ReadWriteModels.Write in
  let rhs_access_expr = HilExp.get_access_exprs rhs_expr in
  let rhs_access_expr_first = List.hd rhs_access_expr in
  match rhs_access_expr_first with
  | Some rhs_access_expr_some ->
    (* add rhs expression (transformed with an alias if any) to accesses, then add alias *)
    (* add rhs expr *)
      (* find rhs in expr and nahrad ho pokud tam je *)
    (* let new_astate_with_rhs = Domain.add_rhs_expr_to_accesses rhs_access_expr_some new_astate loc pname in *)
    let new_astate_with_rhs = Domain.assign_expr rhs_access_expr_some new_astate loc pname Domain.ReadWriteModels.Read in
    (* update aliases *)
    let astate_with_updated_aliases = Domain.update_aliases lhs_access_expr rhs_access_expr_some new_astate_with_rhs in
    (* TODO nepridavam rhs expressions do accesses!!! *)
    (* add rhs to accesses, implicitly Read, jinak je funkce stejna jako Domain.assign_expr pro lhs! *)
    F.printf "Some in Darc.assign_expr - rhs_access_expr_some: %a\n" HilExp.AccessExpression.pp rhs_access_expr_some;
    astate_with_updated_aliases
  | None -> (
    F.printf "None in Darc.assign_expr - rhs_access_expr_some\n";
    new_astate
  )

let handle_free hil_actuals astate =
  (* get actuals - prvni z nich je LOAD alias toho, co se ma odstranit z heap_aliases *)
  let hil_actuals_first = List.hd hil_actuals in
  match hil_actuals_first with
  | None -> (
    F.printf "None\n";
    astate
  )
  | Some HilExp.AccessExpression actual -> (
    F.printf "Some actual=%a\n" HilExp.AccessExpression.pp actual;
    (* find actual in load aliases *)
    Domain.remove_heap_aliases_when_free actual astate
  )
  | Some _ -> (
    F.printf "Some actual=other type\n";
    astate
  )

module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  type nonrec analysis_data = analysis_data

  (* READ access handle_load tenv id e typ ~lhs:(Var.of_id id, typ) loc astate *)
  let handle_load _tenv id e typ ~lhs loc (astate : Domain.t) pname =
    F.printf "handle_load...\n";
    let lhs_var = fst lhs in
    let add_deref = match (lhs_var : Var.t) with LogicalVar _ -> (F.printf "%a je LogicalVar\n" Var.pp lhs_var; true) | ProgramVar _ -> (F.printf "%a je ProgramVar\n" Var.pp lhs_var; false) in
    F.printf "e_hil_exp: ";
    let e_hil_exp = Domain.transform_sil_expr_to_hil e typ add_deref in
    F.printf "\n";
    match e_hil_exp with
    | HilExp.AccessExpression e_ae -> (
      F.printf "e_hil_exp: access expression\n";
      let id_ae = HilExp.AccessExpression.of_id id typ in
      Domain.load id_ae e_ae e typ loc astate pname
    )
    | _ -> (
      F.printf "e_hil_exp: other\n";
      astate
    )

let handle_store_after_malloc e1 typ e2 loc astate (extras : extras_t ref) pname =
  F.printf "random_foo\n";
  let add_deref_e1 =
    match e1 with
    (* TODO asi to neni uplne spravne *)
    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> true
    | Exp.Var _ | _ -> false
  in
  F.printf "e1_hil: ";
  let e1_hil = Domain.transform_sil_expr_to_hil e1 typ add_deref_e1 in
  F.printf "\n";
    match e1_hil with
    | AccessExpression e1_ae -> (
      (* transform e2 *)
      let add_deref_e2 = false
              in
      (* if e2 is Cast (e.g. in malloc), get only the cast_exp, e.g. n$0 *)
      let e2_exp =
        match e2 with
        | Exp.Cast (_, cast_exp) -> cast_exp
        | _ -> e2
      in
      F.printf "e2_hil: ";
      let e2_hil = Domain.transform_sil_expr_to_hil e2_exp typ add_deref_e2 in
      F.printf "\n";
      match e2_hil with
      | AccessExpression e2_ae -> (
        let (astate_with_new_access_and_heap_alias, updated_heap_tmp) = Domain.add_heap_alias_when_malloc e1_ae e2_ae loc astate !(extras).heap_tmp pname in
        extras := { !(extras) with heap_tmp=updated_heap_tmp };
        astate_with_new_access_and_heap_alias
      )
      | _ -> astate
    )
    | _ -> astate (* TODO *)

  let handle_store e1 typ e2 loc astate pname (extras : extras_t ref)  =
   F.printf "handle_store -------------\n";
   match !(extras).heap_tmp with
   | [] -> (* basic store *)
     Domain.store e1 typ e2 loc astate pname
   | _ -> ( (* if neco je v extras, then handle heap_store else below *)
(*     Domain.store_with_heap_alloc e1 typ e2 loc astate pname heap_tmp_list*)
     handle_store_after_malloc e1 typ e2 loc astate extras pname
   )

  let handle_pthread_create callee_pname pname loc actuals sil_actual_argument analyze_dependency astate =
    F.printf "DarcChecker: Pthread_create function call %s at %a\n" (Procname.to_string callee_pname) Location.pp loc;
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

(* TODO handle also return expression *)
  let handle_pthread_join callee_pname loc actuals astate =
    F.printf "DarcChecker: pthread_join function call %s at %a\n" (Procname.to_string callee_pname) Location.pp loc;
    match List.nth actuals 0 with
    | Some HilExp.AccessExpression th_ae -> Domain.remove_thread th_ae astate
    | _ -> astate

  let clear_load_aliases_if_new_loc astate (last_loc : Location.t) (loc : Location.t) =
    if (loc.line > last_loc.line) then
      begin
(*        F.printf "loc is larger than last_loc -> clearing\n";*)
        Domain.astate_with_clear_load_aliases astate
      end
    else
      begin
(*        F.printf "loc is not larger than last_loc -> not clearing\n";*)
        astate
      end

  (** Take an abstract state and instruction, produce a new abstract state *)
  let exec_instr (astate : Domain.t) ({interproc= {proc_desc; tenv; analyze_dependency}} as analysis_data) _ _ instr =
    F.printf "\n";
    let pname = Procdesc.get_proc_name proc_desc in
    match (instr : Sil.instr) with
    | Load {id; e; typ; loc} -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* compute whatever you need to compute *)
      F.printf "Load: id=%a, e=%a on %a...\n" Ident.pp id Exp.pp e Location.pp loc;
      F.printf "e: ";
            let _print_e =
            match e with
            | Var var -> F.printf "Var %a\n" Ident.pp var
            | UnOp _ -> F.printf "UnOp\n" (* of Unop.t * t * Typ.t option  (** Unary operator with type of the result if known *) *)
            | BinOp _ -> F.printf "BinOp\n" (* of Binop.t * t * t  (** Binary operator *) *)
            | Exn _exn -> F.printf "Exn\n" (* of t  (** Exception *) *)
            | Closure closure ->  F.printf "Closure %a\n" Exp.pp_closure closure (* of closure  (** Anonymous function *) *)
            | Const _const -> F.printf "Const\n" (* Const.pp const  (** Constants *)*)
            | Cast _ -> F.printf "Cast\n" (* of Typ.t * t  (** Type cast *) *)
            | Lvar lvar -> F.printf "Lvar %a\n" Pvar.pp_value lvar (** The address of a program variable *)
            | Lfield (exp, fieldname, _typ) -> F.printf "Lfield exp: %a fieldname: %a\n" Exp.pp exp Fieldname.pp fieldname (* of t * Fieldname.t * Typ.t *)
                  (** A field offset, the type is the surrounding struct type *)
            | Lindex _ -> F.printf "Lindex\n" (* )of t * t  (** An array index offset: [exp1\[exp2\]] *) *)
            | Sizeof _ -> F.printf "Sizeof\n" (*  sizeof_data *)
            in
      (* compute the result (add new access, load_aliases etc.) *)
      let result = handle_load tenv id e typ ~lhs:(Var.of_id id, typ) loc astate pname in
      (* update last_loc *)
      analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp = !(analysis_data.extras).heap_tmp };
      result
    )
    | Store {e1; typ; e2; loc} -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* compute whatever you need to compute *)
      F.printf "Store: e1=%a, e2=%a on %a: " Exp.pp e1 Exp.pp e2 Location.pp loc;
      F.printf "e1: ";
      let _print_e1 =
      match e1 with
      | Var var -> F.printf "Var %a\n" Ident.pp var
      | UnOp _ -> F.printf "UnOp\n" (* of Unop.t * t * Typ.t option  (** Unary operator with type of the result if known *) *)
      | BinOp _ -> F.printf "BinOp\n" (* of Binop.t * t * t  (** Binary operator *) *)
      | Exn _exn -> F.printf "Exn\n" (* of t  (** Exception *) *)
      | Closure closure ->  F.printf "Closure %a\n" Exp.pp_closure closure (* of closure  (** Anonymous function *) *)
      | Const _const -> F.printf "Const\n" (* Const.pp const  (** Constants *)*)
      | Cast _ -> F.printf "Cast\n" (* of Typ.t * t  (** Type cast *) *)
      | Lvar lvar -> F.printf "Lvar %a\n" Pvar.pp_value lvar  (** The address of a program variable *)
      | Lfield (exp, fieldname, _typ) -> F.printf "Lfield exp: %a fieldname: %a\n" Exp.pp exp Fieldname.pp fieldname (* of t * Fieldname.t * Typ.t *)
            (** A field offset, the type is the surrounding struct type *)
      | Lindex _ -> F.printf "Lindex\n" (* )of t * t  (** An array index offset: [exp1\[exp2\]] *) *)
      | Sizeof _ -> F.printf "Sizeof\n" (*  sizeof_data *)
      in
      F.printf "e2: ";
      let _print_e2 =
          match e2 with
          | Var var -> F.printf "Var %a\n" Ident.pp var
          | UnOp _ -> F.printf "UnOp\n" (* of Unop.t * t * Typ.t option  (** Unary operator with type of the result if known *) *)
          | BinOp _ -> F.printf "BinOp\n" (* of Binop.t * t * t  (** Binary operator *) *)
          | Exn _exn -> F.printf "Exn\n" (* of t  (** Exception *) *)
          | Closure closure ->  F.printf "Closure %a\n" Exp.pp_closure closure (* of closure  (** Anonymous function *) *)
          | Const _const -> F.printf "Const\n" (* Const.pp const  (** Constants *)*)
          | Cast (_, cast_exp) -> F.printf "Cast %a\n" Exp.pp cast_exp (* of Typ.t * t  (** Type cast *) *)
          | Lvar lvar -> F.printf "Lvar %a\n" Pvar.pp_value lvar  (** The address of a program variable *)
          | Lfield _ -> F.printf "Lfield\n" (* of t * Fieldname.t * Typ.t *)
                (** A field offset, the type is the surrounding struct type *)
          | Lindex _ -> F.printf "Lindex\n" (* )of t * t  (** An array index offset: [exp1\[exp2\]] *) *)
          | Sizeof _ -> F.printf "Sizeof\n" (*  sizeof_data *)
        in
(*      F.printf "hil_expr1: ";*)
(*      (* TODO nemuzu davat vzdy true, protoze pokud je na lhs napr. *p, prevede se to na n$7 a pak mam po dereferenci *n$7 *)*)
(*      let e1_hil = Domain.transform_sil_expr_to_hil e1 typ true in*)
(*      F.printf "hil_expr2: ";*)
(*      let e2_hil = Domain.transform_sil_expr_to_hil e2 typ false in*)
(*      F.printf "\n";*)
(*      match e1_hil with*)
(*      | AccessExpression e1_hil_ae -> handle_store e1_hil_ae e2_hil loc astate pname*)
(*      | _ -> astate*)

      (* compute the result (add new access, load_aliases etc.) *)
      let result = handle_store e1 typ e2 loc astate pname analysis_data.extras in
      (* update last_loc AND CLEAR HEAP_TMP *)
      analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp = [] };
(*      let result_malloc = random_foo e1 typ e2 astate analysis_data.extras in*)
      F.printf "ahojky\n";
      result
    )
    | Prune  (exp, loc, then_branch, _if_kind) -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* compute whatever you need to compute *)
      (* what exp is? *)
      F.printf "hil_exp: ";
      let hil_exp = Domain.transform_sil_expr_to_hil exp StdTyp.boolean false in
      F.printf "\n";
      F.printf "prune hil_exp:%a\n" HilExp.pp hil_exp;
      (* update last_loc *)
      analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp = !(analysis_data.extras).heap_tmp };
      let result =
        if (then_branch) then
          begin
            F.printf "Prune if on %a...\n" Location.pp loc;
            (* compute astate for if branch TODO *)
            astate
          end
        else
          begin
            F.printf "Prune then on %a...\n" Location.pp loc;
            (* compute astate for else branch TODO *)
            astate
          end
      in
      F.printf "PRUNE ASTATE: \n";
      Domain.print_astate result;
      result
    )
    | Call ((ret_id, ret_typ), Const (Cfun callee_pname), sil_actuals, loc, call_flags) -> (
      (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
      let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in
      (* compute whatever you need to compute *)
      F.printf "Call %a on %a: ret_id: %a, ret_typ: %s, call_flags: %a\n" Procname.pp callee_pname Location.pp loc Ident.pp ret_id (Typ.to_string ret_typ) CallFlags.pp call_flags;
      let hil_actuals = Domain.transform_sil_exprs_to_hil_list sil_actuals (* TODO add_deref:false? *) false in
      if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_create") 0) then
        let sil_actual_argument = List.nth sil_actuals 3 in (* variable passed to the function *)
        match sil_actual_argument with
        | None -> astate
        | Some sil_actual -> (
          let result = handle_pthread_create callee_pname pname loc hil_actuals sil_actual analyze_dependency astate in
          analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp = !(analysis_data.extras).heap_tmp };
          result
        )
      else if (phys_equal (String.compare (Procname.to_string callee_pname) "pthread_join") 0) then
        let result = handle_pthread_join callee_pname loc hil_actuals astate in
        analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp = !(analysis_data.extras).heap_tmp };
        result
      else if (phys_equal (String.compare (Procname.to_string callee_pname) "malloc") 0)
        || (phys_equal (String.compare (Procname.to_string callee_pname) "calloc") 0) then
        (* TODO nahradit za malloc, calloc, realloc? atd. - neexistuje nejaka funkce is_dynamically_allocated? *)
        (* add (ret_id, loc) to extras.heap_tmp *)
        let ret_id_ae = HilExp.AccessExpression.of_id ret_id ret_typ in
        let new_heap_tmp = (ret_id_ae, loc) in
        let heap_tmp = new_heap_tmp :: !(analysis_data.extras).heap_tmp in
        analysis_data.extras := { last_loc = loc; random_int = !(analysis_data.extras).random_int; heap_tmp };
        astate
      else if (phys_equal (String.compare (Procname.to_string callee_pname) "free") 0) then
        (* free odstrani z heap_aliases to, co je v argumentu te funkce + vsechno se stejnym loc *)
        handle_free hil_actuals astate
      else
        begin
         (* LOCKS *)
         match ConcurrencyModels.get_lock_effect callee_pname hil_actuals with
               | Lock _ -> (
                 (* lock(l1) *)
                 F.printf "Function %a at %a\n" Procname.pp callee_pname Location.pp loc;
                 F.printf "lock at %a\n" Location.pp loc;
                 Domain.print_astate astate (* loc pname*);
                 let result =
                   (* pthread_mutex_lock(mutex) - one argument *)
                   match hil_actuals with
                   | actual :: [] -> Domain.acquire_lock actual astate loc
                   | _ -> astate (* FIXME *)
                 in
                 analysis_data.extras := { !(analysis_data.extras) with last_loc = loc };
                 result
               )
               | Unlock _ -> (
                 F.printf "Function %a at %a\n" Procname.pp callee_pname Location.pp loc;
                 F.printf "unlock at %a\n" Location.pp loc;
                 Domain.print_astate astate (* loc pname*);
                 let result =
                   (* pthread_mutex_unlock(mutex) - one argument *)
                   match hil_actuals with
                   | actual :: [] -> Domain.release_lock actual astate loc
                   | _ -> astate (* shouldn't happen *)
                 in
                 analysis_data.extras := { !(analysis_data.extras) with last_loc = loc };
                 result
               )
               (* TODO try_lock *)
               | NoEffect -> (
                 F.printf "User defined function %a at %a\n" Procname.pp callee_pname Location.pp loc;
                 Domain.print_astate astate (* loc pname*);
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
               | _ ->
                 F.printf "Function that probably should not be here %a at %a\n" Procname.pp callee_pname Location.pp loc;
                 astate
             end
  )
  | Call _ -> (
    (* check if loc is larger than last_loc -> if true, clear load_aliases set *)
    (* let astate = clear_load_aliases_if_new_loc astate !(analysis_data.extras).last_loc loc in *)
    (* compute whatever you need to compute *)
    F.printf "Call - TODO...\n";
    astate
    (* TODO update last_loc *)
  )
  | Metadata _ -> astate

  let pp_session_name _node fmt = F.pp_print_string fmt "darc" (* checker name in the debug html *)
end


(* function adds all locals to the locals list *)
let add_locals_to_list locals lst_ref pname =
  F.printf "locals...\n";
  let rec loop : ProcAttributes.var_data list -> unit = function
    | [] -> ()
    | var :: tl ->
      (* add the variable to the locals list *)
      F.printf "%a | \n" Mangled.pp (var.name);
      let pvar_mk = Pvar.mk var.name pname in
      let access_path_base = AccessPath.base_of_pvar pvar_mk var.typ in
      let ae = HilExp.AccessExpression.base access_path_base in
      F.printf "ae: %a\n" HilExp.AccessExpression.pp ae;
      lst_ref := ae :: !lst_ref;
      loop tl
  in
  loop locals

(* function adds non-pointer formals to the locals list *)
let add_nonpointer_formals_to_list formals lst_ref pname =
  (* TODO predelat na access_expressions!!! *)
  F.printf "formals...\n";
  let rec loop : (Mangled.t * Typ.t) list -> unit = function
    | [] -> ()
    | var :: tl ->
      (* create access expression from var *)
      let var_pvar = Pvar.mk (fst var) pname in
      let var_base = AccessPath.base_of_pvar var_pvar (snd var) in
      let var_base_ae = HilExp.AccessExpression.base var_base in
      (* if typ is not a pointer, add the variable to locals list *)
      if not (Typ.is_pointer (snd var)) then
        lst_ref := var_base_ae :: !lst_ref;

      F.printf "%a | \n" Mangled.pp (fst var);
      loop tl
  in
  loop formals

let add_formal_to_heap_aliases formal heap_aliases pname =
  (* (Mangled.t * Typ.t) -> HilExp.AccessExpression.t formal *)
  let formal_pvar = Pvar.mk (fst formal) pname in
  let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
  let formal_ae = HilExp.AccessExpression.base formal_access_path_base in
  (* make dummy Location *)
  let loc_dummy = Location.dummy in
  (* add formal to the list *)
  let new_heap_aliases = (formal_ae, loc_dummy) :: heap_aliases in
  new_heap_aliases

let add_formals_to_heap_aliases astate formals pname =
  let rec add_each_formal_to_heap_aliases formals_lst heap_aliases_lst =
    match formals_lst with
    | [] -> heap_aliases_lst
    | formal :: t -> (
      let updated_heap_aliases_lst = add_formal_to_heap_aliases formal heap_aliases_lst pname in
      add_each_formal_to_heap_aliases t updated_heap_aliases_lst
    )
  in
  let heap_aliases_with_formals = add_each_formal_to_heap_aliases formals [] in
  Domain.add_heap_aliases_to_astate astate heap_aliases_with_formals

(** 5(a) Type of CFG to analyze--Exceptional to follow exceptional control-flow edges, Normal to ignore them *)
(*module CFG = ProcCfg.Normal*)

(* Create an intraprocedural abstract interpreter from the transfer functions we defined *)
(*module Analyzer = LowerHil.MakeAbstractInterpreter (TransferFunctions (CFG))*)
module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (ProcCfg.Normal))

(* COMPUTE THE RESULT AND REPORT ERRORS *)
let report {InterproceduralAnalysis.proc_desc; err_log; _} post =
  F.printf "REPORTING AND COMPUTING ----------------------------------------";
  let data_races_list = (Domain.compute_data_races post) in
  let rec report_all_data_races lst =
    match lst with
    | [] -> ()
    | (fst, snd) :: t -> (
      let fst_message = F.asprintf "Data race between \t%a\n\t\t\t%a\n" DarcDomain.AccessEvent.pp_report_short fst DarcDomain.AccessEvent.pp_report_short snd in
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
  F.printf "Hello from Darc Checker.\n";
  F.printf "\n\n<<<<<<<<<<<<<<<<<<<< Darc: function %s START >>>>>>>>>>>>>>>>>>>>>>>>\n\n" (Procname.to_string (Procdesc.get_proc_name proc_desc));

  (* create a list of locals and add all the locals and non-pointer formals to the list *)
  let locals = ref [] in
  let proc_desc_locals = Procdesc.get_locals proc_desc in   (* locals declared in the function *)
  add_locals_to_list proc_desc_locals locals pname;
  let formals = Procdesc.get_formals proc_desc in (* formals of the function *)
  add_nonpointer_formals_to_list formals locals pname;

  (* If the analysed function is main -> we need to do few changes -> add main thread to threads... *)
  let init_astate : DarcDomain.t =
    if (phys_equal (String.compare (Procname.to_string (Procdesc.get_proc_name proc_desc)) "main") 0) then
      DarcDomain.initial_main !locals
    else
      DarcDomain.empty_with_locals !locals
    in
    (* add formals to heap_aliases *)
    let init_astate = add_formals_to_heap_aliases init_astate formals pname in
    (* compute function summary *)
    let result = Analyzer.compute_post data ~initial:init_astate proc_desc in
    F.printf "Domain.print_astate:\n";
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