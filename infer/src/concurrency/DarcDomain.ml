(*
 * Author: Lucie Svobodová (xsvobo1x@stud.fit.vutbr.cz), 2022-present
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Faculty of Information Technology, Brno University of Technology, CZ
 *)
 (* Data Race Checker Domain *)

open! IStd
module F = Format
module LockEvent = DeadlockDomain.LockEvent
module Lockset = DeadlockDomain.Lockset

(* module used for dealing with threads *)
module ThreadEvent = struct
  (* type of ThreadEvent *)
  type t = (HilExp.AccessExpression.t * Location.t * Bool.t)

  (* compare function *)
  let compare (th, loc, created_in_loop) (th', loc', created_in_loop') =
    match HilExp.AccessExpression.equal th th' with
    | false -> HilExp.AccessExpression.compare th th'
    | true ->
      match Location.equal loc loc' with
      | false -> Location.compare loc loc'
      | true -> Bool.compare created_in_loop created_in_loop'

  (* function creates a main thread *)
  let create_main_thread =
    let pname = Procname.from_string_c_fun "main" in
    let pvar_from_pname : Pvar.t = Pvar.mk_tmp "'main_thread'" pname in
    let tvar_name = Typ.TVar "thread" in
    let typ_main_thread = Typ.mk tvar_name in
    let acc_path_from_pvar : AccessPath.base = AccessPath.base_of_pvar pvar_from_pname typ_main_thread in
    let thread_ae = HilExp.AccessExpression.base acc_path_from_pvar in
    (thread_ae, Location.dummy, false)

  (* function returns true if thread name equals var and thread flag equals flag *)
  let var_and_flag_equal (th, _, (th_flag : bool)) var (flag : bool) =
    HilExp.AccessExpression.equal th var && phys_equal th_flag flag

  (* pretty print function *)
  let pp fmt ((th, (loc : Location.t), created_in_loop) as thread) =
    let loc_str =
      match Location.equal loc Location.dummy with
      | true -> ""
      | false -> " created on line " ^ (string_of_int (loc.line))
    in
    let in_loop_str =
      match created_in_loop with
      | true -> " in loop"
      | false -> ""
    in
    match compare thread create_main_thread with
    | 0 -> F.fprintf fmt "main thread"
    | _ -> F.fprintf fmt "%a%s%s" HilExp.AccessExpression.pp th loc_str in_loop_str
end
(* set of ThreadEvent.t elements *)
module ThreadSet = AbstractDomain.FiniteSet(ThreadEvent)

(* module used for handling points to relations *)
module PointsTo = struct
  (* type of PointsTo *)
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t)

  (* compare function *)
  let compare t1 t2 =
    let fst_compare = HilExp.AccessExpression.compare (fst t1) (fst t2) in
    let snd_compare = HilExp.AccessExpression.compare (snd t1) (snd t2) in
    if not (Int.equal fst_compare 0) then fst_compare
    else snd_compare

  (* function returns true if the the first var of the points-to tuple does not equal var *)
  let fst_not_equals_var (fst, _) var =
    not (HilExp.AccessExpression.equal fst var)

  (* pretty print function *)
  let pp fmt (f, s) =
    F.fprintf fmt "(%a, %a)" HilExp.AccessExpression.pp f HilExp.AccessExpression.pp s
end
(* set of PointsTo.t elements *)
module PointsToSet = AbstractDomain.FiniteSet(PointsTo)

(* module used for handling the heap points-to relation *)
module HeapPointsTo = struct
  (* type of heap points-to relation *)
  (* note: the bool is not used yet, it is prepared for handling memory allocation in loops *)
  type t = (HilExp.AccessExpression.t * Location.t * Bool.t)

  (* function compares two heap points-to relations *)
  let compare (var, loc, created_in_loop) (var', loc', created_in_loop') =
    match HilExp.AccessExpression.equal var var' with
    | false -> HilExp.AccessExpression.compare var var'
    | true ->
      match Location.equal loc loc' with
      | false -> Location.compare loc loc'
      | true -> Bool.compare created_in_loop created_in_loop'

  (* function returns true if the variable in the points-to relation
     does not equal the variable var *)
  let fst_not_equals_var (fst, _, _) var =
    not (HilExp.AccessExpression.equal fst var)

  (* function returns true if the location where the variable in the heap points-to
     relation points to does not equal the location loc *)
  let loc_not_equals (_, ha_loc, _) loc =
    not (Location.equal ha_loc loc)

  (* pretty print function *)
  let pp fmt (ae, loc, created_in_loop) =
    F.fprintf fmt "(%a, %a, %b)" HilExp.AccessExpression.pp ae Location.pp loc created_in_loop

  (* function returns true if the loc is greater than zero *)
  let loc_greater_than_0 (_, (loc : Location.t), _) =
    loc.line > 0
end
(* set of HeapPointsTo.t elements *)
module HeapPointsToSet = AbstractDomain.FiniteSet(HeapPointsTo)

(* module used for handling load aliases *)
module LoadAlias = struct
  (* type of LoadAlias (e.g. (n$1, var, line 10) *)
  (* note: the Location.t is not currently used, it can be used for experiments with optimisation *)
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t * Location.t)

  (* compare function *)
  let compare (ae1, ae2, _) (ae1', ae2', _) =
    let fst_compare = HilExp.AccessExpression.compare ae1 ae1' in
    let snd_compare = HilExp.AccessExpression.compare ae2 ae2' in
    if not (Int.equal fst_compare 0) then fst_compare
    else snd_compare

  (* function returns true id the line of the location in the load alias in lower than or equal to max *)
  (* used when experimenting with for optimisation  *)
  let _loc_leq_than_max (_, _, (loc : Location.t)) max =
     loc.line <= max

  (* pretty print function *)
  let pp fmt (f, s, loc) =
    F.fprintf fmt "(%a, %a, %a)" HilExp.AccessExpression.pp f HilExp.AccessExpression.pp s Location.pp loc
end
(* set of LoadAlias.t elements *)
module LoadAliasesSet = AbstractDomain.FiniteSet(LoadAlias)

(* module defining the types of accesses *)
module ReadWriteModels = struct
  (* type of ReadWriteModels *)
  type t = Read | Write

  (* compare function *)
  let compare at1 at2 =
    if phys_equal at1 Write && phys_equal at2 Write then 0
    else if phys_equal at1 Read && phys_equal at2 Read then 0
    else if phys_equal at1 Write && phys_equal at2 Read then 1
    else -1

  (* function returns access type as a string *)
  let access_to_string access_type =
    match access_type with
    | Read  -> "read"
    | Write -> "write"

  let to_report_string access_type =
    match access_type with
    | Read -> "read from"
    | Write -> "write to"
end

(* function replaces location in threads from callee_summary that weren't known before (they have dummy location) *)
let replace_unknown_threads_with_actuals astate_threads_active astate_threads_joined callee_summary_threads_active
                                                                                         callee_summary_threads_joined =
  let callee_threads_joined = ThreadSet.elements callee_summary_threads_joined in
  let rec find_and_replace lst acc =
    match lst with
    | [] -> acc
    | ((th, loc, flag) as thread):: t -> (
      (* if the location equals dummy location (line number: -1), try to find the real thread *)
      if Location.equal loc Location.dummy then
        let thread_updated =
          (* in threads active from the current abstract state *)
          let thread_from_astate = ThreadSet.find_first_opt (fun elt -> ThreadEvent.var_and_flag_equal elt th flag)
                                                                                                astate_threads_active in
          match thread_from_astate with
          | Some thread_noopt -> thread_noopt
          | None -> (
            (* in threads joined from the current abstract state *)
            let thread_from_astate_joined = ThreadSet.find_first_opt (fun elt -> ThreadEvent.var_and_flag_equal elt th
                                                                                          flag) astate_threads_joined in
            match thread_from_astate_joined with
            | Some thread_joined_noopt -> thread_joined_noopt
            | None -> (
              (* in threads active from the callee summary *)
              let thread_from_callee_active = ThreadSet.find_first_opt (fun elt -> ThreadEvent.var_and_flag_equal elt th
                                                                                  flag) callee_summary_threads_active in
              match thread_from_callee_active with
              | Some thread_act_noopt -> thread_act_noopt
              | None -> thread
            )
          )
        in find_and_replace t (thread_updated :: acc)
      else find_and_replace t (thread :: acc)
    )
  in
  let callee_threads_joined_updated = ThreadSet.of_list (find_and_replace callee_threads_joined []) in
  (* F.printf "callee_threads_joined_updated: %a\n" ThreadSet.pp callee_threads_joined_updated; *)
  callee_threads_joined_updated

(* module used for dealing with accesses *)
module AccessEvent = struct
  (* type of AccessEvent *)
  type t =
  {
    var: HilExp.AccessExpression.t;
    loc: Location.t;
    access_type: ReadWriteModels.t;
    locked: Lockset.t;
    unlocked: Lockset.t;
    threads_active: ThreadSet.t;
    threads_joined: ThreadSet.t;
    thread: ThreadEvent.t option;
  }

  (* compare function *)
  let compare a1 a2 =
    let var_cmp = HilExp.AccessExpression.compare a1.var a2.var in
    let loc_cmp = Location.compare a1.loc a2.loc in
    let access_type_cmp = ReadWriteModels.compare a1.access_type a2.access_type in
    let locked_cmp = Lockset.compare a1.locked a2.locked in
    let unlocked_cmp = Lockset.compare a1.unlocked a2.unlocked in
    let threads_active_cmp = ThreadSet.compare a1.threads_active a2.threads_active in
    let threads_joined_cmp = ThreadSet.compare a1.threads_joined a2.threads_joined in
    let thread_cmp =
      match (a1.thread, a2.thread) with
      | (None, None) -> 0
      | (None, Some _) -> -1
      | (Some _, None) -> 1
      | (Some thread1, Some thread2) -> ThreadEvent.compare thread1 thread2
    in
    if not (Int.equal var_cmp 0) then var_cmp
    else if not (Int.equal access_type_cmp 0) then access_type_cmp
    else if not (Int.equal thread_cmp 0) then thread_cmp
    else if not (Int.equal threads_active_cmp 0) then threads_active_cmp
    else if not (Int.equal threads_joined_cmp 0) then threads_joined_cmp
    else if not (Int.equal locked_cmp 0) then locked_cmp
    else if not (Int.equal unlocked_cmp 0) then unlocked_cmp
    else loc_cmp

  (* pretty print *)
  let pp fmt t1 =
    F.fprintf fmt "{%a, %s, %a, " HilExp.AccessExpression.pp t1.var (ReadWriteModels.access_to_string t1.access_type)
                                                                                                Location.pp_line t1.loc;
    let _pp_thr =
      match t1.thread with
      | Some t -> F.fprintf fmt "thread %a\n" ThreadEvent.pp t;
      | None -> F.fprintf fmt "None thread\n";
    in
    F.fprintf fmt "threads: %a, \nthreads joined: %a\nlocks: %a\n}\n" ThreadSet.pp t1.threads_active ThreadSet.pp
                                                                                  t1.threads_joined Lockset.pp t1.locked

  (* pretty print function - shorter version used for reporting *)
  let pp_report_short fmt t1 =
    F.fprintf fmt "%s %a on %a on " (ReadWriteModels.to_report_string t1.access_type) HilExp.AccessExpression.pp t1.var
                                                                                                Location.pp_line t1.loc;
    match t1.thread with
    | Some t -> F.fprintf fmt "%a" ThreadEvent.pp t
    | None -> F.fprintf fmt "unknown thread"

  (* pretty print function - shorter version used for reporting *)
  let pp_report_long fmt t1 =
    F.fprintf fmt "%s %a on %a on " (ReadWriteModels.to_report_string t1.access_type) HilExp.AccessExpression.pp t1.var
                                                                                                Location.pp_line t1.loc;
    let _print_thread =
      match t1.thread with
      | Some t -> F.fprintf fmt "%a" ThreadEvent.pp t;
      | None -> F.fprintf fmt "unknown thread";
    in
    F.fprintf fmt "\nactive threads: %a\nlocks held: %a\n"
        ThreadSet.pp t1.threads_active Lockset.pp t1.locked

  (* function returns access.var *)
  let get_var access = access.var

  (* function returns access.loc *)
  let get_loc access = access.loc

  (* function returns access with updated locks and threads,
     and access with None thread updates with the thread in arguments *)
  let update_accesses_with_locks_and_threads threads_active threads_joined lockset unlockset thread
                                                                    callee_threads_active callee_threads_joined access =
    let locked = Lockset.diff (Lockset.union lockset access.locked) access.unlocked in
    let unlocked = Lockset.union (Lockset.diff unlockset access.locked) access.unlocked in
    let renamed_access_threads_joined = replace_unknown_threads_with_actuals threads_active threads_joined
                                                                          callee_threads_active callee_threads_joined in
    let threads_active = ThreadSet.diff (ThreadSet.union threads_active access.threads_active)
                                                                                        renamed_access_threads_joined in
    let threads_joined = ThreadSet.union threads_joined renamed_access_threads_joined in
    let thread =
      match access.thread with
      | None -> thread
      | Some th -> Some th
    in
    { var=access.var; loc=access.loc; access_type=access.access_type;
                                                              locked; unlocked; threads_active; threads_joined; thread }

  (* function replaces the base in var with actual,
     it must to be recursive to keep the same "format" as the original var was (e.g. **x, *x, &x) *)
  let rec replace_base_of_var_with_another_var var actual =
    match var with
    | HilExp.AccessExpression.Base _ -> (* v -> a *)
      actual
    | HilExp.AccessExpression.Dereference ae -> (* *( *v) -> *(...) *)
      HilExp.AccessExpression.dereference (replace_base_of_var_with_another_var ae actual)
    | HilExp.AccessExpression.AddressOf ae -> ( (* &( *v) -> &(...) *)
      let address_of_option = HilExp.AccessExpression.address_of (replace_base_of_var_with_another_var ae actual) in
      match address_of_option with
      | Some address_of -> address_of
      | None -> ae
    )
    | HilExp.AccessExpression.FieldOffset (ae, fieldname) -> (* v.ptr -> a.ptr *)
      HilExp.AccessExpression.field_offset (replace_base_of_var_with_another_var ae actual) fieldname
    | HilExp.AccessExpression.ArrayOffset (ae, typ, hilexp_option) -> (* v[...] -> a[...] *)
      HilExp.AccessExpression.array_offset (replace_base_of_var_with_another_var ae actual) typ hilexp_option

  (* function replaces the var in access by another var (actual), if the var equals formal *)
  let edit_access_with_actuals formal actual access =
    (* get base (as access_expression) of access.var and formal *)
    let access_var_base = HilExp.AccessExpression.get_base access.var in
    let access_var_base_ae = HilExp.AccessExpression.base access_var_base in
    let formal_base = HilExp.AccessExpression.get_base formal in
    let formal_base_ae = HilExp.AccessExpression.base formal_base in
    (* check if the bases of var and formal equal *)
    if HilExp.AccessExpression.equal access_var_base_ae formal_base_ae then
      match actual with
      | HilExp.AccessExpression actual_ae ->
        (* replace base of the var with actual *)
        let replaced_var = replace_base_of_var_with_another_var access.var actual_ae in
        { access with var=replaced_var }
      | _ -> access
    else  (* access.var is not replaced *)
      access

  (* function returns true if a1.loc is lower or equal than a2.loc *)
  let predicate_loc (a1, a2) =
    if Location.compare a1.loc a2.loc <= 0 then true else false

  (* function returns true if a1.thread != a2.thread *)
  let predicate_thread (a1, a2) =
    match (a1.thread, a2.thread) with
    | (Some t1, Some t2) -> if Int.equal (ThreadEvent.compare t1 t2) 0 then false else true
    | _ -> false

  (* function returns false if both accesses have read access type *)
  let predicate_read_write (a1, a2) = (* a1 == rd and a2 == rd -> false *)
    match (a1.access_type, a2.access_type) with
    | (ReadWriteModels.Read, ReadWriteModels.Read) -> false
    | _ -> true

  (* function returns true if there is at least one thread in the intersection of threads_active,
     and if at least one of the threads in the intersection is the thread on which an access occurred *)
  let predicate_threads_intersection (a1, a2) =
    let intersection = ThreadSet.inter a1.threads_active a2.threads_active in
    if (ThreadSet.cardinal intersection) > 1 then
      begin
        match (a1.thread, a2.thread) with
        | (Some a1_thread, Some a2_thread) ->
          (* there are more threads running concurrently
             -> check if any of these threads equals a1.thread or a2.thread *)
          (ThreadSet.mem a1_thread intersection) || (ThreadSet.mem a2_thread intersection)
        | _ -> false (* at least one of the threads is None *)
      end
    else
      false (* the only thread in the intersection is main -> data race cannot occur *)

  (* function returns true if the intersection of locked locks is empty *)
  let predicate_locksets (a1, a2) = (* intersect ls1 ls2 == {} -> false *)
    let intersect = Lockset.inter a1.locked a2.locked in
    if Lockset.equal intersect Lockset.empty then true else false

end
(* set of AccessEvent.t elements *)
module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

(* module for handling local variables *)
module Locals = struct
  (* type of Locals *)
  type t = HilExp.AccessExpression.t

  (* compare function *)
  let compare t1 t2 =
    HilExp.AccessExpression.compare t1 t2

  (* pretty print function *)
  let pp fmt t1 =
    F.fprintf fmt "%a" HilExp.AccessExpression.pp t1
end
(* set of Locals.t elements *)
module LocalsSet = AbstractDomain.FiniteSet(Locals)

(* type of DarC Domain *)
type t =
{
  threads_active: ThreadSet.t;
  threads_joined: ThreadSet.t;
  accesses: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  unlockset: Lockset.t;
  points_to: PointsToSet.t;
  heap_points_to: HeapPointsToSet.t;
  load_aliases: LoadAliasesSet.t;
  locals: LocalsSet.t;
}

(* empty type with locals *)
let empty_with_locals locals =
{
  threads_active = ThreadSet.empty;
  threads_joined = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  points_to = PointsToSet.empty;
  load_aliases = LoadAliasesSet.empty;
  heap_points_to = HeapPointsToSet.empty;
  locals;
}

(* function returns empty astate with main thread in threads_active and locals *)
let initial_main locals =
  let empty_astate = empty_with_locals locals in
  let main_thread = ThreadEvent.create_main_thread in
  (* add the main thread to an empty astate *)
  let threads_active = ThreadSet.add main_thread empty_astate.threads_active in
  { empty_astate with threads_active }

(* function prints the current abstract state *)
let print_astate astate  =
  F.printf "========= current abstract state... ==========\n";
  F.printf "access=%a\n" AccessSet.pp astate.accesses;
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "threads_joined=%a\n" ThreadSet.pp astate.threads_joined;
  F.printf "points_to=%a\n" PointsToSet.pp astate.points_to;
  F.printf "heap_points_to=%a\n" HeapPointsToSet.pp astate.heap_points_to;
  F.printf "load_aliases=%a\n" LoadAliasesSet.pp astate.load_aliases;
  F.printf "locals=%a\n" LocalsSet.pp astate.locals;
  F.printf "==============================================\n"


(* functions that handle aliases and points-to relations *)
(* function returns base of var as access expression type *)
let get_base_as_access_expression var =
  let var_base = HilExp.AccessExpression.get_base var in
  let var_base_ae = HilExp.AccessExpression.base var_base in
  var_base_ae

(* function returns Some alias if var participates in any alias in astate.points_to, or None,
   if add_deref is true, the second var in alias is returned as dereference *)
let rec find_alias var aliases ~add_deref =
  match aliases with
  | [] -> None
  | (fst, snd) :: t ->
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      match add_deref with
      | true -> Some (fst, HilExp.AccessExpression.dereference snd)
      | false -> Some (fst, snd)
    else
      find_alias var t ~add_deref

(* function returns alias from aliases list if any alias of var exists *)
let rec find_alias_list var aliases ~add_deref acc =
  match aliases with
  | [] -> acc
  | (fst, snd) :: t ->
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      let alias_to_add =
        match add_deref with
        | true -> (fst, HilExp.AccessExpression.dereference snd)
        | false -> (fst, snd)
      in
      find_alias_list var t ~add_deref (alias_to_add :: acc)
    else
      find_alias_list var t ~add_deref acc

(* function returns list of all aliases of var *)
let rec find_load_alias_list var aliases ~add_deref acc =
  match aliases with
  | [] -> acc
  | (fst, snd, loc) :: t ->
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      let alias_to_add =
        match add_deref with
        | true -> (fst, HilExp.AccessExpression.dereference snd, loc)
        | false -> (fst, snd, loc)
      in
      let load_alias_eq (a, b, _) (a', b', _) =
        HilExp.AccessExpression.equal a a' && HilExp.AccessExpression.equal b b'
      in
      let updated_acc =
        match List.mem acc alias_to_add ~equal:load_alias_eq with
        | false -> (alias_to_add :: acc)
        | true -> acc
      in
      find_load_alias_list var t ~add_deref updated_acc
    else
      find_load_alias_list var t ~add_deref acc

(* function removes all aliases of var from aliases set *)
let remove_all_var_aliases_from_aliases var_option astate =
  match var_option with
  | None -> astate
  | Some var -> (
    let points_to = PointsToSet.filter (fun elt -> PointsTo.fst_not_equals_var elt var) astate.points_to in
    let heap_points_to = HeapPointsToSet.filter (fun elt -> HeapPointsTo.fst_not_equals_var elt var)
                                                                                                astate.heap_points_to in
    let res = {astate with points_to; heap_points_to} in
    F.printf "astate.points_to after removing var=%a: %a\n" HilExp.AccessExpression.pp var PointsToSet.pp res.points_to;
    res
  )

(* function adds new alias to astate.points_to *)
let add_new_alias astate alias =
  match alias with
  | None -> astate
  | Some alias -> (
    (* check that fst != snd (to stop recursion) *)
    let (fst, snd) = alias in
    let snd_deref =
      match snd with
      | HilExp.AccessExpression.AddressOf _ -> HilExp.AccessExpression.dereference snd
      | _ -> snd
    in
    if HilExp.AccessExpression.equal fst snd_deref then
      astate
    else
      begin
        (* check if there exists a pair (snd, &fst) (to stop recursion) *)
        let fst_address_of =
          match HilExp.AccessExpression.address_of fst with
          | Some address_of -> address_of
          | None -> fst
        in
        if (PointsToSet.mem (snd, fst_address_of) astate.points_to) then
          astate
        else
          begin
          (* add new alias *)
          let new_aliases = PointsToSet.add alias astate.points_to in
          { astate with points_to=new_aliases }
          end
      end
  )

(* function creates new alias option from fst and snd *)
let create_new_alias fst snd =
  match (fst, snd) with
  | (Some f, Some s) -> Some (f, s)
  | _ -> None

(* function finds all aliases of var *)
let rec resolve_alias_list lhs lhs_current var aliases ~return_addressof_alias ~weak_update_flag =
  F.printf "resolve_alias_list: lhs=%a, lhs_current=%a, var=%a, weak_update=%b\n" HilExp.AccessExpression.pp lhs
                                      HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var weak_update_flag;
  (* if lhs matches lhs_current, end the recursion and return final alias/var *)
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      (* if lhs is dereference -> find new alias in aliases, else return var *)
      match lhs with
      | HilExp.AccessExpression.Dereference lhs_without_dereference -> (
        let aliases_list = find_alias_list lhs_without_dereference aliases ~add_deref:true [] in (* e.g. None | Some (y, &k) *)
        (weak_update_flag, aliases_list)
      )
      | _ -> (* lhs == lhs_current *)
        if return_addressof_alias then
        begin
          F.printf "1\n";
          (* return second member of alias if any alias found  *)
          let aliases = find_alias_list lhs aliases ~add_deref:false [] in
          (weak_update_flag, aliases)
        end
        else
          begin
          F.printf "2\n";
          (weak_update_flag, []) (* lhs was not aliased -> return empty list *)
          end
    end
  else
    begin
      (* find var in aliases and if found, continue recursion with the snd in alias *)
      let find_current_in_aliases = find_alias_list var aliases ~add_deref:false [] in (* e.g. None | Some (m, &y) *)
      let num_aliases = List.length find_current_in_aliases in
      F.printf "var=%a has %d aliases\n" HilExp.AccessExpression.pp var num_aliases;
      let _change_flag =
        if num_aliases > 1 then
          F.printf "changing weak_update_flag from %b\n" weak_update_flag
        else
          F.printf "remain weak_update_flag %b\n" weak_update_flag
      in
      let weak_update_flag = if num_aliases > 1 then true else weak_update_flag in
      let _p =
        if weak_update_flag then
          F.printf "------------------- WEAK UPDATE --------------------\n"
        else
          F.printf "------------------ STRONG UPDATE --------------------\n"
      in
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | [] -> (weak_update_flag, [])
      | list -> (
        let rec resolve lst resolved_acc ~weak_update =
          match lst with
          | [] -> (F.printf "3\n"; resolved_acc)
          | (fst, snd) :: t -> (
            F.printf "4 before: weak_update_flag=%b weak_update=%b, (%a,%a)\n" weak_update_flag weak_update HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
            let snd_deref = HilExp.AccessExpression.dereference snd in
            let (weak_update_flag, resolved_for_one) = resolve_alias_list lhs lhs_dereference snd_deref aliases ~return_addressof_alias ~weak_update_flag:weak_update in
            F.printf "4 after: weak_update_flag=%b weak_update=%b, (%a,%a)\n" weak_update_flag weak_update HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
            resolve t (resolved_for_one @ resolved_acc) ~weak_update:weak_update_flag
          )
        in
        F.printf "weak_update_flag i =%b\n" weak_update_flag;
        let aliases = resolve list [] ~weak_update:weak_update_flag in
        (weak_update_flag, aliases)
      )
    end

(* function returns the first alias of var *)
let rec resolve_alias lhs lhs_current var aliases =
  (* F.printf "resolve_alias: lhs=%a,lhs_current=%a,var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp
                                                                          lhs_current HilExp.AccessExpression.pp var; *)
  (* if lhs matches lhs_current, end the recursion and return final alias/var *)
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      (* if lhs is dereference -> find new alias in aliases, else return var *)
      match lhs with
      | HilExp.AccessExpression.Dereference lhs_without_dereference ->
        find_alias lhs_without_dereference aliases ~add_deref:true (* e.g. None | Some (y, &k) *)
      | _ -> None (* Some (var, var) *)
    end
  else
    begin
      (* find var in aliases and if found, continue recursion with the snd in alias *)
      let find_current_in_aliases = find_alias var aliases ~add_deref:false in (* e.g. None | Some (m, &y) *)
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | None -> None
      | Some (_, snd) -> (
        let snd_dereference = HilExp.AccessExpression.dereference snd in
        resolve_alias lhs lhs_dereference snd_dereference aliases
      )
    end

(* function resolves aliases of lhs recursively and returns None or Some (fst, &snd)
   (e.g. **y -> *u -> v: returns v for **y expression *)
let get_base_alias lhs aliases =
  let lhs_base_ae = get_base_as_access_expression lhs in
  resolve_alias lhs lhs_base_ae lhs_base_ae aliases

(* function returns Some load_alias if there already is an alias in load_aliases *)
let rec find_load_alias_by_var var load_aliases =
  match load_aliases with
  | [] -> None
  | (fst, snd, _) :: t ->
    if HilExp.AccessExpression.equal var fst then
      Some (fst, snd)
    else
      find_load_alias_by_var var t

(* function returns all aliases of exp from load_aliases list *)
let resolve_load_alias_list exp e load_aliases ~add_deref : HilExp.AccessExpression.t list =
  let load_aliases = LoadAliasesSet.elements load_aliases in
  let exp_base_ae = get_base_as_access_expression exp in
  let rec get_list_of_final_vars lst final_list_acc =
    match lst with
    | [] -> final_list_acc
    | (_, snd, _) :: t -> (
      (* transform res to same "format" as exp was (dereference, addressOf etc.) *)
      let res = AccessEvent.replace_base_of_var_with_another_var exp snd in
      get_list_of_final_vars t (res :: final_list_acc)
    )
  in
  match exp with
  | HilExp.AccessExpression.AddressOf _ -> [exp]
  | HilExp.AccessExpression.ArrayOffset _ -> (
    let load_alias_list = find_load_alias_list exp_base_ae load_aliases ~add_deref:false [] in
    match load_alias_list with
    | [] -> [exp]
    | list -> get_list_of_final_vars list []
  )
  | HilExp.AccessExpression.FieldOffset _ -> (
    let load_alias_list = find_load_alias_list exp_base_ae load_aliases ~add_deref [] in
    match load_alias_list with
    | [] -> [exp_base_ae]
    | list -> get_list_of_final_vars list []
  )
  | _ -> (
    let load_alias_list = find_load_alias_list exp_base_ae load_aliases ~add_deref [] in
    match load_alias_list with
    | [] -> (
      match e with
      | Some Exp.Lvar _ | Some Exp.Lindex _ | None ->
        (* program var -> access can be added *)
        [exp_base_ae]
      | Some Exp.Lfield (f_exp, _, _) -> (
        match f_exp with
        | Exp.Lvar _ | Exp.Lindex _ | Exp.Lfield _ -> [exp_base_ae] (* program var -> add *)
        | _ -> [] (* tmp var -> do not add *)
      )
      | Some _ -> [] (* tmp var -> do not add *)
    )
    | list -> get_list_of_final_vars list []
  )

(* function deletes load_aliases from astate *)
(* currently not used (used for experimenting with optimisation) *)
let astate_with_clear_load_aliases astate _loc_to_be_removed =
  (* let load_aliases = LoadAliasesSet.filter (fun x -> LoadAlias.loc_leq_than_max x loc_to_be_removed)
                                                                                               astate.load_aliases in *)
  (* { astate with load_aliases } *)
  astate

(* functions that handle heap points-to relations *)
(* function removes all heap points-to relations with the same loc *)
let remove_heap_aliases_by_loc loc astate =
  HeapPointsToSet.filter (fun elt -> HeapPointsTo.loc_not_equals elt loc) astate.heap_points_to

(* function returns all heap points-to relations with the same loc *)
let get_heap_aliases_list_by_loc loc heap_aliases =
  let rec find_heap_aliases loc list acc =
    match list with
    | [] -> acc
    | (var, location, _) :: t ->
      if Location.equal loc location then
        find_heap_aliases loc t (var :: acc)
      else
        find_heap_aliases loc t acc
  in
  find_heap_aliases loc heap_aliases []

(* function tries to find heap alias of var and returns Some loc if found, None if not found *)
let rec find_heap_alias_by_var var heap_aliases =
  match heap_aliases with
  | [] -> None
  | (fst, loc, _) :: t ->
    if HilExp.AccessExpression.equal var fst then
      Some loc
    else
      find_heap_alias_by_var var t

(* function removes heap alias of var *)
let remove_heap_alias_by_var_name var astate =
  (* find var alias in heap_aliases, return loc *)
  let loc_of_alias_to_be_removed = find_heap_alias_by_var var (HeapPointsToSet.elements astate.heap_points_to) in
  match loc_of_alias_to_be_removed with
  | Some loc ->
    (* remove all heap_aliases with the returned loc *)
    let updated_heap_aliases = remove_heap_aliases_by_loc loc astate in
    { astate with heap_points_to=updated_heap_aliases }
  | None -> astate (* heap alias with var doesn't exist *)

(* function adds new heap alias to astate.heap_points_to,
   if there already is an alias with variable var, the old alias is first removed *)
let add_heap_alias var loc astate =
  (* get base of var? *)
  let var_base = HilExp.AccessExpression.get_base var in
  let var_base_ae = HilExp.AccessExpression.base var_base in
  let new_heap_alias = (var_base_ae, loc, false) in
  (* remove heap alias if there already is any alias with the var *)
  let astate = remove_heap_alias_by_var_name var_base_ae astate in
  (* add new alias to heap aliases *)
  let new_heap_aliases = HeapPointsToSet.add new_heap_alias astate.heap_points_to in
  {astate with heap_points_to = new_heap_aliases}

(* functions joins astate.heap_points_to with heap_aliases *)
let add_heap_aliases_to_astate astate heap_aliases =
  let heap_aliases_set = HeapPointsToSet.of_list heap_aliases in
  let heap_aliases_joined = HeapPointsToSet.union astate.heap_points_to heap_aliases_set in
  {astate with heap_points_to=heap_aliases_joined}

(* function returns first variable in a tuple or var if the tuple is None *)
let get_option_fst var alias = (
  match alias with
  | None -> (F.printf "get_option_fst: None -> Some %a\n" HilExp.AccessExpression.pp var; Some var)
  | Some (fst, _) -> (F.printf "get_option_fst: Some %a\n" HilExp.AccessExpression.pp fst; Some fst)
)

(* function returns second variable in a tuple or None if the tuple is None *)
let get_option_snd alias = (
  match alias with
  | None -> None
  | Some (_, snd) -> Some snd
)

(* function updates points-to and heap points-to relations with (lhs = rhs) expression *)
let _update_aliases_list lhs rhs astate ~weak_update_flag42 =
  F.printf "update_aliases_list: lhs=%a, rhs=%a, weak_update42=%b\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp rhs weak_update_flag42;
  let aliases = PointsToSet.elements astate.points_to in
(*  (* lhs *)*)
(*  (* find if there exists an alias for lhs variable and get the first var in the alias *)*)
  let _lhs_alias = get_base_alias lhs aliases in
  let lhs_base_ae = get_base_as_access_expression lhs in
  let (_, result_list) = resolve_alias_list lhs lhs_base_ae lhs_base_ae aliases ~return_addressof_alias:true ~weak_update_flag:false in
  let rec _pr lst =
    match lst with
    | [] -> F.printf "]\n";
    | (fst,snd) :: t -> (
      F.printf "zzz fst=%a, snd=%a" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
      _pr t
    )
  in
  _pr result_list;
(*  F.printf "---WEAK_UPDATE_FLAG FOR REMOVE:%b---\n" weak_update_flag;*)
(*  let rec _print lst =*)
(*    match lst with*)
(*    | [] -> F.printf "."*)
(*    | h :: t -> ( *)
(*      F.printf "%a, " PointsTo.pp h;*)
(*      _print t*)
(*    )*)
(*  in*)
(*  _print result_list;*)

  let rec update_alias_for_each lst astate =
    match lst with
    | [] -> astate
    | (fst, _) :: t -> (
      F.printf "fst=%a\n" HilExp.AccessExpression.pp fst;
      let lhs_alias_fst = (Some fst) in
(*      let lhs_alias_fst = Some fst in*)
(*      let lhs_alias_fst = Some fst in *)
(*      let lhs_alias_fst = get_option_fst lhs lhs_alias in*)
      F.printf "weak_update_flag42: %b\n" weak_update_flag42;
      let res_astate =
      (* rhs *)
      match rhs with
      | HilExp.AccessExpression.AddressOf _ -> (
        (* create new alias: Some (lhs_alias_fst, &rhs) *)
        let new_alias = create_new_alias lhs_alias_fst (Some rhs) in
        (* remove existing lhs_alias and add the new alias to astate *)
        let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
        add_new_alias astate_alias_removed new_alias
      )
      | _ -> (  (* base, dereference etc. *)
        (* check if there already is some alias for the rhs expression *)
        let rhs_alias = get_base_alias rhs aliases in (* *q -> Some (x, &z) *)
        match rhs_alias with
        | Some _ -> ( (* alias was found *)
          (* get the second variable in rhs_alias and create new alias *)
          let rhs_alias_snd = get_option_snd rhs_alias in (* Some (x, &z) -> Some &z *)
          let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in
          (* remove existing lhs_alias and add the new alias to astate *)
          let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
          add_new_alias astate_alias_removed new_alias
        )
        | None -> ( (* alias wasn't found - try to find alias in heap aliases *)
          (* find rhs in heap aliases *)
          let rhs_heap_alias_loc = find_heap_alias_by_var rhs (HeapPointsToSet.elements astate.heap_points_to) in
          match rhs_heap_alias_loc with
          | Some loc -> (
            (* remove existing alias from aliases and add the new alias to astate *)
            let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
            add_heap_alias lhs loc astate_alias_removed
            )
          | None -> astate (* alias doesn't exist *)
        )
      )
    in
    update_alias_for_each t res_astate
    )
  in update_alias_for_each result_list astate


(* function updates points-to and heap points-to relations with (lhs = rhs) expression *)
let update_aliases lhs rhs astate ~weak_update =
(*  F.printf "TRY-----\n";*)
(*  update_aliases_list lhs rhs astate;*)
  F.printf "update_aliases: lhs=%a, rhs=%a, weak_update=%b\n" HilExp.AccessExpression.pp lhs
                                                                          HilExp.AccessExpression.pp rhs weak_update;
  let aliases = PointsToSet.elements astate.points_to in
  (* lhs *)
  (* find if there exists an alias for lhs variable and get the first var in the alias *)
  let lhs_alias = get_base_alias lhs aliases in
  let lhs_alias_fst = get_option_fst lhs lhs_alias in
  (* rhs *)
  match rhs with
  | HilExp.AccessExpression.AddressOf _ -> (
    (* create new alias: Some (lhs_alias_fst, &rhs) *)
    let new_alias = create_new_alias lhs_alias_fst (Some rhs) in
    (* remove existing lhs_alias and add the new alias to astate *)
    let astate_alias_removed =
      if weak_update then
        astate
      else
        remove_all_var_aliases_from_aliases lhs_alias_fst astate
    in
    add_new_alias astate_alias_removed new_alias
  )
  | _ -> (  (* base, dereference etc. *)
    (* check if there already is some alias for the rhs expression *)
    let rhs_alias = get_base_alias rhs aliases in (* *q -> Some (x, &z) *)
    match rhs_alias with
    | Some _ -> ( (* alias was found *)
      (* get the second variable in rhs_alias and create new alias *)
      let rhs_alias_snd = get_option_snd rhs_alias in (* Some (x, &z) -> Some &z *)
      let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in
      (* remove existing lhs_alias and add the new alias to astate *)
      let astate_alias_removed =
        if weak_update then
          astate
        else
          remove_all_var_aliases_from_aliases lhs_alias_fst astate
      in
      add_new_alias astate_alias_removed new_alias
    )
    | None -> ( (* alias wasn't found - try to find alias in heap aliases *)
      (* find rhs in heap aliases *)
      let rhs_heap_alias_loc = find_heap_alias_by_var rhs (HeapPointsToSet.elements astate.heap_points_to) in
      match rhs_heap_alias_loc with
      | Some loc -> (
        (* remove existing alias from aliases and add the new alias to astate *)
      let astate_alias_removed =
        if weak_update then
          astate
        else
          remove_all_var_aliases_from_aliases lhs_alias_fst astate
        in
        add_heap_alias lhs loc astate_alias_removed
        )
      | None -> astate (* alias doesn't exist *)
    )
  )

(* function returns alias of var if found in aliases, else returns var *)
let replace_var_with_its_alias_list var aliases heap_aliases ~return_addressof_alias =
  let var_ae = get_base_as_access_expression var in
  let (weak_update_flag_res, result_list) = resolve_alias_list var var_ae var_ae aliases ~return_addressof_alias ~weak_update_flag:false in
  match result_list with
  | [] -> (* [var] (* alias not found -> return the original var *) *)
  (
    (* alias not found -> try to find in heap_aliases *)
    (* find heap aliases with the base *)
    let loc = find_heap_alias_by_var var_ae heap_aliases in
    match loc with
    | Some loc -> (
      (* get list of all aliases with the same loc *)
      let lst = get_heap_aliases_list_by_loc loc heap_aliases in
      (* get the same format as the first expression (base, *, ** etc.) *)
      (* if the list is empty then return the original var *)
      match lst with
      | [] -> (weak_update_flag_res, [var])
      | lst -> (
        let rec for_each_in_list_get_right_format list acc =
          match list with
          | [] -> acc
          | h :: t -> (
            let right_format_var = AccessEvent.replace_base_of_var_with_another_var var h in
            for_each_in_list_get_right_format t (right_format_var :: acc)
          )
        in
        let res_list = for_each_in_list_get_right_format lst [] in
        (weak_update_flag_res, res_list)
      )
    )
    | None -> (weak_update_flag_res, [var]) (* not found -> return original var *)
  )
  | list -> (
    let rec get_list_of_snd lst acc =
      match lst with
      | [] -> acc
      | (_, snd) :: t -> (
        get_list_of_snd t (snd :: acc) (* alias found -> return the alias *)
      )
    in
    let res_list = get_list_of_snd list [] in
    (weak_update_flag_res, res_list)
  )

(* function returns all aliases of var by going through the list of load_aliases, then the list of points-to relations,
   and finally by going through the list of heap points-to relations *)
let resolve_entire_aliasing_of_var_list e_ae e astate ~add_deref ~return_addressof_alias =
  (* get list of load aliases, e.g. (n$1, i), (n$1, j) *)
  let e_after_resolving_load_alias_list = resolve_load_alias_list e_ae e astate.load_aliases ~add_deref in
  (* for each load alias *)
  let rec for_each_load_alias lst acc ~weak_update_flag =
    match lst with
    | [] -> (weak_update_flag, acc)
    | e_after_resolving_load_alias :: t -> (
      (* get list of all aliased variables *)
      let (weak_update_flag, e_final_list) = replace_var_with_its_alias_list e_after_resolving_load_alias (PointsToSet.elements
                           astate.points_to) (HeapPointsToSet.elements astate.heap_points_to) ~return_addressof_alias in
      (* create list of (e_after_resolving_load_alias, e_final) pairs *)
      let rec create_list_of_aliased_vars lst cacc =
        match lst with
        | [] -> cacc
        | var :: t -> (create_list_of_aliased_vars t ((e_after_resolving_load_alias, var) :: cacc) )
      in
      (* if the list is empty try to find in heap_aliases *)
        match e_final_list with
        | [] -> (
          let (weak_update_flag, e_final_list_heap) = replace_var_with_its_alias_list e_after_resolving_load_alias (PointsToSet.elements
                           astate.points_to) (HeapPointsToSet.elements astate.heap_points_to) ~return_addressof_alias in
          let new_heap_acc = create_list_of_aliased_vars e_final_list_heap acc in
          for_each_load_alias t new_heap_acc ~weak_update_flag
        )
        | _ -> (
          let new_acc = create_list_of_aliased_vars e_final_list acc in
          for_each_load_alias t new_acc ~weak_update_flag
        )
    )
  in
  let (weak_update_flag, res_list) = for_each_load_alias e_after_resolving_load_alias_list [] ~weak_update_flag:false in
  (weak_update_flag, res_list)

(* function returns all aliases of e_ae of the lfield type by going through the list of load_aliases,
   then the list of points-to relations, and finally by going through the list of heap points-to relations *)
let resolve_entire_aliasing_of_var_for_lfield_list e_ae e astate ~add_deref ~return_addressof_alias =
    match e_ae with
    | HilExp.AccessExpression.FieldOffset (fieldoffset_ae, fieldname)-> (
      (* get list of aliases of fieldoffset_ae *)
      let (_, lst) = resolve_entire_aliasing_of_var_list fieldoffset_ae e astate ~add_deref ~return_addressof_alias in
      (* for each member of the list of fieldoffset_ae create a field with the fieldname *)
      let rec for_each_create_fieldname fieldname lst acc =
        match lst with
        | [] -> acc
        | (e_aliased, e_aliased_final) :: t -> (
          let new_fieldname_uno = HilExp.AccessExpression.field_offset e_aliased fieldname in
          let new_fieldname_due = HilExp.AccessExpression.field_offset e_aliased_final fieldname in
          for_each_create_fieldname fieldname t ((new_fieldname_uno, new_fieldname_due) :: acc)
        )
      in
      let lst_with_fieldnames = for_each_create_fieldname fieldname lst [] in
      (* return the list *)
      lst_with_fieldnames
    )
    | _ -> []

(* functions that handle threads *)
(* function creates new thread: None or Some (thread, loc, false) *)
let create_thread_from_load_ae_with_false_flag load loc astate : ThreadEvent.t =
  (* find thread in load aliases *)
  let thread_load_alias = find_load_alias_by_var load (LoadAliasesSet.elements astate.load_aliases) in
  match thread_load_alias with
  | None -> (
    (* create thread name from load alias base *)
    let load_base =
      match load with
      | HilExp.AccessExpression.AddressOf b -> b
      | _ -> load
    in
    (load_base, loc, false)
  )
  | Some (_, final_thread) -> (
    (* create thread *)
    let final_thread =
      match final_thread with
      | HilExp.AccessExpression.AddressOf th -> th
      | _ -> final_thread
    in
    (final_thread, loc, false)
  )

(* function creates new thread from its load alias *)
let new_thread th_load_ae loc astate =
  let new_thread_from_load_with_false_flag = create_thread_from_load_ae_with_false_flag th_load_ae loc astate in
  (* find thread (with false flag) in threads_active *)
  let found_with_false_flag = ThreadSet.mem new_thread_from_load_with_false_flag astate.threads_active in
  match found_with_false_flag with
  | false -> new_thread_from_load_with_false_flag
  | true -> (
      (* if found then find the same thread with true *)
      let (th, loc, _) = new_thread_from_load_with_false_flag in
      let thread_with_true_flag = (th, loc, true) in
      thread_with_true_flag
  )

(* function removes a thread from threads_joined list,
   first try to remove a thread with true flag, if not found, try to remove a thread with false flag *)
let remove_thread_from_threads_joined thread_id threads_joined =
  let thread_with_true_flag_found = ThreadSet.find_opt (thread_id, Location.dummy, true) threads_joined in
  (* first try to find thread with true flag *)
  match thread_with_true_flag_found with
  | Some th_true -> (
    (* thread with true flag is in threads_joined -> remove it *)
    ThreadSet.remove th_true threads_joined
  )
  | None -> (
    (* thread with true flag is not in threads_joined -> try to find thread with false flag *)
    let thread_with_false_flag_found = ThreadSet.find_opt (thread_id, Location.dummy, false) threads_joined in
    match thread_with_false_flag_found with
    | Some th_false -> (
      (* thread is found -> remove it *)
      ThreadSet.remove th_false threads_joined
    )
    | None -> (
      (* not found -> return the original threads_joined *)
      threads_joined
    )
  )

(* function adds a thread to astate.threads_active,
   if there already is the thread with false created_in_loop flag, adds it with true flag *)
let add_thread thread astate =
  (* find thread in threads_active *)
  let found_with_false_flag = ThreadSet.mem thread astate.threads_active in
    match found_with_false_flag with
    | false -> (
      let threads_active = ThreadSet.add thread astate.threads_active in
      let (thread_name, _, _) = thread in
      let threads_joined = remove_thread_from_threads_joined thread_name astate.threads_joined in
      {astate with threads_active; threads_joined }
    )
    | true -> (
      (* if found then find the same thread with true *)
      let (th, loc, _) = thread in
      let thread_with_true = (th, loc, true) in
      let found_with_true_flag = ThreadSet.mem thread_with_true astate.threads_active in
      (* add the thread if it is not already present in astate.threads_active *)
      match found_with_true_flag with
      | false -> (
        let threads_active = ThreadSet.add thread_with_true astate.threads_active in
        { astate with threads_active }
      )
      | true -> (
        let threads_active = astate.threads_active in
        { astate with threads_active }
      )
    )

(* function finds a thread in threads set by its name and created_in_loop flag
   and returns None if not found or Some thread if found *)
let find_thread_in_threads_active thread_name threads ~created_in_loop_flag =
let threads_list = ThreadSet.elements threads in
  let rec find_thread lst =
    match lst with
    | [] -> None
    | (th, _, flag) as th_ev :: t -> (
      if (HilExp.AccessExpression.equal th thread_name)
          && (Bool.equal flag created_in_loop_flag) then
        Some th_ev
      else
        find_thread t
    )
  in find_thread threads_list

(* function tries to find thread with flag created_in_loop set to true in astate.threads_active,
   if found then removes it, if not found, tries to find the thread with false flag and removes it *)
let remove_thread load_ae astate =
  (* find thread by its name in threads *)
  let thread_load_alias = find_load_alias_by_var load_ae (LoadAliasesSet.elements astate.load_aliases) in
  match thread_load_alias with
  | None -> (
    (* not found -> add to threads_joined and return *)
    let new_thread = (load_ae, Location.dummy, false) in
    let threads_joined = ThreadSet.add new_thread astate.threads_joined in
    { astate with threads_joined }
  )
  | Some (_, thread_ae) -> (
    (* find the thread in threads_active - first find with true flag *)
    let thread_ae =
      match thread_ae with
      | HilExp.AccessExpression.AddressOf th -> th
      | _ -> thread_ae
    in
    let thread_with_true_flag = find_thread_in_threads_active thread_ae astate.threads_active
                                                                                           ~created_in_loop_flag:true in
    (* if found then remove *)
    match thread_with_true_flag with
    | Some th -> (
      (* remove the thread *)
      let threads_joined = ThreadSet.add th astate.threads_joined in
      let threads_active = ThreadSet.remove th astate.threads_active in
      { astate with threads_active; threads_joined }
    )
    | None -> (
      (* else find the thread with false flag *)
      let thread = find_thread_in_threads_active thread_ae astate.threads_active ~created_in_loop_flag:false in
      match thread with
      | Some th ->
        (* remove the thread *)
        let threads_joined = ThreadSet.add th astate.threads_joined in
        let threads_active = ThreadSet.remove th astate.threads_active in
        { astate with threads_active; threads_joined }
      | None -> (
        let th = (thread_ae, Location.dummy, false) in
        let threads_joined = ThreadSet.add th astate.threads_joined in
        { astate with threads_joined }
      )
    )
  )

(* function transforms a SIL expression to the HIL expression *)
let transform_sil_expr_to_hil sil_exp sil_typ add_deref =
  let f_resolve_id _ = None in
  HilExp.of_sil ~include_array_indexes:false ~f_resolve_id ~add_deref sil_exp sil_typ

(* function transforms list of SIL expressions to HIL expressions *)
let transform_sil_exprs_to_hil_list sil_expr_list add_deref = (* list of sil exprs *)
  let rec transform_sil_to_hil_actuals (sil_list : (Exp.t * Typ.t) list) (acc : HilExp.t list) =
    match sil_list with
    | [] -> acc
    | (exp, typ) :: t -> (
      let hil_expr = transform_sil_expr_to_hil exp typ add_deref in
      (* add h to the list of HilExp.t *)
      let list_updated = acc @ [hil_expr] in
      transform_sil_to_hil_actuals t list_updated
    )
  in transform_sil_to_hil_actuals sil_expr_list []

(* functions that handle locals *)
(* function adds var to the locals *)
let add_var_to_locals var locals_set =
  LocalsSet.add var locals_set

(* function removes var from locals *)
let remove_var_from_locals var_to_be_removed locals =
  (* get base as access expression of var_to_be_removed *)
  let var_to_be_removed_base = HilExp.AccessExpression.get_base var_to_be_removed in
  let var_to_be_removed = HilExp.AccessExpression.base var_to_be_removed_base in
  LocalsSet.remove var_to_be_removed locals

(* function removes all vars from the list_of_vars_to_be_removed list from locals *)
let rec remove_vars_from_locals list_of_vars_to_be_removed locals =
  match list_of_vars_to_be_removed with
  | [] -> locals
  | (_, var) :: t -> (
    let updated_locals = remove_var_from_locals var locals in
    remove_vars_from_locals t updated_locals
  )

(* functions that handle adding/removing accesses *)
(* function adds new access to var to astate *)
let add_access_to_astate var access_type astate loc pname =
  let new_access : AccessEvent.t =
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let threads_joined = astate.threads_joined in
    let thread =
      (* if the current function is name, create the main thread *)
      if (Int.equal (String.compare (Procname.to_string pname) "main") 0) then
        Some (ThreadEvent.create_main_thread)
      else (* else the thread is unknown *)
        None
    in
    { var; loc; access_type; locked; unlocked; threads_active; threads_joined; thread }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  { astate with accesses }

(* function checks if the var should be added to accesses and if yes, it is added,
   var is not added if it is present in the list of locals or if it is a return expression *)
let add_access_to_astate_with_check var access_type astate loc pname =
  if HilExp.AccessExpression.is_return_var var then
    astate (* return won't be added to accesses *)
  else
    begin
      let var_base_ae = get_base_as_access_expression var in
      let is_local = LocalsSet.mem var_base_ae astate.locals in
      match is_local with
      | true -> astate (* local won't be added to accesses *)
      | false -> add_access_to_astate var access_type astate loc pname
    end

(* function adds new access to astate and updates the list of tmp_heap used when dynamically allocating memory *)
let add_access_with_heap_alias_when_malloc e1_ae e2_ae loc astate tmp_heap pname =
  let rec update_astate_and_tmp_heap updated_astate tmp_heap updated_tmp_heap =
    match tmp_heap with
    | [] -> (updated_astate, updated_tmp_heap)
    | (var, loc) :: t ->
      (* check if the var is equal to e2_ae *)
      if (HilExp.AccessExpression.equal var e2_ae) then
        begin
          (* create (e1_ae, loc), add it to astate.heap_points_to, don't add (var, loc) to acc and continue with t *)
          let new_astate = add_heap_alias e1_ae loc updated_astate in
          update_astate_and_tmp_heap new_astate t updated_tmp_heap
        end
      else
        (* var is not equal to e2_ae -> then add (var, loc) to acc and continue with t with astate and new acc *)
        update_astate_and_tmp_heap updated_astate t ((var, loc) :: updated_tmp_heap)
  in
  let (astate, tmp_heap) = update_astate_and_tmp_heap astate tmp_heap [] in
  (* add new access to astate *)
  let astate_with_new_write_access = add_access_to_astate_with_check e1_ae ReadWriteModels.Write astate loc pname in
  (astate_with_new_write_access, tmp_heap)

(* function returns list of all heap aliases with the same loc *)
let get_list_of_heap_aliases_with_same_loc_as_var var (astate : t) =
  (* find var in aliases *)
  let var_base_ae = get_base_as_access_expression var in
  let loc_opt = find_heap_alias_by_var var_base_ae (HeapPointsToSet.elements astate.heap_points_to) in
  let rec get_list_of_vars_with_loc loc heap_aliases acc =
    match heap_aliases with
    | [] -> acc
    | (var_found, loc_found, _) :: t ->
      (* check if loc equals loc_found *)
      if (Location.equal loc loc_found) then
        begin
          (* make var_found the same format as var was (e. g. dereference, double dereference, addressOf) *)
          let var_to_add = AccessEvent.replace_base_of_var_with_another_var var var_found in
          get_list_of_vars_with_loc loc t (var_to_add :: acc)
        end
      else
        get_list_of_vars_with_loc loc t acc
  in
  (* check if heap alias with var exists and if yes, get list of all heap aliases with the same loc *)
  match loc_opt with
  | None -> [] (* heap alias doesn't exist *)
  | Some loc -> get_list_of_vars_with_loc loc (HeapPointsToSet.elements astate.heap_points_to) []

(* function adds accesses to all aliased vars *)
let add_accesses_to_astate_with_aliases_or_heap_aliases e1_ae e1_aliased_final access_type astate loc pname =
  (* check if e1_ae (original var) and a1_aliased_final (var after aliasing) are equal *)
  if (HilExp.AccessExpression.equal e1_ae e1_aliased_final) then
    begin
      (* var was not aliased - try to find the var in heap aliases *)
      let list_of_new_accesses_from_heap_aliases = get_list_of_heap_aliases_with_same_loc_as_var e1_ae astate in
      match list_of_new_accesses_from_heap_aliases with
      | [] -> (* var was not in heap aliases -> add access to var *)
        add_access_to_astate_with_check e1_aliased_final access_type astate loc pname
      | _ -> ( (* var was in heap aliases -> add access to each var from list *)
        let rec add_heap_accesses accesses_to_add_list astate =
          match accesses_to_add_list with
          | [] -> astate
          | var_heap :: t -> (
            (* add access to var and continue in adding vars from list *)
            let new_astate = add_access_to_astate_with_check var_heap access_type astate loc pname in
            add_heap_accesses t new_astate
          )
        in
        add_heap_accesses list_of_new_accesses_from_heap_aliases astate
      )
    end
  else
    (* add access to aliased var to accesses *)
    add_access_to_astate_with_check e1_aliased_final access_type astate loc pname

(* function removes all accesses to formal parameters of a function *)
let rec remove_accesses_to_all_formals callee_pname formals accesses : AccessSet.t =
  match formals with
  | [] -> accesses
  | formal :: t -> (
    let formal_pvar = Pvar.mk (fst formal) callee_pname in
    let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
    let formal_access_expression = HilExp.AccessExpression.base formal_access_path_base in
    (* create base of formal *)
    let formal_base = HilExp.AccessExpression.get_base formal_access_expression in
    (* create list from set *)
    let accesses_list = AccessSet.elements accesses in
    (* if access.var == formal.base then don't add it to the list of accesses *)
    let rec remove_formal lst acc =
      match lst with
      | [] -> acc
      | access :: t -> (
        (* get access.var and create base from it *)
        let access_var_base = HilExp.AccessExpression.get_base (AccessEvent.get_var access) in
        (* check if the base of formal equals the base of access.var *)
        if (AccessPath.equal_base access_var_base formal_base) then
          remove_formal t acc (* don't add the access to the list *)
        else
          remove_formal t (access :: acc) (* add the access to the list *)
      )
    in
    (* remove formals from accesses *)
    let accesses_list_with_removed_accesses = remove_formal accesses_list [] in
    (* create set from list *)
    let accesses_without_formal = AccessSet.of_list accesses_list_with_removed_accesses in
    remove_accesses_to_all_formals callee_pname t accesses_without_formal
  )

(* function creates new AccessSet with all accesses to var formal in accesses *)
let get_all_accesses_to_formal formal accesses : AccessSet.t =
  (* create base of formal *)
  let formal_base = HilExp.AccessExpression.get_base formal in
  (* create list from set *)
  let accesses_list = AccessSet.elements accesses in
  (* if access.var == formal.base then don't add it to the list of accesses *)
  let rec add_formal lst acc =
    match lst with
    | [] -> acc
    | access :: t -> (
      (* get access.var and create base from it *)
      let access_var_base = HilExp.AccessExpression.get_base (AccessEvent.get_var access) in
      (* check if the base of formal equals the base of access.var *)
      if (AccessPath.equal_base access_var_base formal_base) then
        add_formal t (access :: acc) (* don't add the access to the list *)
      else
        add_formal t acc (* add the access to the list *)
    )
  in
  (* remove formals from accesses *)
  let accesses_list_with_accesses_to_formals = add_formal accesses_list [] in
  (* create set from list *)
  AccessSet.of_list accesses_list_with_accesses_to_formals

(* functions that handle locks *)
(* function adds a lock to lockset and removes it from unlockset *)
let acquire_lock lockid astate loc =
  match lockid with
  | HilExp.AccessExpression e_ae -> (
    let lst =  resolve_load_alias_list e_ae None astate.load_aliases ~add_deref:true in
    let rec add_locks_to_lockset lst astate =
      match lst with
      | [] -> astate
      | lock_ae :: t -> (
        let lockid = HilExp.AccessExpression.to_access_path lock_ae in
        (* add the lock *)
        let lock : LockEvent.t = (lockid, loc) in
        (* F.printf "adding lock: %a\n" LockEvent.pp lock; *)
        let new_astate : t =
          let lockset = Lockset.add lock astate.lockset in
          let unlockset = Lockset.remove lock astate.unlockset in
          { astate with lockset; unlockset }
        in add_locks_to_lockset t new_astate
      )
    in add_locks_to_lockset lst astate
  )
  | _ -> astate

(* function removes a lock from lockset and adds it to the unlockset *)
let release_lock lockid astate loc =
  match lockid with
  | HilExp.AccessExpression e_ae -> (
    (* get program var from load alias *)
    (* locks: must-be-locked, points-to: may-point-to -> don't remove all lock aliases *)
    let lst =  resolve_load_alias_list e_ae None astate.load_aliases ~add_deref:true in
    let rec remove_locks_from_lockset lst astate =
      match lst with
      | [] -> astate
      | lock_ae :: t -> (
        let lockid = HilExp.AccessExpression.to_access_path lock_ae in
        (* remove the lock *)
        let lock : LockEvent.t = (lockid, loc) in
        (* F.printf "removing lock: %a\n" LockEvent.pp lock; *)
        let new_astate : t =
          let lockset = Lockset.remove lock astate.lockset in
          let unlockset = Lockset.add lock astate.unlockset in
          { astate with lockset; unlockset }
        in remove_locks_from_lockset t new_astate
      )
    in remove_locks_from_lockset lst astate
  )
  | _ -> astate

(* function handles the LOAD instruction *)
let load id_ae e_ae e (_typ: Typ.t) loc astate pname =
  (* for each load alias *)
  let rec add_load_alias_and_accesses l updated_astate =
    match l with
    | [] -> updated_astate
    | (e_aliased, e_aliased_final) :: t -> (
      (* create new load alias *)
      let new_load_alias = (id_ae, e_aliased_final, loc) in
      let load_aliases = LoadAliasesSet.add new_load_alias astate.load_aliases in
      (* add new load alias to load_aliases *)
      let astate = { updated_astate with load_aliases } in
      (* add all read access (if it is access to heap allocated variable with alias, there could be more accesses) *)
      let new_updated_astate = add_accesses_to_astate_with_aliases_or_heap_aliases e_aliased e_aliased_final
                                                                                ReadWriteModels.Read astate loc pname in
      add_load_alias_and_accesses t new_updated_astate
    )
  in
  match e with
  | Exp.Var _ -> (
    (* e is Var (e.g. n$0) -> it should already be present in load_aliases -> resolve it *)
    let (_, lst) = resolve_entire_aliasing_of_var_list e_ae (Some e) astate ~add_deref:false ~return_addressof_alias:false in
    (* for each load alias *)
    add_load_alias_and_accesses lst astate
  )
  | Exp.Lfield _ -> (
    (* e is a field of a structure *)
    let lst = resolve_entire_aliasing_of_var_for_lfield_list e_ae (Some e) astate ~add_deref:true
                                                                                        ~return_addressof_alias:false in
    add_load_alias_and_accesses lst astate
  )
  | Exp.Lvar _ | _ -> (
    (* e is program var -> create new load alias (pvar, load_expr) and add it to astate.load_aliases *)
    let new_load_alias = (id_ae, e_ae, loc) in
    let load_aliases = LoadAliasesSet.add new_load_alias astate.load_aliases in
    let astate = { astate with load_aliases } in
    (* add read access to e *)
    add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname
  )

(* function handles the STORE instruction *)
let store e1 typ e2 loc astate pname =
  F.printf "store e1=%a e2=%a on line %a\n" Exp.pp e1 Exp.pp e2 Location.pp loc;
  F.printf "store - points-to at the beginning: %a\n" PointsToSet.pp astate.points_to;
  F.printf "store - heap-points-to at the beginning: %a\n" HeapPointsToSet.pp astate.heap_points_to;
  let new_astate_after_store =
  (* transform e1 expression to the access expression *)
  let add_deref =
    match e1 with
    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> true (* e.g. p, *p *)
    | Exp.Var _ | _ -> false (* e.g. n$0 *)
  in
  let e1_hil = transform_sil_expr_to_hil e1 typ add_deref in
  match e1_hil with
  | HilExp.AccessExpression ((FieldOffset _) as e1_ae ) -> (
    (* get list of all aliases of e1_ae (field offset) *)
    F.printf "store1\n";
    let lst = resolve_entire_aliasing_of_var_for_lfield_list e1_ae (Some e1) astate ~add_deref:true
                                                                                        ~return_addressof_alias:false in
    (* function adds accesses for each var from the list of aliases *)
    let rec add_accesses_for_each_aliased_var lst updated_astate =
      match lst with
      | [] -> updated_astate
      | (e1_aliased, e1_aliased_final) :: t -> (
        let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final
                                                                       ReadWriteModels.Write updated_astate loc pname in
        add_accesses_for_each_aliased_var t astate
      )
    in add_accesses_for_each_aliased_var lst astate
  )
  | AccessExpression e1_ae -> (
    F.printf "store2\n";
    (* get list of all aliases of e1_ae *)
    (* when resolving all aliases of var, get the information if the var has more aliases than one ->
       -> if yes, weak update is performed (existing points-to relations are not removed from the set),
          else strong update is performed *)
    let (weak_update_flag, lst) = resolve_entire_aliasing_of_var_list e1_ae (Some e1) astate ~add_deref:true ~return_addressof_alias:false in
    F.printf "/////////////////// WEAK UPDATE FLAG IN STORE: %b\n" weak_update_flag;
    let rec for_each lst astate =
      match lst with
      | [] -> astate
      | (e1_aliased, e1_aliased_final) :: t -> (
        let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final
                                                                               ReadWriteModels.Write astate loc pname in
        (* if the type is pointer, add aliases to e2 *)
        if (Typ.is_pointer typ) then
          begin
            F.printf "store3\n";
            (* check null on the rhs *)
            if (Exp.is_null_literal e2) then
              (* remove aliases of e1_aliased_final *)
              remove_all_var_aliases_from_aliases (Some e1_aliased_final) astate
            else (* add alias *)
              begin
                (* convert e2 expression to the access expression *)
                let e2_exp = match e2 with Exp.Cast (_, cast_exp) -> cast_exp (* handle Cast *) | _ -> e2 in
                let e2_hil = transform_sil_expr_to_hil e2_exp typ false in
                match e2_hil with
                | AccessExpression e2_ae -> (
                  (* handle aliasing of e2 *)
                  let astate =
                    match e2 with
                    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> update_aliases e1_aliased_final e2_ae astate ~weak_update:weak_update_flag
                    | Exp.Var _ | _ ->  (
                      F.printf "store4\n";
                      let (_, lst_e2) = resolve_entire_aliasing_of_var_list e2_ae (Some e2) astate ~add_deref:false
                                                                                        ~return_addressof_alias:false in
                      let rec foreach lst astate =
                        match lst with
                        | [] -> astate
                        | (_, e2_aliased_final) :: t -> (
                          F.printf "store5\n";
                          foreach t (update_aliases e1_aliased_final e2_aliased_final astate ~weak_update:weak_update_flag)
                        )
                      in foreach lst_e2 astate
                    )
                  in for_each t astate (* save alias to the aliases set *)
                )
                | _ -> for_each t astate
              end
          end
        else
          for_each t astate
      )
    in for_each lst astate
  )
  | _ -> astate
  in
  F.printf "store: points-to after store: %a\n" PointsToSet.pp new_astate_after_store.points_to;
  new_astate_after_store

  (* function returns a list of accesses to each alias of actual *)
  let rec for_each_alias_of_actual_add_access formal_access_expression list_of_accesses_to_formal list_of_actual_aliases
                                                                                                   accesses_acc astate =
      match list_of_actual_aliases with
      | [] -> accesses_acc
      | (_, actual_alias_ae) :: t_aliases -> (
        let actual_alias_base_ae = get_base_as_access_expression actual_alias_ae in
        (* check if the variable is local *)
        let is_local = LocalsSet.mem actual_alias_base_ae astate.locals in
        let new_accesses_list =
          match is_local with
          | true -> [] (* local will not be added to accesses *)
          | false -> (* replace all accesses to formal with actual *)
            AccessSet.elements (AccessSet.map (AccessEvent.edit_access_with_actuals formal_access_expression
                                       (HilExp.AccessExpression actual_alias_ae)) list_of_accesses_to_formal)
        in
        let accesses_updated_with_new_accesses = new_accesses_list @ accesses_acc in
        for_each_alias_of_actual_add_access formal_access_expression list_of_accesses_to_formal t_aliases
                                                                               accesses_updated_with_new_accesses astate
      )

  (* function resolves aliases for each actual,
     and calls function that returns a list of accesses to all actual's aliases *)
  let for_actual_add_accesses_to_all_aliases formal_access_expression list_of_accesses_to_formal
                                                                   (actual : HilExp.t option)  astate ~creating_thread =
    match actual with
    | None -> (astate, [])
    | Some actual ->
      if HilExp.is_null_literal actual then
        (* actual is NULL -> don't add any accesses *)
        (astate, [])
      else
        begin
          (* get all aliases of actual *)
          let list_of_actual_aliases =
            match actual with
            | HilExp.AccessExpression ((FieldOffset _) as actual_load) ->
              resolve_entire_aliasing_of_var_for_lfield_list actual_load None astate ~add_deref:false
                                                             ~return_addressof_alias:creating_thread
            | HilExp.AccessExpression actual_load -> (
              let (_, lst) = resolve_entire_aliasing_of_var_list actual_load None astate ~add_deref:false
                                                                                 ~return_addressof_alias:creating_thread
              in lst
            )
            | _ -> []
          in
          (* if flag is true then remove all aliases from locals of astate *)
          let astate =
            if creating_thread then
              let locals = remove_vars_from_locals list_of_actual_aliases astate.locals in
              {astate with locals}
            else astate
          in
          (* add accesses to all aliases *)
          let new_accesses = for_each_alias_of_actual_add_access formal_access_expression list_of_accesses_to_formal
                                                                                     list_of_actual_aliases [] astate in
          (astate, new_accesses)
        end

(* function removes all points-to relations containing a local variable *)
let remove_locals_points_to points_to locals =
  let points_to_list = PointsToSet.elements points_to in
  let rec remove_var lst acc =
    match lst with
    | [] -> acc
    | (var, var') :: t ->
      if LocalsSet.mem var locals || LocalsSet.mem var' locals then
        remove_var t (PointsToSet.remove (var, var') acc)
      else remove_var t acc
  in remove_var points_to_list points_to

(* function removes all heap points-to relations containing a formal argument *)
let remove_formals_heap_arguments heap_points_to =
  HeapPointsToSet.filter HeapPointsTo.loc_greater_than_0 heap_points_to

(* function joins two abstract states *)
let integrate_summary_without_accesses astate callee_summary =
  let renamed_callee_summary_threads = replace_unknown_threads_with_actuals astate.threads_active astate.threads_joined
                                                          callee_summary.threads_active callee_summary.threads_joined in
  let threads_active = ThreadSet.diff (ThreadSet.union astate.threads_active callee_summary.threads_active)
                                                                                       renamed_callee_summary_threads in
  let threads_joined = ThreadSet.union (ThreadSet.diff astate.threads_joined callee_summary.threads_active)
                                                                                       renamed_callee_summary_threads in
  let lockset = Lockset.diff (Lockset.union astate.lockset callee_summary.lockset) callee_summary.unlockset in
  let unlockset = Lockset.union (Lockset.diff astate.unlockset callee_summary.lockset) callee_summary.unlockset in
  let points_to = PointsToSet.union astate.points_to (remove_locals_points_to callee_summary.points_to
                                                                                               callee_summary.locals) in
  let heap_points_to = HeapPointsToSet.union astate.heap_points_to (remove_formals_heap_arguments
                                                                                       callee_summary.heap_points_to) in
  { astate with threads_active; threads_joined; lockset; unlockset; points_to; heap_points_to }

(* function integrates summary of callee to the current astate when function call to pthread_create() occurs,
   it replaces all accesses to formal in callee_summary to accesses to actuals, joins the callee summary
   with the current abstract state, and creates a new active thread *)
let integrate_pthread_summary astate thread callee_pname _loc callee_summary callee_formals actuals =
  (* F.printf "integrate_pthread_summary: callee_pname=%a on %a\n" Procname.pp callee_pname Location.pp _loc; *)
  (* edit information about each access - thread, threads_active, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads
            astate.threads_active astate.threads_joined astate.lockset astate.unlockset (Some thread)
            callee_summary.threads_active callee_summary.threads_joined) callee_summary.accesses in
  (* replace actuals with formals *)
  let callee_formal = (* callee formal is the same every time: pthread_create(void *arg) *)
    match callee_formals with
    | (var, typ) :: _ -> (
      let formal_pvar = Pvar.mk (var) callee_pname in
      let formal_access_path_base = AccessPath.base_of_pvar formal_pvar typ in
      (* F.printf "callee formal access path base: %a\n" AccessPath.pp_base formal_access_path_base; *)
      HilExp.AccessExpression.base formal_access_path_base
    )
    | _ -> assert false
  in
  let list_of_accesses_to_formal = get_all_accesses_to_formal callee_formal edited_accesses_from_callee in
  (* get set of accesses to corresponding actual in callee and update the set *)
  let (astate, accesses_to_formal_to_add_to_astate_list) = for_actual_add_accesses_to_all_aliases callee_formal
                                         list_of_accesses_to_formal (List.nth actuals 3) astate ~creating_thread:true in
  let accesses_to_formal_to_add_to_astate = AccessSet.of_list accesses_to_formal_to_add_to_astate_list in
  let accesses_to_globals_in_callee = remove_accesses_to_all_formals callee_pname callee_formals
                                                                                          edited_accesses_from_callee in
  let accesses_from_callee = AccessSet.union accesses_to_formal_to_add_to_astate accesses_to_globals_in_callee in
  let accesses_joined = AccessSet.union astate.accesses accesses_from_callee in
  (* abstract state with updated accesses *)
  let astate = { astate with accesses=accesses_joined } in
  (* integrate locks, threads, and points-to relations to the current abstract state *)
  integrate_summary_without_accesses astate callee_summary

(* function integrates summary of callee to the current abstract state when function call occurs,
   it replaces all accesses to formals in callee_summary to accesses to actuals, and joins the
   callee summary with the current abstract state *)
let integrate_summary astate callee_pname _loc callee_summary callee_formals actuals caller_pname =
  (* F.printf "integrate_summary: callee_pname=%a in Darc\n" Procname.pp callee_pname; *)
  (* create main thread if the caller function is main *)
  let current_thread =
    if (Int.equal (String.compare (Procname.to_string caller_pname) "main") 0) then
      Some (ThreadEvent.create_main_thread)
    else None
  in
  (* update accesses in callee_summary with the current lockset, unlockset, threads_active and thread *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads
           astate.threads_active astate.threads_joined astate.lockset astate.unlockset current_thread
           callee_summary.threads_active callee_summary.threads_joined) callee_summary.accesses in
  (* function replaces formal parameters in accesses with actual parameters *)
  let replace_formals_with_actuals formals actuals accesses =
    let cnt = ref 0 in
    let accesses_ref = ref accesses in
    let rec loop = function
      | [] -> !accesses_ref
      | formal :: t_formals -> (
        (* get formal as access expression *)
        let formal_pvar = Pvar.mk (fst formal) callee_pname in
        let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
        let formal_ae = HilExp.AccessExpression.base formal_access_path_base in
        (* get list of accesses to formal in callee *)
        let list_of_accesses_to_formal = get_all_accesses_to_formal formal_ae edited_accesses_from_callee in
        (* get set of accesses to corresponding actual in callee *)
        let (_, accesses_to_formal_to_add_to_astate_list) = for_actual_add_accesses_to_all_aliases formal_ae
                                     list_of_accesses_to_formal (List.nth actuals !cnt) astate ~creating_thread:false in
        let accesses_to_formal_to_add_to_astate = AccessSet.of_list accesses_to_formal_to_add_to_astate_list in
        accesses_ref := AccessSet.union accesses_to_formal_to_add_to_astate !accesses_ref;
        cnt := !cnt + 1; (* go to the next parameter *)
        loop t_formals
      )
    in loop formals
  in
  (* update accesses *)
  let accesses_with_actuals = replace_formals_with_actuals callee_formals actuals (AccessSet.empty) in
  let accesses_to_globals_in_callee = remove_accesses_to_all_formals callee_pname callee_formals
                                                                                          edited_accesses_from_callee in
  let accesses_from_callee = AccessSet.union accesses_with_actuals accesses_to_globals_in_callee in
  let accesses_joined = AccessSet.union astate.accesses accesses_from_callee in
  (* abstract state with updated accesses *)
  let astate = { astate with accesses=accesses_joined } in
  (* integrate locks, threads, and points-to relations to the current abstract state *)
  integrate_summary_without_accesses astate callee_summary

(* function returns a tuple of lists, the first list is a list of accesses to var,
   the second list is a list of accesses that are not to var *)
let rec separate_lists var lst accesses_to_var other_accesses =
  match lst with
  | [] -> (accesses_to_var, other_accesses)
  | access :: t -> (
    let access_var = AccessEvent.get_var access in
    if HilExp.AccessExpression.equal var access_var then
      separate_lists var t (access :: accesses_to_var) other_accesses
    else
      separate_lists var t accesses_to_var (access :: other_accesses)
  )

(* function creates cartesian product of two lists *)
let rec product l1 l2 =
    match l1, l2 with
    | [], _ | _, [] -> []
    | h1::t1, h2::t2 -> (h1,h2)::(product [h1] t2)@(product t1 l2)

(* function computes data races for one variable,
   and returns one pair of accesses if there is a data race between them *)
let compute_data_races_for_one_var accesses_to_var =
  let pairs_of_accesses = product accesses_to_var accesses_to_var in
  let redundant_loc_reduced = List.filter ~f:AccessEvent.predicate_loc pairs_of_accesses in
  let read_write_checked = List.filter ~f:AccessEvent.predicate_read_write redundant_loc_reduced in
  let threads_checked = List.filter ~f:AccessEvent.predicate_thread read_write_checked in
  let threads_intersection_checked = List.filter ~f:AccessEvent.predicate_threads_intersection threads_checked in
  let locksets_checked_one_element = List.find ~f:AccessEvent.predicate_locksets threads_intersection_checked in
  match locksets_checked_one_element with
  | None -> []
  | Some element -> [element]

(* function checks if there are any data races in the program
   by creating pairs of accesses and checking on which pairs data race could occur *)
let compute_data_races post =
  let accesses_list = AccessSet.elements post.accesses in
  let rec create_report lst_of_accesses report_acc =
    match lst_of_accesses with
    | [] -> report_acc
    | (access : AccessSet.elt) :: t -> (
      let access_var = AccessEvent.get_var access in
      let (accesses_to_var, other_accesses) = separate_lists access_var t [access] [] in
      let report_acc_new = compute_data_races_for_one_var accesses_to_var in
      create_report other_accesses (report_acc @ report_acc_new)
    )
  in create_report accesses_list []

(* abstract interpretation operators *)
(* <= function *)
let ( <= ) ~lhs ~rhs =
  let accesses_leq = AccessSet.leq ~lhs:lhs.accesses ~rhs:rhs.accesses in
  let threads_leq = ThreadSet.leq ~lhs:lhs.threads_active ~rhs:rhs.threads_active in
  let lockset_leq = Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset in
  let unlockset_leq = Lockset.leq ~lhs:lhs.unlockset ~rhs:rhs.unlockset in
  (* aliases, load_aliases, heap_aliases, locals? *)
  accesses_leq && threads_leq && lockset_leq && unlockset_leq

(* less-than-or-equal function *)
let leq ~lhs ~rhs = (<=) ~lhs ~rhs

(* function joins two abstract states *)
let join astate1 astate2 =
  let threads_active = ThreadSet.union astate1.threads_active astate2.threads_active in
  let threads_joined = ThreadSet.inter astate1.threads_joined astate2.threads_joined in
  let accesses = AccessSet.union astate1.accesses astate2.accesses in
  let lockset = Lockset.inter astate1.lockset astate2.lockset in
  let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
  let points_to = PointsToSet.union astate1.points_to astate2.points_to in
  let load_aliases = LoadAliasesSet.union astate1.load_aliases astate2.load_aliases in
  let heap_points_to = HeapPointsToSet.union astate1.heap_points_to astate2.heap_points_to in
  let locals = LocalsSet.union astate1.locals astate2.locals in
  { threads_active; threads_joined; accesses; lockset; unlockset; points_to; load_aliases; heap_points_to; locals }

(* widening function *)
let widen ~prev ~next ~num_iters:_ =
  join prev next

(* pretty print function *)
let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "\nthreads_active=%a" ThreadSet.pp astate.threads_active;
    F.fprintf fmt "\nthreads_joined=%a" ThreadSet.pp astate.threads_joined;
    F.fprintf fmt "\naccesses=%a" AccessSet.pp astate.accesses;
    F.fprintf fmt "\nlockset=%a" Lockset.pp astate.lockset;
    F.fprintf fmt "\nunlockset=%a" Lockset.pp astate.unlockset;
    F.fprintf fmt "\npoints_to=%a" PointsToSet.pp astate.points_to;
    F.fprintf fmt "\nheap_points_to=%a" HeapPointsToSet.pp astate.heap_points_to;
    F.fprintf fmt "\nload_aliases=%a" LoadAliasesSet.pp astate.load_aliases;
    F.fprintf fmt "\nlocals=%a" LocalsSet.pp astate.locals;

(* type of the summary *)
type summary = t
