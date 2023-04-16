(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
 (* Data Race Checker Domain *)

open! IStd
module F = Format
module LockEvent = DeadlockDomain.LockEvent
module Lockset = DeadlockDomain.Lockset

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

end

module ThreadEvent = struct
  (* type of ThreadEvent *)
  type t = (AccessPath.t * Location.t * Bool.t)

  (* compare function *)
  let compare ((base, aclist) as th, loc, created_in_loop) ((base', aclist') as th', loc', created_in_loop') =
    (* F.printf "comparing threads: %a and %a\n" AccessPath.pp th AccessPath.pp th'; *)
    let result_th =
      (* compare access paths *)
      if (Int.equal (AccessPath.compare th th') 0) then 0
      else begin
        let res = AccessPath.compare_base base base' in
        if not (Int.equal res 0) then res
        else
          List.compare AccessPath.compare_access aclist aclist'
      end
    in
    if (Int.equal result_th 0) then
      (* compare loc *)
      if (Int.equal (Location.compare loc loc') 0) then
        (* compare created_in_loop flag *)
        match (created_in_loop, created_in_loop') with
        | (true, false) -> 1
        | (false, true) -> -1
        | _ -> 0
      else
        Location.compare loc loc'
    else
      result_th

  (* function creates a main thread *)
  let create_main_thread =
    let pname = Procname.from_string_c_fun "main" in
    let pvar_from_pname : Pvar.t = Pvar.mk_tmp "'main_thread'" pname in
    let tvar_name = Typ.TVar "thread" in
    let typ_main_thread = Typ.mk tvar_name in
    let acc_path_from_pvar : AccessPath.t = AccessPath.of_pvar pvar_from_pname typ_main_thread in
    (acc_path_from_pvar, Location.dummy, false)

  (* pretty print function *)
  let pp fmt (th, loc, created_in_loop) =
    F.fprintf fmt "%a on %a, in_loop=%b" AccessPath.pp th Location.pp loc created_in_loop

  (* pretty print function - shorter version used for reporting *)
  let pp_short fmt ((th, loc, created_in_loop) as thread) =
    let main_thread = create_main_thread in
    if (Int.equal (compare main_thread thread) 0) then
      F.fprintf fmt "main thread"
    else
      match created_in_loop with
      | true -> F.fprintf fmt "thread %a created on %a in loop" AccessPath.pp th Location.pp_line loc
      | false -> F.fprintf fmt "thread %a created on %a" AccessPath.pp th Location.pp_line loc

end

module ThreadSet = AbstractDomain.FiniteSet(ThreadEvent)

module Aliases = struct
  (* type of Aliases *)
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t)

  (* compare function *)
  let compare t1 t2 =
    let fst_compare = HilExp.AccessExpression.compare (fst t1) (fst t2) in
    let snd_compare = HilExp.AccessExpression.compare (snd t1) (snd t2) in
    if not (Int.equal fst_compare 0) then
      fst_compare
    else
      snd_compare

  (* pretty print function *)
  let pp fmt (f, s) =
    F.fprintf fmt "(%a, %a)" HilExp.AccessExpression.pp f HilExp.AccessExpression.pp s

end

module AliasesSet = AbstractDomain.FiniteSet(Aliases)

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
    thread: ThreadEvent.t option;
  }

  (* function prints a thread option *)
  let print_thread thread_opt =
    match thread_opt with
    | None -> F.printf "on thread None"
    | Some thread -> F.printf "on thread %a" ThreadEvent.pp thread

  (* function prints an access pair *)
  let print_access_pair (t1, t2) =
    let t1_access_string = ReadWriteModels.access_to_string t1.access_type in
    F.printf "(%a, %a, %s, %a " HilExp.AccessExpression.pp t1.var Location.pp t1.loc t1_access_string ThreadSet.pp t1.threads_active;
    print_thread t1.thread;
    (* print_lockset t1; *)
    F.printf "\n";
    let t2_access_string = ReadWriteModels.access_to_string t2.access_type in
    F.printf "| %a, %a, %s, %a " HilExp.AccessExpression.pp t2.var Location.pp t2.loc t2_access_string ThreadSet.pp t2.threads_active;
    print_thread t2.thread;
    (* print_lockset t2; *)
    F.printf ")\n-----\n"

  (* compare function *)
  let compare a1 a2 =
    let var_cmp = HilExp.AccessExpression.compare a1.var a2.var in
    let loc_cmp = Location.compare a1.loc a2.loc in
    let access_type_cmp = ReadWriteModels.compare a1.access_type a2.access_type in
    let locked_cmp = Lockset.compare a1.locked a2.locked in
    let unlocked_cmp = Lockset.compare a1.unlocked a2.unlocked in
    let threads_active_cmp = ThreadSet.compare a1.threads_active a2.threads_active in
    let thread_cmp =
      match a1.thread with
      | Some thread1 -> (
        match a2.thread with
        | Some thread2 -> ThreadEvent.compare thread1 thread2
        | None -> 1
      )
      | None -> (
        match a2.thread with
        | Some _ -> -1
        | None -> 0
      )
    in
    if not (Int.equal var_cmp 0) then
      var_cmp
    else if not (Int.equal access_type_cmp 0) then
      access_type_cmp
    else if not (Int.equal thread_cmp 0) then
      thread_cmp
    else if not (Int.equal threads_active_cmp 0) then
      threads_active_cmp
    else if not (Int.equal locked_cmp 0) then
      locked_cmp
    else if not (Int.equal unlocked_cmp 0) then
      unlocked_cmp
    else
      loc_cmp

  (* pretty print *)
  let pp fmt t1 =
    F.fprintf fmt "{%a, %s, %a, " HilExp.AccessExpression.pp t1.var (ReadWriteModels.access_to_string t1.access_type) Location.pp_line t1.loc;
    match t1.thread with
    | Some t -> F.fprintf fmt "thread %a}" ThreadEvent.pp_short t
    | None -> F.fprintf fmt "None thread}"

  (* pretty print function - shorter version used for reporting *)
  let pp_report_short fmt t1 =
    F.fprintf fmt "%s %a on %a on " (ReadWriteModels.access_to_string t1.access_type) HilExp.AccessExpression.pp t1.var Location.pp_line t1.loc;
    match t1.thread with
    | Some t -> F.fprintf fmt "%a" ThreadEvent.pp_short t
    | None -> F.fprintf fmt "unknown thread"

  (* function returns access.var *)
  let get_var access = access.var

  (* function returns access.loc *)
  let get_loc access = access.loc

  (* function returns access with updated locks and threads,
     and access with None thread updates with the thread in arguments *)
  let update_accesses_with_locks_and_threads threads_active lockset unlockset thread access =
    let locked = Lockset.diff (Lockset.union lockset access.locked) access.unlocked in
    let unlocked = Lockset.union (Lockset.diff unlockset access.locked) access.unlocked in
    let threads_active = ThreadSet.union threads_active access.threads_active in
    let thread =
      match access.thread with
      | None -> thread
      | Some th -> Some th
    in
    { var=access.var; loc=access.loc; access_type=access.access_type; locked; unlocked; threads_active; thread }

  (* function replaces the base in var with actual,
     it must to be recursive to keep the same "format" as the original var was (e.g. **x, *x, &x) *)
  let rec replace_base_of_var_with_another_var var actual =
    F.printf "replace_base_of_var_with_another_var: var=%a, actual=%a\n" HilExp.AccessExpression.pp var HilExp.AccessExpression.pp actual;
    let replace_base_inner = replace_base_of_var_with_another_var actual in
    match var with
    | HilExp.AccessExpression.Dereference (Base _) -> (* *v -> *a *)
      HilExp.AccessExpression.dereference actual
    | HilExp.AccessExpression.Dereference ae -> (* *( *v) -> *(...) *)
      HilExp.AccessExpression.dereference (replace_base_inner ae)
    | HilExp.AccessExpression.AddressOf (Base _) -> ((* &v -> &a *)
      match HilExp.AccessExpression.address_of actual with
      | Some address_of -> address_of
      | None -> actual
    )
    | HilExp.AccessExpression.AddressOf ae -> ( (* &( *v) -> &(...) *)
      let address_of_option = HilExp.AccessExpression.address_of (replace_base_inner ae) in
      match address_of_option with
      | Some address_of -> address_of
      | None -> ae
    )
    | HilExp.AccessExpression.FieldOffset (ae, fieldname) -> (
      F.printf "replace_base_of_var_with_another_var2: ae: %a, fieldname: %a\n" HilExp.AccessExpression.pp ae Fieldname.pp fieldname;
      (* rekurzivne replacnout ae with another var a pridat fieldname *)
      let final_ae = (replace_base_of_var_with_another_var ae actual) in
      let final = HilExp.AccessExpression.field_offset final_ae fieldname in
      F.printf "replace_base_of_var_with_another_var2: ae after: %a\n" HilExp.AccessExpression.pp final;
      final
      (* actual *)
    )
    | _ -> actual

  (* function replaces the var in access by another var (actual), if the var equals formal *)
  let edit_access_with_actuals formal actual access =
    (* get base (as access_expression) of access.var *)
    let access_var_base = HilExp.AccessExpression.get_base access.var in
    let access_var_base_ae = HilExp.AccessExpression.base access_var_base in
    (* check if the var equals formal *)
    if HilExp.AccessExpression.equal access_var_base_ae formal then
      match actual with
      | HilExp.AccessExpression actual_ae ->
        (* replace base of the var with actual *)
        let replaced_var = replace_base_of_var_with_another_var access.var actual_ae in
        { access with var=replaced_var }
      | _ -> (* TODO don't use the access *)
        F.printf "Not an AccessExpression in procedure edit_access_with_actuals in DarcDomain.ml\n";
        access
    else  (* TODO don't use the access *)
      access

  (* function returns true if a1.loc is lower or equal than a2.loc *)
  let predicate_loc (a1, a2) =
    if Location.compare a1.loc a2.loc <= 0 then true else false

  (* function returns true if a1.var == a2.var *)
  let predicate_var (a1, a2) =
    if Int.equal (HilExp.AccessExpression.compare a1.var a2.var) 0 then true else false

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

  (* FIXME *)
  (* function returns true if there is at least one thread in the intersection of threads_active,
     and if at least one of the threads in the intersection is the thread on which an access occurred *)
  let predicate_threads_intersection (a1, a2) =
    let intersection = ThreadSet.inter a1.threads_active a2.threads_active in
    if (ThreadSet.cardinal intersection) > 1 then
      begin
        match (a1.thread, a2.thread) with
        | (Some a1_thread, Some a2_thread) -> (
          (* there are more threads running concurrently - check if any of these threads equals a1.thread or a2.thread *)
          let a1_in_intersection = ThreadSet.mem a1_thread intersection in
          (* F.printf "a1_in_intersection: %b\n" a1_in_intersection; *)
          let a2_in_intersection = ThreadSet.mem a2_thread intersection in
          (* F.printf "a2_in_intersection: %b\n" a2_in_intersection; *)
          a1_in_intersection || a2_in_intersection
        )
        | _ -> false (* at least one of the threads is None -> FIXME *)
      end
    else
      false (* the only thread in the intersection is main -> data race cannot occur *)


  (* function returns true if the intersection of locked locks is empty *)
  let predicate_locksets (a1, a2) = (* intersect ls1 ls2 == {} -> false *)
    let intersect = Lockset.inter a1.locked a2.locked in
    if Lockset.equal intersect Lockset.empty then true else false

end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

type t =
{
  threads_active: ThreadSet.t;
  accesses: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  unlockset: Lockset.t;
  aliases: AliasesSet.t;
  load_aliases: (HilExp.AccessExpression.t * HilExp.AccessExpression.t) list;
  heap_aliases: (HilExp.AccessExpression.t * Location.t) list;
(*  locals: (Mangled.t * Typ.t) list; (* TODO maybe use HilExp.AccessExpression.t? *)*)
  locals: HilExp.AccessExpression.t list;
}

let empty =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  aliases = AliasesSet.empty;
  load_aliases = [];
  heap_aliases = [];
  locals = [];
}

let empty_with_locals locals =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  aliases = AliasesSet.empty;
  load_aliases = [];
  heap_aliases = [];
  locals;
}

(* print functions *)
let print_load_aliases (ae1, ae2) =
  F.printf "(%a, %a)\n" HilExp.AccessExpression.pp ae1 HilExp.AccessExpression.pp ae2

let _print_load_aliases_list astate =
  let rec print list =
     match list with
     | [] -> F.printf ".\n";
     | h::t -> print_load_aliases h; print t
   in
   print astate.load_aliases

let print_heap_aliases (ae, loc) =
  F.printf "(%a, %a), " HilExp.AccessExpression.pp ae Location.pp loc

let _print_heap_aliases_list astate =
  let rec print list =
     match list with
     | [] -> F.printf ".\n";
     | h::t -> print_heap_aliases h; print t
   in
   print astate.heap_aliases

let _print_alias alias = (
  match alias with
 | None -> F.printf "print_alias: None\n";
 | Some (fst, snd) -> F.printf "print_alias: %a\n" Aliases.pp (fst, snd);
 )

let _print_accesses accesses =
  F.printf "accesses: -----\n%a\n" AccessSet.pp accesses

let _print_alias_opt alias =
  F.printf "print_alias_opt...\n";
  match alias with
  | None -> F.printf "None\n"
  | Some (fst, snd) -> F.printf "(%a, %a)\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd

let print_locals astate =
  F.printf "locals: {";
  let rec print_vars = function
    | [] -> F.printf "}\n"
    | hd :: tl -> F.printf "%a, " HilExp.AccessExpression.pp hd; print_vars tl
(*    | hd :: tl ->*)
(*      let typ_string = Typ.to_string (snd hd) in*)
(*      F.printf "|(%a, %s)|" Mangled.pp (fst hd) typ_string; print_vars tl*)
  in
  print_vars astate.locals

let _print_astate_all astate loc caller_pname =
  F.printf "========= printing astate... ==========\n";
  F.printf "access=%a\n" AccessSet.pp astate.accesses;
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
  F.printf "caller_pname=%a\n" Procname.pp caller_pname;
  F.printf "loc=%a\n" Location.pp loc;
  print_locals astate;
  F.printf "=======================================\n"

let _print_formals formals =
  F.printf "print_formals: \n";
  let rec loop = function
    | [] -> F.printf "\n"
    | (mangled, typ) :: tl ->
      (*
      let print_type typ =
        match typ with
        | Tptr -> F.printf "Tptr\n";
        | Tfun -> F.printf "Tfun\n";
        | Tvar -> F.printf "Tvar\n";
        | _ -> F.printf "Tother\n";
      in
      print_type typ;
      *)
      let typ_string = Typ.to_string typ in
      (* F.printf "typ: %s\n" (Typ.to_string typ); *)
      let _is_ptr =
        if (Typ.is_pointer typ) then
          F.printf "is pointer\n"
        else
          F.printf "isn't pointer\n"
      in
      F.printf "| (%a," IR.Mangled.pp mangled; F.printf " %s) |" typ_string; loop tl
  in loop formals

let _print_actuals actuals =
  F.printf "print_actuals: \n";
  let rec loop = function
    | [] -> F.printf "\n"
    | hd :: tl -> F.printf "| %a |" HilExp.pp hd; loop tl
  in loop actuals

let print_astate astate  =
  (* F.printf "========= printing astate... ==========\n"; *)
  F.printf "access=%a\n" AccessSet.pp astate.accesses;
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
  F.printf "heap_aliases=";
  _print_heap_aliases_list astate
  (* F.printf "caller_pname=%a\n" Procname.pp caller_pname; *)
  (* F.printf "loc=%a\n" Location.pp loc *)
  (* F.printf "=======================================\n" *)

let rec _print_ae_list ae_list =
  match ae_list with
  | [] -> F.printf ".\n"
  | h::t -> F.printf "%a, " Aliases.pp h; _print_ae_list t

let rec print_pairs_list lst =
  match lst with
  | [] -> F.printf "\n"
  | h::t -> AccessEvent.print_access_pair h; print_pairs_list t

(* functions that handle aliases *)
(* function returns base of var as access expression type *)
let get_base_as_access_expression var =
  let var_base = HilExp.AccessExpression.get_base var in
  let var_base_ae = HilExp.AccessExpression.base var_base in
  var_base_ae

let rec find_load_alias var aliases ~add_deref =
  F.printf "find_load_alias of var=%a: " HilExp.AccessExpression.pp var;
  match aliases with
  | [] -> None
  | (fst, snd) :: t ->
    F.printf "fst=%a, snd=%a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      match add_deref with
      | true -> Some (fst, HilExp.AccessExpression.dereference snd)
      | false -> Some (fst, snd)
    else
      find_load_alias var t ~add_deref

(* function returns Some alias if var participates in any alias in astate.aliases, or None,
   if add_deref is true, the second var in alias is returned as dereference *)
let rec find_alias var aliases ~add_deref =
  F.printf "find_alias of var=%a: " HilExp.AccessExpression.pp var;
  match aliases with
  | [] -> None
  | (fst, snd) :: t ->
    F.printf "fst=%a, snd=%a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      match add_deref with
      | true -> Some (fst, HilExp.AccessExpression.dereference snd)
      | false -> Some (fst, snd)
    else
      find_alias var t ~add_deref

let rec find_alias_list var aliases ~add_deref acc =
  F.printf "find_alias_list of var=%a: " HilExp.AccessExpression.pp var;
  match aliases with
  | [] -> acc
  | (fst, snd) :: t ->
    F.printf "fst=%a, snd=%a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      let alias_to_add =
        match add_deref with
        | true -> (fst, HilExp.AccessExpression.dereference snd)
        | false -> (fst, snd)
      in
      find_alias_list var t ~add_deref (alias_to_add :: acc)
    else
      find_alias_list var t ~add_deref acc

let rec find_load_alias_list var aliases ~add_deref acc =
  F.printf "find_load_alias_list of var=%a: " HilExp.AccessExpression.pp var;
  match aliases with
  | [] -> acc
  | (fst, snd) :: t ->
    F.printf "fst=%a, snd=%a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd;
    if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then
      let alias_to_add =
        match add_deref with
        | true -> (fst, HilExp.AccessExpression.dereference snd)
        | false -> (fst, snd)
      in
      let alias_eq (a, b) (a', b') =
        HilExp.AccessExpression.equal a a' && HilExp.AccessExpression.equal b b'
      in
      let updated_acc =
        match List.mem acc alias_to_add ~equal:alias_eq with
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
    let aliases_list = AliasesSet.elements astate.aliases in
    let rec remove_var_alias var lst acc =
      match lst with
      | [] -> acc
      | ((fst, _) as alias) :: t -> (
        if (HilExp.AccessExpression.equal fst var) then
          remove_var_alias var t acc
        else
          remove_var_alias var t (alias :: acc)
      )
    in
    let aliases_removed_list = remove_var_alias var aliases_list [] in
    let aliases_removed = AliasesSet.of_list aliases_removed_list in
    let heap_aliases_removed = remove_var_alias var astate.heap_aliases [] in
    {astate with aliases=aliases_removed; heap_aliases=heap_aliases_removed}
  )

(* function adds new alias to astate.aliases *)
let add_new_alias astate alias =
  match alias with
  | None -> astate
  | Some alias -> (
    let new_aliases = AliasesSet.add alias astate.aliases in
    { astate with aliases=new_aliases }
  )

(* function creates new alias option from fst and snd *)
let create_new_alias fst snd =
  match (fst, snd) with
  | (Some f, Some s) -> Some (f, s)
  | _ -> None

let rec resolve_alias_list lhs lhs_current var aliases =
  F.printf "resolve_alias_list: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
  (* if lhs matches lhs_current, end the recursion and return final alias/var *)
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      (* if lhs is dereference -> find new alias in aliases, else return var *)
      match lhs with
      | HilExp.AccessExpression.Dereference lhs_without_dereference ->
        find_alias_list lhs_without_dereference aliases ~add_deref:true [] (* e.g. None | Some (y, &k) *)
      | _ -> [] (* [(var, var)] *)
    end
  else
    begin
      (* find var in aliases and if found, continue recursion with the snd in alias *)
      let find_current_in_aliases = find_alias_list var aliases ~add_deref:false [] in (* e.g. None | Some (m, &y) *)
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | [] -> []
      | list -> (
        let rec resolve lst resolved_acc =
          match lst with
          | [] -> resolved_acc
          | (_, snd) :: t -> (
            let snd_dereference = HilExp.AccessExpression.dereference snd in
            let resolved_for_one = resolve_alias_list lhs lhs_dereference snd_dereference aliases in
            resolve t (resolved_for_one @ resolved_acc)
          )
        in
        resolve list []
      )
    end

(* function resolves alias by going through aliases (not heap aliases) *)
let rec resolve_alias lhs lhs_current var aliases =
  F.printf "resolve_alias: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
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

(* function resolves aliases of lhs recursively and returns None or Some (fst, &snd) (e.g. **y -> *u -> v: returns v for **y expression *)
let get_base_alias lhs aliases =
  let lhs_base_ae = get_base_as_access_expression lhs in
  resolve_alias lhs lhs_base_ae lhs_base_ae aliases

(* function returns alias of var if found in aliases, else returns var *)
let replace_var_with_its_alias var aliases =
  let var_ae = get_base_as_access_expression var in
  let result_option = resolve_alias var var_ae var_ae aliases in
  match result_option with
  | None -> var (* alias not found -> return the original var *)
  | Some (_, snd) -> snd (* alias found -> return the alias *)

(* function returns Some load_alias if there already is an alias in load_aliases *)
let rec find_load_alias_by_var var load_aliases =
  match load_aliases with
  | [] -> None
  | (fst, snd) :: t ->
    if HilExp.AccessExpression.equal var fst then
      Some (fst, snd)
    else
      find_load_alias_by_var var t

(* function resolves load alias *)
let resolve_load_alias exp load_aliases ~add_deref : HilExp.AccessExpression.t =
  let exp_base_ae = get_base_as_access_expression exp in
  let res =
    match exp with
    | HilExp.AccessExpression.AddressOf _ -> exp
    | _ -> (
      let alias = find_load_alias exp_base_ae load_aliases ~add_deref in
      match alias with
      | Some (_, snd) -> snd
      | None -> exp_base_ae
    )
  in
  (* transform res to same "format" as exp was (dereference, addressOf etc.) *)
  AccessEvent.replace_base_of_var_with_another_var exp res

let resolve_load_alias_list exp load_aliases ~add_deref : HilExp.AccessExpression.t list =
  let exp_base_ae = get_base_as_access_expression exp in
  F.printf "resolve_load_alias_list -> exp_base_ae: %a\n" HilExp.AccessExpression.pp exp_base_ae;
    match exp with
    | HilExp.AccessExpression.AddressOf _ -> [exp]
    | _ -> (
      let load_alias_list = find_load_alias_list exp_base_ae load_aliases ~add_deref [] in
      F.printf "resolve_load_alias_list, before match, exp_base_ae=%a\n" HilExp.AccessExpression.pp exp_base_ae;
      match load_alias_list with
      | [] -> [exp_base_ae]
      | list -> (
        let rec get_list_of_final_vars lst final_list_acc =
          match lst with
          | [] -> final_list_acc
          | (_, snd) :: t -> (
            F.printf "snd in resolve_load_alias_list\n";
            (* transform res to same "format" as exp was (dereference, addressOf etc.) *)
            let res = AccessEvent.replace_base_of_var_with_another_var exp snd in
            get_list_of_final_vars t (res :: final_list_acc)
          )
        in
        get_list_of_final_vars list []
      )
    )

(* function deletes all load_aliases from astate *)
let astate_with_clear_load_aliases astate = {astate with load_aliases=[]}

(* functions that handle heap aliases *)
(* function removes all heap aliases with the same loc (used when free() is called) *)
let remove_heap_aliases_by_loc loc astate =
  let rec update_heap_aliases loc list acc =
    match list with
    | [] -> acc
    | (var, location) :: t -> (
      if Location.equal loc location then
        update_heap_aliases loc t acc
      else
        begin
          let new_acc = (var, location) :: acc in
          update_heap_aliases loc t new_acc
        end
    )
  in
  update_heap_aliases loc astate.heap_aliases []

let get_heap_aliases_list_by_loc loc heap_aliases =
  let rec find_heap_aliases loc list acc =
    match list with
    | [] -> acc
    | (var, location) :: t ->
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
  | (fst, loc) :: t ->
    if HilExp.AccessExpression.equal var fst then
      Some loc
    else
      find_heap_alias_by_var var t

(* function removes heap alias of var *)
let remove_heap_alias_by_var_name var astate =
  (* find var alias in heap_aliases, return loc *)
  let loc_of_alias_to_be_removed = find_heap_alias_by_var var astate.heap_aliases in
  match loc_of_alias_to_be_removed with
  | Some loc ->
    (* remove all heap_aliases with the returned loc *)
    let updated_heap_aliases = remove_heap_aliases_by_loc loc astate in
    { astate with heap_aliases=updated_heap_aliases }
  | None -> astate (* heap alias with var doesn't exist *)

(* function adds new heap alias to astate.heap_aliases,
   if there already is an alias with variable var, the old alias is first removed *)
let add_heap_alias var loc astate =
  let new_heap_alias = (var, loc) in
  (* remove heap alias if there already is any alias with the var *)
  let astate = remove_heap_alias_by_var_name var astate in
  (* add new alias to heap aliases *)
  let new_heap_aliases = new_heap_alias :: astate.heap_aliases in
  {astate with heap_aliases = new_heap_aliases}

(* functions joins astate.heap_aliases with heap_aliases *)
let add_heap_aliases_to_astate astate heap_aliases =
  let heap_aliases_joined = astate.heap_aliases @ heap_aliases in
  {astate with heap_aliases=heap_aliases_joined}

(* function returns first variable in a tuple or var if the tuple is None *)
let get_option_fst var alias = (
  match alias with
  | None -> Some var
  | Some (fst, _) -> Some fst
)

(* function returns second variable in a tuple or None if the tuple is None *)
let get_option_snd alias = (
  match alias with
  | None -> None
  | Some (_, snd) -> Some snd
)

(* function updates aliases and heap aliases with (lhs = rhs) expression *)
let update_aliases lhs rhs astate =
  F.printf "update_aliases: lhs=%a, rhs=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp rhs;
  let aliases = AliasesSet.elements astate.aliases in
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
    let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
    add_new_alias astate_alias_removed new_alias
  )
  | _ -> (  (* base, dereference etc. *)
    (* check if there already is some alias for the rhs expression *)
    F.printf ":---\n";
    print_astate astate;
    F.printf "---:\n";
    let rhs_alias = get_base_alias rhs aliases in (* *q -> Some (x, &z) *)
    match rhs_alias with
    | Some _ -> ( (* alias was found *)
      F.printf "rhs alias Some\n";
      (* get the second variable in rhs_alias and create new alias *)
      let rhs_alias_snd = get_option_snd rhs_alias in (* Some (x, &z) -> Some &z *)
      let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in
      (* remove existing lhs_alias and add the new alias to astate *)
      let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
      add_new_alias astate_alias_removed new_alias
    )
    | None -> ( (* alias wasn't found - try to find alias in heap aliases *)
      F.printf "rhs alias None\n";
      (* find rhs in heap aliases *)
      let rhs_heap_alias_loc = find_heap_alias_by_var rhs astate.heap_aliases in
      match rhs_heap_alias_loc with
      | Some loc -> (
        (* remove existing alias from aliases and add the new alias to astate *)
        let astate_alias_removed = remove_all_var_aliases_from_aliases lhs_alias_fst astate in
        add_heap_alias lhs loc astate_alias_removed
        )
      | None -> astate (* alias doesn't exist *)
    )
  )


(* function returns alias of var if found in aliases, else returns var *)
let replace_var_with_its_alias_list var aliases (heap_aliases : (HilExp.access_expression * Location.t) list) =
  let var_ae = get_base_as_access_expression var in
  let result_list = resolve_alias_list var var_ae var_ae aliases in
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
      | [] -> [var]
      | lst -> (
        let rec for_each_in_list_get_right_format list acc =
          match list with
          | [] -> acc
          | h :: t -> (
            let right_format_var = AccessEvent.replace_base_of_var_with_another_var var h in
            for_each_in_list_get_right_format t (right_format_var :: acc)
          )
        in
        for_each_in_list_get_right_format lst []
      )
    )
    | None -> (
      (* not found -> return original var *)
      [var]
    )
  )
  | list -> (
    let rec get_list_of_snd lst acc =
      match lst with
      | [] -> acc
      | (_, snd) :: t -> (
        get_list_of_snd t (snd :: acc) (* alias found -> return the alias *)
      )
    in
    get_list_of_snd list []
  )



let resolve_entire_aliasing_of_var_list e_ae astate ~add_deref =
  (* get list of load aliases, e.g. (n$1, i), (n$1, j) *)
  let e_after_resolving_load_alias_list = resolve_load_alias_list e_ae astate.load_aliases ~add_deref in
  (* for each load alias *)
  let rec for_each_load_alias lst acc =
    match lst with
    | [] -> acc
    | e_after_resolving_load_alias :: t -> (
      F.printf "e_after_resolving_load_alias 1: %a\n" HilExp.AccessExpression.pp e_after_resolving_load_alias;
      (* get list of all aliased variables *)
      let e_final_list = replace_var_with_its_alias_list e_after_resolving_load_alias (AliasesSet.elements astate.aliases) astate.heap_aliases in
      (* create list of (e_after_resolving_load_alias, e_final) pairs *)
      let rec create_list_of_aliased_vars lst cacc =
        match lst with
        | [] -> cacc
        | var :: t -> (F.printf "var 1: %a\n" HilExp.AccessExpression.pp var; create_list_of_aliased_vars t ((e_after_resolving_load_alias, var) :: cacc) )
      in
      (* if the list is empty try to find in heap_aliases *)
        match e_final_list with
        | [] -> (
          let e_final_list_heap = replace_var_with_its_alias_list e_after_resolving_load_alias (AliasesSet.elements astate.aliases) astate.heap_aliases in
          let new_heap_acc = create_list_of_aliased_vars e_final_list_heap acc in
          for_each_load_alias t new_heap_acc
        )
        | _ -> (
          let new_acc = create_list_of_aliased_vars e_final_list acc in
          for_each_load_alias t new_acc
        )
    )
  in
  for_each_load_alias e_after_resolving_load_alias_list []

(* function resolves load alias of e_ae and then other aliases (FIXME not heap aliases) *)
let resolve_entire_aliasing_of_var e_ae astate ~add_deref =
  let e_after_resolving_load_alias = resolve_load_alias e_ae astate.load_aliases ~add_deref in
  let e_final = replace_var_with_its_alias e_after_resolving_load_alias (AliasesSet.elements astate.aliases) in
  (e_after_resolving_load_alias, e_final)

(* functions that handle threads *)
(* function returns None or Some (thread, loc, false) *)
let create_thread_from_load_ae_with_false_flag load loc astate =
  (* load expression dealiasing *)
  let thread_load_alias = find_load_alias_by_var load astate.load_aliases in
  match thread_load_alias with
  | None -> (
    let load_ap = HilExp.AccessExpression.to_access_path load in
    (load_ap, loc, false)
  )
  | Some (_, final_thread) -> (
    (* create new thread from alias *)
    let final_thread_ap = HilExp.AccessExpression.to_access_path final_thread in
    (final_thread_ap, loc, false)
  )

(* function created new thread from load alias *)
let new_thread th_load_ae loc astate =
  (* dealiasing load expression *)
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

(* function add thread to astate.threads_active,
   if there already is the thread with false created_in_loop flag, adds it with true flag *)
let add_thread thread astate =
  (* find thread in threads_active *)
  let found_with_false_flag = ThreadSet.mem thread astate.threads_active in
  let threads_active =
    match found_with_false_flag with
    | false -> ThreadSet.add thread astate.threads_active
    | true -> (
      (* if found then find the same thread with true *)
      let (th, loc, _) = thread in
      let thread_with_true = (th, loc, true) in
      let found_with_true_flag = ThreadSet.mem thread_with_true astate.threads_active in
      (* add the thread if it is not already present in astate.threads_active *)
      match found_with_true_flag with
      | false -> ThreadSet.add thread_with_true astate.threads_active
      | true -> astate.threads_active
    )
  in
  { astate with threads_active }

(* function finds thread in threads set and returns None if not found or Some thread if found *)
let find_thread_in_threads_active thread_name threads ~created_in_loop_flag =
  let threads_list : (AccessPath.t * Location.t * Bool.t) list = ThreadSet.elements threads in
  let rec find_thread lst =
    match lst with
    | [] -> None
    | (th_ap, _, flag) as th :: t -> (
      if (AccessPath.equal th_ap thread_name) && (Bool.equal flag created_in_loop_flag) then
        Some th
      else
        find_thread t
    )
  in
  find_thread threads_list

(* function tries to find thread with flag created_in_loop set to true in astate.threads_active,
   if found then removes it, if not found, tries to find the thread with false flag and removes it *)
let remove_thread load_ae astate =
  (* find thread by its name in threads *)
  let thread_load_alias = find_load_alias_by_var load_ae astate.load_aliases in
  match thread_load_alias with
  | None -> astate (* not found *)
  | Some (_, thread_ae) -> (
    let thread_name = HilExp.AccessExpression.to_access_path thread_ae in
    (* find the thread in threads_active - first find with true flag *)
    let thread_with_true_flag = find_thread_in_threads_active thread_name astate.threads_active ~created_in_loop_flag:true in
    (* if found then remove *)
    match thread_with_true_flag with
    | Some th -> (
      (* remove the thread *)
      let threads_active = ThreadSet.remove th astate.threads_active in
      { astate with threads_active }
    )
    | None -> (
      (* else find the thread with false flag *)
      let thread = find_thread_in_threads_active thread_name astate.threads_active ~created_in_loop_flag:false in
      match thread with
      | Some th ->
        (* remove the thread *)
        let threads_active = ThreadSet.remove th astate.threads_active in
        { astate with threads_active }
      | None -> astate
    )
  )

(* function returns empty astate with main thread in threads_active *)
let initial_main locals =
  let empty_astate = empty_with_locals locals in
  let main_thread = ThreadEvent.create_main_thread in
  (* add the main thread to an empty astate *)
  let threads_active = ThreadSet.add main_thread empty_astate.threads_active in
  { empty_astate with threads_active }

(* function transforms SIL expression to HIL expression *)
let transform_sil_expr_to_hil sil_exp sil_typ add_deref =
  let f_resolve_id _ = None in
  let hil_expr = HilExp.of_sil ~include_array_indexes:false ~f_resolve_id ~add_deref sil_exp sil_typ in
  hil_expr

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
  in
  transform_sil_to_hil_actuals sil_expr_list []

(* f_ae je load expression struktury *)
let resolve_entire_aliasing_of_var_for_lfield_list e_ae astate  ~add_deref =
  F.printf "resolve_entire_aliasing_of_var_for_lfield_list e_ae=%a\n" HilExp.AccessExpression.pp e_ae;
  let ae_fields_list =
    match e_ae with
    | HilExp.AccessExpression.FieldOffset (fieldoffset_ae, fieldname)-> (
      F.printf "resolve_entire_aliasing_of_var_for_lfield_list-FieldOffset: (%a, %a)\n" HilExp.AccessExpression.pp fieldoffset_ae Fieldname.pp fieldname;
      (* ziskat list aliasu toho fieldoffset_ae *)
      let lst = resolve_entire_aliasing_of_var_list fieldoffset_ae astate ~add_deref in (* lst je ve tvaru [(e_aliased, e_aliased_final)] *)
      (* pro kazdy prvek z listu vytvorit ae s fieldname *)
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
      (* return list *)
      lst_with_fieldnames
    )
    | _ -> (
      F.printf "resolve_entire_aliasing_of_var_for_lfield_list-Other\n";
      []
    )
  in
  let rec print_list_of_vars lst =
    match lst with
    | [] -> F.printf "\n"
    | (h_fst, h_snd) :: t -> (
      F.printf "(%a,%a) " HilExp.AccessExpression.pp h_fst HilExp.AccessExpression.pp h_snd;
      print_list_of_vars t
    )
  in
  F.printf "ae_fields_list: \n";
  print_list_of_vars ae_fields_list;
  ae_fields_list



(* function returns Some var if var is present in locals, or else returns None *)
let find_var_in_list var locals =
  let rec find_in_list lst =
    match lst with
    | [] -> None
    | h :: t ->
      if (HilExp.AccessExpression.equal var h) then Some h else find_in_list t
  in find_in_list locals

(* function returns list of locals without var *)
let remove_var_from_locals actual locals =
  match actual with
  | HilExp.AccessExpression actual_ae -> (
    let actual_base_ae = get_base_as_access_expression actual_ae in
    F.printf "remove_var_from_locals: actual_base_ae: %a\n" HilExp.AccessExpression.pp actual_base_ae;
    (* check if the var is in locals *)
    let is_in_locals = List.mem locals actual_base_ae ~equal:HilExp.AccessExpression.equal in
    (* remove var from locals *)
    let rec remove_from_locals var locals acc =
      F.printf "removing from locals: %a\n" HilExp.AccessExpression.pp var;
      match locals with
      | [] -> acc
      | h :: t ->
        if (HilExp.AccessExpression.equal h var) then
          acc @ t
        else
          remove_from_locals var t (h :: acc)
    in
    (* if var is in locals, remove it *)
    match is_in_locals with
    | false -> locals
    | true -> remove_from_locals actual_base_ae locals []
  )
  | _ -> locals

(* functions that handle adding/removing accesses *)
(* function adds new access to var to astate *)
let add_access_to_astate var access_type astate loc pname =
  let new_access : AccessEvent.t =
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread =
      (* TODO check equality to the entry point (not only main) *)
      if (Int.equal (String.compare (Procname.to_string pname) "main") 0) then
        Some (ThreadEvent.create_main_thread)
      else
        None
    in
    { var; loc; access_type; locked; unlocked; threads_active; thread }
  in
  F.printf "add_access_to_astate: %a\n" AccessEvent.pp new_access;
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
      let is_local = find_var_in_list var_base_ae astate.locals in
      match is_local with
      | Some _ -> astate (* local won't be added to accesses *)
      | None -> add_access_to_astate var access_type astate loc pname
    end

(* function adds new access to astate and updates the list of tmp_heap,
   that is used when dynamically allocating memory *)
let add_access_with_heap_alias_when_malloc e1_ae e2_ae loc astate tmp_heap pname =
  let rec update_astate_and_tmp_heap updated_astate tmp_heap updated_tmp_heap =
    match tmp_heap with
    | [] -> (updated_astate, updated_tmp_heap)
    | (var, loc) :: t ->
      (* check if the var is equal to e2_ae *)
      if (HilExp.AccessExpression.equal var e2_ae) then
        begin
          (* create (e1_ae, loc), add it to astate.heap_aliases, don't add (var, loc) to acc and continue with t *)
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
  let loc_opt = find_heap_alias_by_var var_base_ae astate.heap_aliases in
  let rec get_list_of_vars_with_loc loc (heap_aliases : (HilExp.access_expression * Location.t) list) acc =
    match heap_aliases with
    | [] -> acc
    | (var_found, loc_found) :: t ->
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
  | Some loc -> get_list_of_vars_with_loc loc astate.heap_aliases []

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

(* function removes all accesses to formal parameter of a function
   (used when the actual parameter is NULL in function call *)
let remove_accesses_to_formal formal accesses : AccessSet.t =
  (* create base of formal *)
  let formal_base = HilExp.AccessExpression.get_base formal in
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
  AccessSet.of_list accesses_list_with_removed_accesses

(* functions that handle locks *)
(* function adds a lock to lockset and removes it from unlockset *)
let acquire_lock lockid astate loc =
  (* dealiasing *)
  match lockid with
  | HilExp.AccessExpression e_ae -> (
    let (_, e_aliased_final) = resolve_entire_aliasing_of_var e_ae astate ~add_deref:true in
    let lockid = HilExp.AccessExpression.to_access_path e_aliased_final in
    (* add the lock *)
    let lock : LockEvent.t = (lockid, loc) in
    F.printf "adding lock: %a\n" LockEvent.pp lock;
    let new_astate : t =
      let lockset = Lockset.add lock astate.lockset in
      let unlockset = Lockset.remove lock astate.unlockset in
      { astate with lockset; unlockset }
    in
    new_astate
  )
  | _ -> astate

(* function removes lock from lockset and adds it to unlockset *)
let release_lock lockid astate loc =
  (* dealiasing *)
  match lockid with
  | HilExp.AccessExpression e_ae -> (
    let (_, e_aliased_final) = resolve_entire_aliasing_of_var e_ae astate ~add_deref:true in
    let lockid = HilExp.AccessExpression.to_access_path e_aliased_final in
    (* remove the lock *)
    let lock : LockEvent.t = (lockid, loc) in
    F.printf "removing lock: %a\n" LockEvent.pp lock;
    let new_astate : t =
      let lockset = Lockset.remove lock astate.lockset in
      let unlockset = Lockset.add lock astate.unlockset in
      { astate with lockset; unlockset }
    in
    new_astate
  )
  | _ -> astate

(* function handles load expression *)
let load id_ae e_ae e (_typ: Typ.t) loc astate pname =
  F.printf "load_aliases: \n";
  _print_load_aliases_list astate;
  (* for each load alias *)
      let rec add_load_alias_and_accesses l updated_astate =
        F.printf "add_load_alias_and_accesses: \n";
        print_astate updated_astate;
        match l with
        | [] -> updated_astate
        | (e_aliased, e_aliased_final) :: t -> (
          (* create new load alias *)
          let new_load_alias = (id_ae, e_aliased_final) in
          (* check if the load alias already exist *)
          let load_alias_eq (a, b) (a', b') =
            HilExp.AccessExpression.equal a a' && HilExp.AccessExpression.equal b b'
          in
          let load_aliases =
            match List.mem updated_astate.load_aliases new_load_alias ~equal:load_alias_eq with
            | false -> new_load_alias :: updated_astate.load_aliases
            | true -> updated_astate.load_aliases
          in
          (* add new load alias to load_aliases *)
          let astate = { updated_astate with load_aliases } in
          (* add all read access (if it is access to heap allocated variable with alias, there could be more accesses) *)
          F.printf "load:add_load_alias_and_accesses: e_aliased=%a e_aliased_final=%a\n" HilExp.AccessExpression.pp e_aliased HilExp.AccessExpression.pp e_aliased_final;
          let new_updated_astate = add_accesses_to_astate_with_aliases_or_heap_aliases e_aliased e_aliased_final ReadWriteModels.Read astate loc pname in
          F.printf "new_updated_astate: \n";
          print_astate new_updated_astate;
          F.printf "new_updated_astate end--- \n";
          add_load_alias_and_accesses t new_updated_astate
        )
  in
  match e with
  | Exp.Var _ -> (
    F.printf "Var\n";
    (* e is Var (e.g. n$0) -> it should already be present in load_aliases -> resolve it *)
    let lst = resolve_entire_aliasing_of_var_list e_ae astate ~add_deref:false in (* lst je ve tvaru [(e_aliased, e_aliased_final)] *)
    (* for each load alias *)
    add_load_alias_and_accesses lst astate
  )
  | Exp.Lvar _ -> (
    F.printf "Lvar\n";
    (* e is program var -> create new load alias (pvar, load_expr) and add it to astate.load_aliases *)
    let new_load_alias = (id_ae, e_ae) in
    let load_aliases = new_load_alias :: astate.load_aliases in
    let astate = { astate with load_aliases } in
    (* add read access to e *)
    add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname
  )
  | Exp.Lfield (exp, fieldname, _lfield_typ) -> (
    F.printf "Lfield exp: %a fieldname: %a\n" Exp.pp exp Fieldname.pp fieldname;
    (* FIXME do it recursively! *)
    let lst = resolve_entire_aliasing_of_var_for_lfield_list e_ae astate ~add_deref:true in
    add_load_alias_and_accesses lst astate
  )
  | Exp.Lindex _ -> (
      F.printf "Lindex\n";
      (* e is program var -> create new load alias (pvar, load_expr) and add it to astate.load_aliases *)
      let new_load_alias = (id_ae, e_ae) in
      let load_aliases = new_load_alias :: astate.load_aliases in
      let astate = { astate with load_aliases } in
      (* add read access to e *)
      add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname
    )
  | _ -> (
    F.printf "another Exp type\n";
    (* create new load alias and add it to the astate.load_aliases *)
    let new_load_alias = (id_ae, e_ae) in
    let load_aliases = new_load_alias :: astate.load_aliases in
    let astate = { astate with load_aliases } in
    (* add read access to e *)
    add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname
  )

(* function handles store expression *)
let store e1 typ e2 loc astate pname =
  let add_deref =
    match e1 with
    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> true (* e.g. p, *p *)
    | Exp.Var _ | _ -> false (* e.g. n$0 *)
  in
  let e1_hil = transform_sil_expr_to_hil e1 typ add_deref in
  match e1_hil with
  | HilExp.AccessExpression ((FieldOffset _) as e1_ae ) -> (
    let lst = resolve_entire_aliasing_of_var_for_lfield_list e1_ae astate ~add_deref:true in
    let rec add_accesses_for_each_aliased_var lst updated_astate =
      match lst with
      | [] -> updated_astate
      | (e1_aliased, e1_aliased_final) :: t -> (
        let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final ReadWriteModels.Write updated_astate loc pname in
        add_accesses_for_each_aliased_var t astate
      )
    in
    add_accesses_for_each_aliased_var lst astate
  )
  | AccessExpression e1_ae -> (
    (* add write_accesses TODO transform to _list function *)
    let (e1_aliased, e1_aliased_final) = resolve_entire_aliasing_of_var e1_ae astate ~add_deref:true in
    let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final ReadWriteModels.Write astate loc pname in
    (* if the type is pointer, add aliases to e2 *)
    if (Typ.is_pointer typ) then
      begin
        (* check null on the rhs *)
        if (Exp.is_null_literal e2) then
          (* remove aliases of e1_aliased_final *)
          remove_all_var_aliases_from_aliases (Some e1_aliased_final) astate
        else
          begin
            (* add alias *)
            let add_deref = false in
            let e2_exp =
              match e2 with
              | Exp.Cast (_, cast_exp) -> cast_exp (* handle Cast *)
              | _ -> e2
            in
            let e2_hil = transform_sil_expr_to_hil e2_exp typ add_deref in
            match e2_hil with
            | AccessExpression e2_ae -> (
               (* handle aliasing of e2 *)
              let e2_final =
                match e2 with
                | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> e2_ae
                | Exp.Var _ | _ ->  (
                  let (_, e2_aliased_final) = resolve_entire_aliasing_of_var e2_ae astate ~add_deref:false in
                  e2_aliased_final
                )
              in
              (* save alias to the aliases set *)
              update_aliases e1_aliased_final e2_final astate
            )
            | _ -> astate
          end
      end
    else
      astate
  )
  | _ -> astate

(* function integrates summary of callee to the current astate when function call to pthread_create() occurs,
   it replaces all accesses to formal in callee_summary to accesses to actual *)
let integrate_pthread_summary astate thread callee_pname loc callee_summary callee_formals actuals _sil_actual_argument _caller_pname =
  F.printf "integrate_pthread_summary: callee_pname=%a on %a\n" Procname.pp callee_pname Location.pp loc;
  (* edit information about each access - thread, threads_active, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads astate.threads_active astate.lockset astate.unlockset (Some thread)) callee_summary.accesses in
  let callee_summary_edited_accesses = {callee_summary with accesses=edited_accesses_from_callee} in
  (* replace actuals with formals *)
  let callee_formal = (* callee formal is the same every time: pthread_create(void *arg) *)
    match callee_formals with
    | (var, typ) :: [] -> (
      let formal_pvar = Pvar.mk (var) callee_pname in
      let formal_access_path_base = AccessPath.base_of_pvar formal_pvar typ in
      HilExp.AccessExpression.base formal_access_path_base
    )
    | _ -> assert false (*TODO*)
  in
  let actual_passed_to_function = (List.nth actuals 3) in (* fourth argument of pthread_create function *)
  match actual_passed_to_function with
  | Some actual -> (
    (* if the argument is NULL, don't add accesses to formal in callee summary *)
    let is_null = HilExp.is_null_literal actual in
    (* resolve aliasing *)
    (* returns list of hil expressions (dealiased actuals) *)
    let rec for_each_var_create_hilexp lst acc =
      match lst with
      | [] -> acc
      | (_, h) :: t -> (
        let hil = HilExp.AccessExpression h in
        for_each_var_create_hilexp t (hil :: acc)
      )
    in
    let actual_list =
      match actual with
      | HilExp.AccessExpression ((FieldOffset _) as e_ae) -> (
        let lst = resolve_entire_aliasing_of_var_for_lfield_list e_ae astate ~add_deref:false in
        for_each_var_create_hilexp lst []
      )
      | HilExp.AccessExpression e_ae -> (
        let lst = resolve_entire_aliasing_of_var_list e_ae astate ~add_deref:false in (* TODO struct dealiasing *)
        for_each_var_create_hilexp lst []
      )
      | _ -> [actual]
    in
    (* edit accesses - formal to actual *)
    let (callee_summary_edited_accesses, astate) =
      if is_null then
        begin
          let accesses = remove_accesses_to_formal callee_formal callee_summary_edited_accesses.accesses in
          ({callee_summary_edited_accesses with accesses}, astate)
        end
      else
        begin
          (* edit accesses in callee_summary with actual - for each actual *)
          let rec for_each_actual_replace_formal_with_actual lst callee_summary astate =
            match lst with
            | [] -> (callee_summary, astate)
            | actual :: t -> (
              F.printf "updating with %a\n" HilExp.pp actual;
              let updated_accesses = AccessSet.map (AccessEvent.edit_access_with_actuals callee_formal actual) callee_summary.accesses in
              let callee_summary = {callee_summary with accesses=updated_accesses} in
              let updated_locals = remove_var_from_locals actual astate.locals in
              let astate = { astate with locals=updated_locals } in
              for_each_actual_replace_formal_with_actual t callee_summary astate
            )
          in
          for_each_actual_replace_formal_with_actual actual_list callee_summary_edited_accesses astate
        end
    in
    (* join callee and caller accesses *)
    let accesses_joined = AccessSet.join astate.accesses callee_summary_edited_accesses.accesses in
    let astate = { astate with accesses=accesses_joined } in
    astate
  )
  | None -> (
    let accesses_joined = AccessSet.join astate.accesses callee_summary_edited_accesses.accesses in
    { astate with accesses=accesses_joined }
  )

(* function integrates summary of callee to the current astate when function call occurs,
   it replaces all accesses to formals in callee_summary to accesses to actual *)
let integrate_summary astate callee_pname _loc callee_summary callee_formals actuals caller_pname =
  F.printf "integrate_summary: callee_pname=%a in Darc\n" Procname.pp callee_pname;
  (* create main thread if the caller function is main *)
  let current_thread = (* TODO check equality to the entry point (not only main) *)
    if (Int.equal (String.compare (Procname.to_string caller_pname) "main") 0) then
      Some (ThreadEvent.create_main_thread)
    else
      None
  in
  (* update accesses in callee_summary with the current lockset, unlockset, threads_active and thread *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads astate.threads_active astate.lockset astate.unlockset current_thread) callee_summary.accesses in
    (* returns list of hil expressions (dealiased actuals) *)
    let rec for_each_var_create_hilexp lst acc =
      match lst with
      | [] -> acc
      | (_, h) :: t -> (
        let hil = HilExp.AccessExpression h in
        for_each_var_create_hilexp t (hil :: acc)
      )
    in
    (* edit accesses - formal to actual *)
    let for_each_update_accesses formal actuals_list callee_pname edited_accesses_from_callee =
      (* edit accesses in callee_summary with actual - for each actual *)
      let rec for_each_actual_replace_formal_with_actual lst accesses =
        match lst with
        | [] -> accesses
        | actual :: t -> (
          F.printf "updating with %a\n" HilExp.pp actual;
          let formal_pvar = Pvar.mk (fst formal) callee_pname in
          let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
          let formal_access_expression = HilExp.AccessExpression.base formal_access_path_base in
          if HilExp.is_null_literal actual then
            remove_accesses_to_formal formal_access_expression edited_accesses_from_callee
          else
            begin
              (* replace all accesses to formal with actual *)
              let accesses_new = AccessSet.map (AccessEvent.edit_access_with_actuals formal_access_expression actual) accesses in
              for_each_actual_replace_formal_with_actual t accesses_new
            end
          )
        in
        for_each_actual_replace_formal_with_actual actuals_list edited_accesses_from_callee
      in
  (* function replaces formal parameters in accesses with actual parameters *)
  let replace_formals_with_actuals formals actuals accesses =
    let cnt = ref 0 in
    let accesses_ref = ref accesses in
    let rec loop = function
      | [] -> !accesses_ref
      | formal :: tl -> (
        (* edit access *)
        let actuals_list =
          match (List.nth actuals !cnt) with
          | None -> [] (* TODO *)
          | Some HilExp.AccessExpression ((FieldOffset _) as actual_load) -> (
            let lst = resolve_entire_aliasing_of_var_for_lfield_list actual_load astate ~add_deref:false in
            for_each_var_create_hilexp lst []
          )
          | Some HilExp.AccessExpression actual_load -> (
            let lst = resolve_entire_aliasing_of_var_list actual_load astate ~add_deref:false in (* TODO struct dealiasing *)
            for_each_var_create_hilexp lst []
          )
          | Some actual -> [actual]
        in
        (* replace all accesses to formal with actual *)
        accesses_ref := for_each_update_accesses formal actuals_list callee_pname !accesses_ref;(* AccessSet.map (AccessEvent.edit_access_with_actuals formal_access_expression actual) !accesses_ref; *)
        cnt := !cnt + 1; (* go to the next parameter *)
        loop tl
      )
    in
    loop formals
  in
  let accesses_with_actuals = replace_formals_with_actuals callee_formals actuals edited_accesses_from_callee in
  let accesses_joined = AccessSet.join astate.accesses accesses_with_actuals in
  (* return updated astate *)
  { astate with accesses=accesses_joined }

(* {{x, 2, ...}, {x, 3, ...}, {y, 5, ...}, ...} -> get_list_of_vars: [x, y, ...] *)
let get_list_of_vars set =
  AccessSet.fold (fun s acc -> (if List.mem acc s.var ~equal:HilExp.AccessExpression.equal then acc else s.var :: acc)) set []

let rec print_list lst =
  match lst with
  | [] -> F.printf "\n"
  | h :: t -> (
    F.printf "%a " HilExp.AccessExpression.pp h;
    print_list t
  )

(* function computes if there are any data races in the program,
   it creates pairs of accesses and checks on which pairs data race could occur *)
let compute_data_races post =
  (* create a list of pairs of accesses - [(ac1, ac1); (ac1, ac2)] *)
  let fold_add_pairs access lst = lst @ [access] in (* val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
  (*
    FIXME optimize data race computation:
    create list of used vars
    -> create pairs of accesses to those vars
    -> compute data races
    -> report only one of them
   *)
  let list_of_vars = get_list_of_vars post.accesses in
  F.printf "list_of_vars: \n";
  print_list list_of_vars;
  (* create list from set *)
  let lst1 = AccessSet.fold fold_add_pairs post.accesses [] in
  let lst2 = AccessSet.fold fold_add_pairs post.accesses [] in
  (* create a cartesian product *)
  let rec product l1 l2 =
    match l1, l2 with
    | [], _ | _, [] -> []
    | h1::t1, h2::t2 -> (h1,h2)::(product [h1] t2)@(product t1 l2)
  in
  let list_of_access_pairs = product lst1 lst2 in
  (* remove pairs where the first access has higher loc than the second one *)
  let optimised_list = List.filter ~f:AccessEvent.predicate_loc list_of_access_pairs in
  (* the final computation*)
  (* F.printf "cartesian product:\n";
  print_pairs_list list_of_access_pairs; *)
  (* F.printf "different pairs:\n";*)
  (* print_pairs_list optimised_list;*)
  (* F.printf "vars_checked:\n";*)
  let vars_checked = List.filter ~f:AccessEvent.predicate_var optimised_list in
  (* print_pairs_list vars_checked;*)
  (* F.printf "read_write_checked:\n";*)
  let read_write_checked = List.filter ~f:AccessEvent.predicate_read_write vars_checked in
  (* print_pairs_list read_write_checked;*)
  (* F.printf "threads_checked:\n"; *)
  let threads_checked = List.filter ~f:AccessEvent.predicate_thread read_write_checked in
  (* print_pairs_list threads_checked; *)
  (* F.printf "threads_intersection_checked:\n"; *)
  let threads_intersection_checked = List.filter ~f:AccessEvent.predicate_threads_intersection threads_checked in
  (* print_pairs_list threads_intersection_checked; *)
  F.printf "locksets_checked:\n";
  let locksets_checked = List.filter ~f:AccessEvent.predicate_locksets threads_intersection_checked in
  print_pairs_list locksets_checked;
  locksets_checked



(* abstract interpretation functions *)
(* <= function *)
let ( <= ) ~lhs ~rhs =
  let accesses_leq = AccessSet.leq ~lhs:lhs.accesses ~rhs:rhs.accesses in
  let threads_leq = ThreadSet.leq ~lhs:lhs.threads_active ~rhs:rhs.threads_active in
  let lockset_leq = Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset in
  let unlockset_leq = Lockset.leq ~lhs:lhs.unlockset ~rhs:rhs.unlockset in
  (* aliases, load_aliases, heap_aliases, locals? *)
  accesses_leq && threads_leq && lockset_leq && unlockset_leq

(* leq function *)
let leq ~lhs ~rhs = (<=) ~lhs ~rhs

(* function returns "union" of two lists *)
let rec list_union lst1 lst2 =
  match lst1 with
  | [] -> lst2
  | hd :: tl -> (
    let list_mem_opt = List.mem lst2 hd ~equal:phys_equal in
    match list_mem_opt with
    | true -> list_union tl lst2
    | false -> hd :: list_union tl lst2
  )

(* function joint two astates *)
let join astate1 astate2 =
  F.printf "join\n";
  let threads_active = ThreadSet.union astate1.threads_active astate2.threads_active in
  let accesses = AccessSet.union astate1.accesses astate2.accesses in
  let lockset = Lockset.inter astate1.lockset astate2.lockset in
  let unlockset = Lockset.inter astate1.unlockset astate2.unlockset in
  let aliases = AliasesSet.union astate1.aliases astate2.aliases in  (* TODO FIXME how to join aliases *)
  let load_aliases = list_union astate1.load_aliases astate2.load_aliases in
  let heap_aliases = list_union astate1.heap_aliases astate2.heap_aliases in
  let locals = list_union astate1.locals astate2.locals in
  { threads_active; accesses; lockset; unlockset; aliases; load_aliases; heap_aliases; locals }

(* widening function *)
let widen ~prev ~next ~num_iters:_ =
  join prev next

(* pretty print function *)
let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "\nthreads_active=%a" ThreadSet.pp astate.threads_active;
    F.fprintf fmt "\naccesses=%a" AccessSet.pp astate.accesses;
    F.fprintf fmt "\nlockset=%a" Lockset.pp astate.lockset;
    F.fprintf fmt "\nunlockset=%a" Lockset.pp astate.unlockset;
    F.fprintf fmt "\naliases=%a" AliasesSet.pp astate.aliases;

(* type of summary *)
type summary = t
