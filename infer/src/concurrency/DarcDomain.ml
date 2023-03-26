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
  let rec replace_base_of_var_with_actual var actual =
    let replace_base_inner = replace_base_of_var_with_actual actual in
    match var with
    | HilExp.AccessExpression.Dereference (Base _) -> (* *v -> *a *)
      HilExp.AccessExpression.dereference actual
    | HilExp.AccessExpression.Dereference ae -> (* *( *v) -> *(...) *)
      HilExp.AccessExpression.dereference (replace_base_inner ae)
    | HilExp.AccessExpression. AddressOf ae -> ( (* &( *v) -> &(...) *)
      let address_of_option = HilExp.AccessExpression.address_of (replace_base_inner ae) in
      match address_of_option with
      | Some address_of -> address_of
      | None -> ae
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
        let replaced_var = replace_base_of_var_with_actual access.var actual_ae in
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

let print_accesses accesses =
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
  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases
  (* F.printf "caller_pname=%a\n" Procname.pp caller_pname; *)
  (* F.printf "loc=%a\n" Location.pp loc *)
  (* F.printf "=======================================\n" *)

let rec _print_ae_list ae_list =
  match ae_list with
  | [] -> F.printf ".\n"
  | h::t -> F.printf "%a, " Aliases.pp h; _print_ae_list t

let get_base_as_access_expression var =
  let var_base = HilExp.AccessExpression.get_base var in
  let var_base_ae = HilExp.AccessExpression.base var_base in
  var_base_ae

let rec find_alias var aliases =  (* return Aliases.t option *)
  F.printf "find_alias: trying to find alias of var=%a\n" HilExp.AccessExpression.pp var;
 match aliases with
 | [] -> F.printf "find_alias: None\n"; None
 | (fst, snd)::t -> (
   F.printf "find_alias: fst: %a, snd: %a, lhs: %a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd HilExp.AccessExpression.pp var;
   if ((HilExp.AccessExpression.equal fst var) || (HilExp.AccessExpression.equal snd var)) then (
     F.printf "find_alias: %a, rhs: .a\n" Aliases.pp (fst, snd) (* HilExp.AccessExpression.pp rhs *);
     Some (fst, snd)
   ) else (
     find_alias var t
   )
 )

let rec find_alias_dereference var_without_dereference (* e.g. *p, *k *) aliases =  (* return Aliases.t option *)
  F.printf "find_alias_dereference: trying to find alias of var_without_dereference=%a\n" HilExp.AccessExpression.pp var_without_dereference;
 match aliases with
 | [] -> F.printf "find_alias_dereference: None\n"; None
 | (fst, snd)::t -> (
   F.printf "find_alias_dereference: fst: %a, snd: %a, lhs: %a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd HilExp.AccessExpression.pp var_without_dereference;
   if ((HilExp.AccessExpression.equal fst var_without_dereference) || (HilExp.AccessExpression.equal snd var_without_dereference)) then (
     F.printf "find_alias_dereference: %a, rhs: .a\n" Aliases.pp (fst, snd) (* HilExp.AccessExpression.pp rhs *);
     let snd_dereference = HilExp.AccessExpression.dereference snd in
     Some (fst, snd_dereference)
   ) else (
     find_alias_dereference var_without_dereference t
   )
 )

let remove_alias_from_aliases alias astate = (
  match alias with
  | None -> astate
  | Some alias -> (
    let new_aliases = AliasesSet.remove alias astate.aliases in
    (* )print_astate_aliases {astate with aliases=new_aliases }; *)
    { astate with aliases=new_aliases }
  )
)

let add_new_alias astate alias = (
  match alias with
  | None -> astate
  | Some alias -> (
    let new_aliases = AliasesSet.add alias astate.aliases in
    { astate with aliases=new_aliases }
  )
)

let create_new_alias fst snd = (
  match fst with
  | None -> None
  | Some f -> (
    match snd with
    | None -> None
    | Some s -> (
      Some (f, s)
    )
  )
)

let get_base_alias lhs aliases = (* vraci None | Some (m, &y) *)
  F.printf "get_base_alias\n";
  let lhs_base_ae = get_base_as_access_expression lhs in

let rec check_lhs lhs lhs_current var aliases =
  F.printf "-----------------check_lhs:------------------\n";
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      F.printf "check_lhs-if: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      let alias = find_alias var aliases in (* e.g. None | Some (y, &k) *)
      match alias with
      | Some alias -> Some alias   (* return alias *)
      | None -> (
(*        Some (var, var)    (* the var is not in aliases -> return var (only the second variable will be needed later) *)*)
        None (* TODO after the heap aliases are prohledane *)
      )
    end
  else
    begin
      F.printf "check_lhs-else: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      let find_current_in_aliases = find_alias var aliases in (* e.g. None | Some (m, &y) *)
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | None -> None
      | Some (_, snd) -> (
(*        F.printf "else Some snd\n";*)
        let snd_dereference = HilExp.AccessExpression.dereference snd in
        check_lhs lhs lhs_dereference snd_dereference aliases
      )
    end
  in
  check_lhs lhs lhs_base_ae lhs_base_ae aliases



let rec check_lhs_without_address_of lhs lhs_current var aliases =
  F.printf "-----------------check_lhs_without_address_of:------------------\n";
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      F.printf "check_lhs_without_address_of-if: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      (* if dereference -> find new alias, else return var *)
      match lhs with
      | HilExp.AccessExpression.Dereference lhs_without_dereference -> (
        let alias = find_alias_dereference lhs_without_dereference aliases in (* e.g. None | Some (y, &k) *)
        match alias with
        | Some alias_no_opt -> (
          (* TODO kdyz je n mallocovana a v aliasech je (p, n), musim zapsat pristup k obema, nejen k *n *)
          (* pozor, z vysledku beru jen var -> mrlo by se zkontrolovat potom, jestli var na leve strane je stejna jako na prave a pokud ne, tak pokud jsou oboji neadressof, musi se udelat pristup k obojimu *)
          Some alias_no_opt   (* return alias *)
        )
        | None -> (
          (* Some (var, var) *)    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
          None (* protoze se nasledne pokusime hledat v heap_aliases *) (* TODO TODO TODO *)
        )
      )
      | _ -> (
        Some (var, var)
      )
    end
  else
    begin
      F.printf "check_lhs_without_address_of-else: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      let find_current_in_aliases = find_alias var aliases in (* e.g. None | Some (m, &y) *)
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | None -> None
      | Some (_, snd) -> (
(*        F.printf "else Some snd\n";*)
        let snd_dereference = HilExp.AccessExpression.dereference snd in
        check_lhs_without_address_of lhs lhs_dereference snd_dereference aliases
      )
    end

(* FIXME tato funkce nepracuje s heap_aliases||| predelat *)
let replace_var_with_aliases_without_address_of var aliases = (* if alias is not found, var is returned *)
  let var_ae = get_base_as_access_expression var in
  let result_option = check_lhs_without_address_of var var_ae var_ae aliases in
  match result_option with
  | None -> (
    (* zkusime najit v heap_aliases a vratit list aliasu, za ktere se to aliasuje -> pak musime udelat pristup ke kazdemu *)
    var
  )
  | Some (_, snd) -> (
    snd
  )

let rec find_load_alias_by_var var load_aliases =
  match load_aliases with
  | [] -> None
  | (fst, snd) :: t -> (
    if HilExp.AccessExpression.equal var fst then
      Some (fst, snd)
    else
      find_load_alias_by_var var t
  )

let astate_with_clear_load_aliases astate =
  (*F.printf "load_aliases before clear: \n";*)
  (*_print_load_aliases_list astate;*)
  {astate with load_aliases=[]}



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

(* actual_to_be_removed is e.g. n$0 *)
let remove_heap_aliases_when_free actual_to_be_removed astate =
  (* find actual in load aliases *)
  let load_alias = find_load_alias_by_var actual_to_be_removed astate.load_aliases in
  match load_alias with
  | None -> astate
  | Some (var, snd) ->
    F.printf "Some var=%a, snd=%a\n" HilExp.AccessExpression.pp var HilExp.AccessExpression.pp snd;
  (* remove var and all aliases with the same loc as loc *)
    remove_heap_alias_by_var_name snd astate

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
    let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in
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
      let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in
      add_new_alias astate_alias_removed new_alias
    )
    | None -> ( (* alias wasn't found - try to find alias in heap aliases *)
      (* find rhs in heap aliases *)
      let rhs_heap_alias_loc = find_heap_alias_by_var rhs astate.heap_aliases in
      match rhs_heap_alias_loc with
      | Some loc -> (
        (* remove existing alias from aliases and add the new alias to astate *)
        let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in
        add_heap_alias lhs loc astate_alias_removed
        )
      | None -> astate (* alias doesn't exist *)
    )
  )



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

(* function returns main thread option *)
let create_main_thread = 
  let main_thread = ThreadEvent.create_main_thread in
  Some main_thread





let initial_main locals =
  (* create empty astate *)
  let empty_astate = empty_with_locals locals in
  (* create main thread *)
  let main_thread_option = create_main_thread in
  match main_thread_option with
  | None -> empty_astate
  | Some main_thread ->
    (* add the main thread to an empty astate *)
    let threads_active = ThreadSet.add main_thread empty_astate.threads_active in
    { empty_astate with threads_active }

(* Function transforms SIL expression to HIL expression *)
(* TODO handle f_resolve_id, add_deref and include_array_indexes correctly *)
let transform_sil_expr_to_hil sil_exp sil_typ add_deref =
  let f_resolve_id _var = None in
  let hil_expr = HilExp.of_sil ~include_array_indexes:false ~f_resolve_id ~add_deref sil_exp sil_typ in
  F.printf "%a " HilExp.pp hil_expr;
  hil_expr

(* Function transforms list of SIL expressions to HIL expressions *)
(* TODO handle f_resolve_id, add_deref and include_array_indexes correctly *)
let transform_sil_exprs_to_hil_list sil_expr_list add_deref = (* list of sil exprs *)
  F.printf "hil_actuals: ";
  let rec transform_sil_to_hil_actuals (sil_list : (Exp.t * Typ.t) list) (acc : HilExp.t list) =
    match sil_list with
    | [] -> (F.printf "\n"; acc)
    | (exp, typ) :: t -> (
      let hil_expr = transform_sil_expr_to_hil exp typ add_deref in
      (* add h to the list of HilExp.t *)
      let list_updated = acc @ [hil_expr] in
      transform_sil_to_hil_actuals t list_updated
    )
    in
    transform_sil_to_hil_actuals sil_expr_list []

let find_var_in_list var locals =
  let rec go lst =
    match lst with
    | [] -> None
    | h :: t ->
      if (HilExp.AccessExpression.equal var h) then Some h else go t
  in go locals

let add_access_to_astate var access_type astate loc pname =
  (* continue, add the access *)
  F.printf "Inside add_access_to_astate in Domain\n";
  let new_access : AccessEvent.t = (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread =
      (* TODO check equality to the entry point (not only main) *)
      if (Int.equal (String.compare (Procname.to_string pname) "main") 0) then
        create_main_thread
      else
        None
    in
    { var; loc; access_type; locked; unlocked; threads_active; thread }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  let new_astate = { astate with accesses } in
  print_astate new_astate;
  { astate with accesses }

(* function checks if the var should be added to accesses and if yes it is added *)
let add_access_to_astate_with_check var access_type astate loc pname =
  (* first check if the var is not local or return *)
  let is_return_exp = HilExp.AccessExpression.is_return_var var in
    if is_return_exp then
      astate
    else
      begin
        let var_base_ae = get_base_as_access_expression var in
        let is_local = find_var_in_list var_base_ae astate.locals in
        match is_local with
        | Some _ -> astate
        | None -> add_access_to_astate var access_type astate loc pname
      end


let add_access_with_heap_alias_when_malloc e1_ae e2_ae loc astate tmp_heap pname =
  let rec foo updated_astate tmp_heap updated_tmp_heap =
    match tmp_heap with
    | [] -> (updated_astate, updated_tmp_heap)
    | (var, loc) :: t ->
      (* check if the var is equal to n2 ->
        if yes, then create (e1_ae, loc), add it to astate.heap_aliases, don't add (var, loc) to acc and go with t
        if no, then add (var, loc) to acc and do t with astate and new acc*)
      if (HilExp.AccessExpression.equal var e2_ae) then
        begin
          let new_astate = add_heap_alias e1_ae loc updated_astate in
          foo new_astate t updated_tmp_heap
        end
      else
        begin
          foo updated_astate t ((var, loc) :: updated_tmp_heap)
        end
  in
  F.printf "heap_aliases before: \n";
  _print_heap_aliases_list astate;
  let (astate, tmp_heap) = foo astate tmp_heap [] in
  F.printf "heap_aliases after: \n";
  _print_heap_aliases_list astate;
  let astate_with_new_write_access = add_access_to_astate_with_check e1_ae ReadWriteModels.Write astate loc pname in
  (astate_with_new_write_access, tmp_heap)
(* go through aliases and add to acc every var with the same loc *)
let get_list_of_heap_aliases_with_same_loc_as_var var (astate : t) =
  (* find var in aliases *)
  let var_base_ae = get_base_as_access_expression var in
  F.printf "get_list_of_heap_aliases_with_same_loc_as_var: heap_aliases: \n";
  _print_heap_aliases_list astate;
  let loc_opt = find_heap_alias_by_var var_base_ae astate.heap_aliases in
  match loc_opt with
  | None -> []
  | Some loc -> (
    let rec go (heap_aliases : (HilExp.access_expression * Location.t) list) acc =
      match heap_aliases with
      | [] -> acc
      | (var_found, loc_found) :: tail -> (
        F.printf "something was found, var_found: %a\n" HilExp.AccessExpression.pp var_found;
        if (Location.equal loc loc_found) then
          begin
            (* vratit var_base_ae zpatky na podobu var - pokud to byla dereference, vratit dereferenci napr. *)
            match var with
            | HilExp.AccessExpression.Dereference _ -> (
              let var_found_dereference = HilExp.AccessExpression.dereference var_found in
              F.printf "+++++++++Deref: %a\n" HilExp.AccessExpression.pp var_found_dereference;
              go tail (var_found_dereference :: acc)
            )
            | _ -> (* TODO neco dalsiho vratit + rekurze na dereferenci ? *) (
              F.printf "+++++++++Not Deref\n";
              go tail (var_found :: acc)
            )
          end
        else
          go tail acc
      )
    in
    go astate.heap_aliases []
  )



let fst_aliasing_snd exp mem_aliased ~add_deref : HilExp.AccessExpression.t =
  F.printf "fst_aliasing_snd:\n";
  let exp_base_ae = get_base_as_access_expression exp in
    let (* rec *) check_lhs lhs lhs_current var aliases =
      F.printf "-----------------mem_aliased:check_lhs:------------------\n";
          F.printf "mem_aliased:check_lhs: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
          match lhs with
          | HilExp.AccessExpression.AddressOf _addressOf -> lhs
          | _ -> (
            let alias = find_alias var aliases in (* e.g. None | Some (y, &k) *) (* FIXME find only the second member of alias tuple? *)
            (* TODO rekurze!!! *)
            match alias with
            | Some (_, snd) -> ( (* var was found in aliases -> return alias *)
              if add_deref then
                HilExp.AccessExpression.dereference snd
              else
                snd
            )
            | None -> (    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
              F.printf "BLAAAAAAAAAAAAAAAH tady bych mela provest heap_aliases projduti a vraceni seznamu vsech ae, ke kterym se pristupuje\n";
              (* jenze tahle funkce vraci jenom jeden vyraz, ale ja potrebuju list *)
              var
              (*pouzit new_astate = add_accesses_with_aliases_or_heap_aliases *)
              (* pokud puvodni lhs byla addressOf -> vratit zase addressOf! *)
            )
          )
      in
      let res = check_lhs exp exp_base_ae exp_base_ae mem_aliased in
      F.printf "exp: %a, res: %a\n" HilExp.AccessExpression.pp exp HilExp.AccessExpression.pp res;
      match exp with
      | HilExp.AccessExpression.Dereference _ -> HilExp.AccessExpression.dereference res
      | _ -> res



(* functions that handle locks *)
(* function adds a lock to lockset and removes it from unlockset *)
let acquire_lock lockid astate loc =
  (* dealiasing *)
  match lockid with
  | HilExp.AccessExpression e_ae -> (
    let actual_dealiased_hilexp =
      let e_aliased = fst_aliasing_snd e_ae astate.load_aliases ~add_deref:true in
      (* find e_alised in aliases *)
      let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
      e_aliased_final
    in
    let lockid = HilExp.AccessExpression.to_access_path actual_dealiased_hilexp in
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
    let actual_dealiased_hilexp =
      let e_aliased = fst_aliasing_snd e_ae astate.load_aliases ~add_deref:true in
      F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
      (* find e_alised in aliases *)
      F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
      let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
      e_aliased_final
    in
    let lockid = HilExp.AccessExpression.to_access_path actual_dealiased_hilexp in
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




(*
  malloc:
    CALL malloc, ret_id: n$7, loc
    STORE e1:&n, e2: n$7

    -> malloc: heap_tmp: [(n$7, loc)]
    -> store:
         vidim (n$7, loc), mam (&n, n$7)
         hledam v heap_tmp e2 -> pak ho vezmu, vyrobim (e1, loc) a pridam do heap_aliases
*)



let add_accesses_to_astate_with_aliases_or_heap_aliases e1_ae e1_aliased_final access_type astate loc pname =
  if (HilExp.AccessExpression.equal e1_ae e1_aliased_final) then
    begin
      F.printf "add_accesses_to_astate_with_aliases_or_heap_aliases: if, e1_ea: %a, e1_aliased_final: %a\n" HilExp.AccessExpression.pp e1_ae HilExp.AccessExpression.pp e1_aliased_final;
      (* var was not aliased - maybe it is in heap aliases and if not, add access to var *)
      let list_of_new_accesses_from_heap_aliases = get_list_of_heap_aliases_with_same_loc_as_var e1_ae astate in
      match list_of_new_accesses_from_heap_aliases with
      | [] -> (
        (* var was not in heap aliases -> add access to var *)
        add_access_to_astate_with_check e1_aliased_final access_type astate loc pname(* returns astate *)
      )
      | _ -> (
        (* recursively add access to the next var *)
        let rec add_heap_accesses accesses_to_add_list astate = (* returns astate *)
          match accesses_to_add_list with
          | [] -> astate
          | var_heap :: t -> (
            (* add access to var *)
            (* check if there is the dereference!!! or double dereference etc. *)
            let new_astate = add_access_to_astate_with_check var_heap access_type astate loc pname(* returns astate *) in
            add_heap_accesses t new_astate
          )
        in
        add_heap_accesses list_of_new_accesses_from_heap_aliases astate
      )
    end
  else
    begin
      F.printf "add_accesses_to_astate_with_aliases_or_heap_aliases: else, e1_ea: %a, e1_aliased_final: %a\n" HilExp.AccessExpression.pp e1_ae HilExp.AccessExpression.pp e1_aliased_final;
      (* add access to aliased var to accesses *)
      add_access_to_astate_with_check e1_aliased_final access_type astate loc pname(* returns astate *)
    end

let load id_ae e_ae e (_typ: Typ.t) loc astate pname =
  (* save alias to the load_aliases set *)
(*  let _print_typ =*)
(*    match typ.desc with*)
(*    | Typ.Tint _ -> F.printf "Tint\n";*)
(*    | _ -> F.printf "other\n";*)
(*  in*)
  F.printf "load_aliases before:\n";
  _print_load_aliases_list astate;
  (* TODO TADY JSEM SKONCILA !!! ALIASING SE PROVADI POUZE V PRIPADE, ZE E JE VAR -> JE TO PRAVDA VZDY? + neni vyresena rekurze! *)
  (* TODO:
     - rekurze
     - STORE
     - neukladat do aliases int j = 0
  *)
  (* dealiasing se provadi pouze v pripade, ze rhs je Var a ne Pvar *)
  match e with
  | Exp.Var _ -> (
    F.printf "Var\n";
    (* DEALIASING *)
    (* find e in load_aliases jako fst -> return snd -> ale rekurzivne!!! *)
    (* TODO zakomponovat heap_aliases!!! *)
      let e_aliased = fst_aliasing_snd e_ae astate.load_aliases ~add_deref:false in
      F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
      (* find e_alised in aliases *)
      F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
      let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
      (* save alias to the load_aliases set *)
      let e_to_add = e_aliased_final in
      let new_mem_alias = (id_ae, e_to_add) in
        let load_aliases = new_mem_alias :: astate.load_aliases in
        let astate = { astate with load_aliases } in
        F.printf "load_aliases after:\n";
        _print_load_aliases_list astate;
        (* add all read access (if it is access to heap allocated variable with alias, there could be more accesses) *)
        let astate_with_new_read_accesses = add_accesses_to_astate_with_aliases_or_heap_aliases e_aliased e_aliased_final ReadWriteModels.Read astate loc pname in
(*        let astate_with_new_read_accesses = add_accesses_to_astate_with_check_local_or_return e_aliased e_aliased_final ReadWriteModels.Read astate loc in*)
        astate_with_new_read_accesses
  )
  | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> (
    F.printf "Lvar or Lfield or Lindex\n";
    let new_mem_alias = (id_ae, e_ae) in
      let load_aliases = new_mem_alias :: astate.load_aliases in
      let astate = { astate with load_aliases } in
      F.printf "load_aliases after:\n";
      _print_load_aliases_list astate;
      (* add read access *)
      let astate_with_new_read_access = add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname in
      astate_with_new_read_access
  )
  | _ -> (
    F.printf "other e, nemelo by nastat\n";
    let new_mem_alias = (id_ae, e_ae) in
      let load_aliases = new_mem_alias :: astate.load_aliases in
      let astate = { astate with load_aliases } in
      F.printf "load_aliases after:\n";
      _print_load_aliases_list astate;
      (* add read access *)
      let astate_with_new_read_access = add_access_to_astate_with_check e_ae ReadWriteModels.Read astate loc pname in
      astate_with_new_read_access
  )

let store e1 typ e2 loc astate pname =
  F.printf "handle_store -------------\n";
  let add_deref =
    match e1 with
    (* TODO asi to neni uplne spravne *)
    | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> true
    | Exp.Var _ | _ -> false
  in
  F.printf "e1_hil: ";
  let e1_hil = transform_sil_expr_to_hil e1 typ add_deref in
  F.printf "\n";
    match e1_hil with
    | AccessExpression e1_ae -> (
          (* add write_access *)
          let e1_aliased = fst_aliasing_snd e1_ae astate.load_aliases ~add_deref:true in
          F.printf "e1_aliased: %a\n" HilExp.AccessExpression.pp e1_aliased;
          (* find e_alised in aliases *)
          F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
          let e1_aliased_final = replace_var_with_aliases_without_address_of e1_aliased (AliasesSet.elements astate.aliases) in
          F.printf "e1_aliased_final: %a\n" HilExp.AccessExpression.pp e1_aliased_final;
           (* TODO nerozbije vec napsana na radku niz cele pristupy k nepointerovskym promennym? ty totiz nebudou v zadnem aliasu a var muze se rovnat var *)
           (* astate vytvorit na zaklade toho, zda se var == e1_ae nebo ne - pokud rovna, find in heap_aliases, pokud nerovna, pridat normalni pristup *)
          let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final ReadWriteModels.Write astate loc pname in
          (* save alias to the load_aliases set *)
          if (Typ.is_pointer typ) then (* TODO pridat alias, pokud typ je pointer *) (* nebo pridat malloc *)
            begin
            (* add alias *)
            (* e2 -> ziskat z nej Pvar access expression *)
            F.printf "e2_hil: ";
            let add_deref = (* TODO pridava se tu vubec nekdy deref? *)
              match e2 with
              | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> (
                F.printf "e2 je Lvar, Lfield, Lindex -> melo by byt add_deref=true, ale zatim davam false\n";
                false
              )
              | Exp.Var ident -> (
              let var = Var.of_id ident in
                let _add_deref =
                  match (var : Var.t) with
                  | LogicalVar _ -> (F.printf "%a je LogicalVar -> true, ale davam ted schvalne taky false\n" Var.pp var; true)
                 | ProgramVar _ -> (F.printf "%a je ProgramVar -> false\n" Var.pp var; false)
                in
(*                add_deref*)
                false (* TODO melo by byt add_deref *)
               )
               | _ -> (
                F.printf "other -> add_deref=false\n";
                false (* TODO right? *)
              )
            in
            let e2_exp =
              match e2 with
              | Exp.Cast (_, cast_exp) -> cast_exp (* handle Cast *)
              | _ -> e2
            in
            let e2_hil = transform_sil_expr_to_hil e2_exp typ add_deref in
            F.printf "\n";
            match e2_hil with(* TODO *)
            | AccessExpression e2_ae -> (
              (* dealiasing *)
              (* FIXME zatim nebudu delat dealiasing - potreba zachovat addressOf *)
    (*          let e2_aliased = fst_aliasing_snd e2_ae astate.load_aliases in*)
    (*          F.printf "e2_aliased: %a\n" HilExp.AccessExpression.pp e2_aliased;*)
    (*          F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;*)
    (*          let e2_aliased_final = replace_var_with_aliases_without_address_of e2_aliased (AliasesSet.elements astate.aliases) in*)
    (*          F.printf "e2_aliased_final: %a\n" HilExp.AccessExpression.pp e2_aliased_final;*)
              let e2_final =
                match e2 with
                | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> e2_ae
                | Exp.Var _ | _ ->  (
                  F.printf "TODO: dealiasovat\n";
                  let e2_aliased = fst_aliasing_snd e2_ae astate.load_aliases ~add_deref:false in
                  F.printf "e2_aliased: %a\n" HilExp.AccessExpression.pp e2_aliased;
                  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
                  let e2_aliased_final = replace_var_with_aliases_without_address_of e2_aliased (AliasesSet.elements astate.aliases) in
                  F.printf "e2_aliased_final: %a instead of e2_ae: %a\n" HilExp.AccessExpression.pp e2_aliased_final HilExp.AccessExpression.pp e2_ae;
                  e2_aliased_final
    (*              let e2_aliased = fst_aliasing_snd_with_dereference_counter e2_ae astate.load_aliases in*)
    (*              F.printf "e2_aliased: %a\n" HilExp.AccessExpression.pp e2_aliased;*)
    (*              (* find e_alised in aliases *)*)
    (*              F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;*)
    (*              let e2_aliased_final = replace_var_with_aliases_without_address_of e2_aliased (AliasesSet.elements astate.aliases) in*)
    (*              F.printf "e2_aliased_final: %a instead of e2_ae: %a\n" HilExp.AccessExpression.pp e2_aliased_final HilExp.AccessExpression.pp e2_ae;*)
    (*               e2_ae*)
                   (* e2_aliased_final *)
                )
              in
              (* save alias to the aliases set *)
              F.printf "aliases before=%a\n" AliasesSet.pp astate.aliases;
              let astate = update_aliases e1_aliased_final e2_final astate in
              F.printf "aliases after=%a\n" AliasesSet.pp astate.aliases;
              astate
    (*          let alias = (e1_aliased_final, e2_final) in*)
    (*          (* TODO melo by byt rafinovanejsi - pokud uz nejaky alias je, musi se najit a dal aliasovat atd. *)*)
    (*          let new_aliases = AliasesSet.add alias astate.aliases in*)
    (*          F.printf "aliases before=%a\n" AliasesSet.pp astate.aliases;*)
    (*          F.printf "aliases before=%a\n" AliasesSet.pp new_aliases;*)
    (*          { astate with aliases=new_aliases }*)
            )
            | _ -> astate
          end
        else
          begin
            (* dealiasing??? *)
            astate
          end
    )
    | _ -> astate

let remove_accesses_to_formal formal accesses : AccessSet.t =
  F.printf "remove_accesses_to_formal\n";
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
      let access_var = AccessEvent.get_var access in
      let access_var_base = HilExp.AccessExpression.get_base access_var in
      (* check if the base of formal equals the base of access.var *)
      if (AccessPath.equal_base access_var_base formal_base) then
        (* dont add the access to the list *)
        remove_formal t acc
      else
        (* add the access to the list *)
        remove_formal t (access :: acc)
    )
  in
  (* remove formals from accesses *)
  let accesses_list_with_removed_accesses = remove_formal accesses_list [] in
  (* create set from list *)
  AccessSet.of_list accesses_list_with_removed_accesses

let rec remove_from_locals var locals acc =
  match locals with
  | [] -> acc
  | h :: t -> (
    if (HilExp.AccessExpression.equal h var) then (
      acc @ t
    )
    else
      remove_from_locals var t (h :: acc)
  )

let remove_var_from_locals actual locals =
  match actual with
  | HilExp.AccessExpression actual_ae -> (
    let actual_base_ae = get_base_as_access_expression actual_ae in
    let is_in_locals = List.mem locals actual_base_ae ~equal:HilExp.AccessExpression.equal in
    match is_in_locals with
    | true -> remove_from_locals actual_base_ae locals []
    | false -> locals
  )
  | _ -> locals

(* TODO if argument funkce je null, pak nepredelavat formals na actuals a nepridavat ty pristupy k formals! *)
let integrate_pthread_summary astate thread callee_pname loc callee_summary callee_formals actuals sil_actual_argument caller_pname =
  F.printf "integrate_pthread_summary: callee_pname=%a on %a\n" Procname.pp callee_pname Location.pp loc;
  F.printf "summary of caller_pname=%a before --------" Procname.pp caller_pname;
  print_astate astate (* loc caller_pname *);
  F.printf "\nsummary of callee_pname=%a before --------" Procname.pp callee_pname;
  print_astate callee_summary (* loc caller_pname *);
  (* edit information about each access - thread, threads_active, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads astate.threads_active astate.lockset astate.unlockset (Some thread)) callee_summary.accesses in
  (* replace actuals with formals *)
  F.printf "\nformals of callee: %a: \n" Procname.pp callee_pname;
  _print_formals callee_formals;
  (* callee formal je jenom jeden: void *arg - normalne vzit ten prvni a pretypovat na ae (muze jich nejakym zpusobem byt vic?) *)
  let callee_formal =
    match callee_formals with
    | (var, typ) :: [] -> (
      let formal_pvar = Pvar.mk (var) callee_pname in
      let formal_access_path_base = AccessPath.base_of_pvar formal_pvar typ in
      let formal_access_expression = HilExp.AccessExpression.base formal_access_path_base in
      formal_access_expression
    )
    | _ -> assert false (*TODO*)
  in
  F.printf "actuals: \n";
  _print_actuals actuals;
  let actual_passed_to_function = List.nth actuals 3 in (* fourth argument of pthread_create function *)
  match actual_passed_to_function with
  | Some (* HilExp.AccessExpression *) actual -> (
    F.printf "NOT NULL\n";
    F.printf "actual: %a\n" HilExp.pp actual;
    (* if the argument is NULL, don't add accesses to formal in callee summary *)
    let is_null = HilExp.is_null_literal actual in
    F.printf "is_null: %b\n" is_null;
    (* TODO actual dealiasing *)
    let actual_dealiased_hilexp =
      match actual with
      | HilExp.AccessExpression e_ae -> (
        let e_aliased = fst_aliasing_snd e_ae astate.load_aliases ~add_deref:false in
        F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
        (* find e_alised in aliases *)
        F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
        let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
        F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
        HilExp.AccessExpression e_aliased_final
      )
      | _ -> actual
    in
    F.printf "actual_dealiased_hilexp: %a\n" HilExp.pp actual_dealiased_hilexp;
    let actual = actual_dealiased_hilexp in
    (* edit accesses - formal to actual *)
    let edited_accesses =
      if is_null then
          (* remove all accesses to formal in callee summary *)
          remove_accesses_to_formal callee_formal edited_accesses_from_callee
      else
        (* edit accesses in callee_summary with actual *)
        AccessSet.map (AccessEvent.edit_access_with_actuals callee_formal actual) edited_accesses_from_callee
    in
    (* join callee and caller accesses *)
    let accesses_joined = AccessSet.join astate.accesses edited_accesses in
    let astate = { astate with accesses=accesses_joined } in
    (* remove the variable from locals - remove base? *)
    (* TODO continue in the implementation, handle arrays and structs *)
    let updated_locals1 =
      F.printf "sil_actual_argument exp: %a, " Exp.pp (fst sil_actual_argument);
      match (fst sil_actual_argument) with
      | Exp.Lfield (_t1, _fieldname, _typ) -> (F.printf "Lfield\n"; astate.locals)
      | Exp.Lindex (_t1, _t2) -> (F.printf "Lindex\n"; astate.locals)
      | Exp.Lvar _pvar -> (F.printf "Lvar\n"; astate.locals)
      | Exp.Var ident -> (F.printf "Var %a\n" Ident.pp ident; astate.locals)
      | _ -> astate.locals
    in
    let updated_locals = remove_var_from_locals actual updated_locals1 in
    let astate = { astate with locals=updated_locals } in
    F.printf "locals after removing actual:\n";
    print_locals astate;
    (* return new astate *)
    astate
  )
  | None -> (
    (* TODO should be astate or edited astate? *)
    let accesses_joined = AccessSet.join astate.accesses edited_accesses_from_callee in
    { astate with accesses=accesses_joined }
  )

(* myslim, ze integrate_summary je stejna jako uintegrate_pthread_summary, akorat se nepridava aktualne nove vlakno,
   takze nevim, jake vlakno k tem pristupum pridat -> TODO vymyslet!! *)
(* plus tady se jeste musi nejak integrovat locks, threads atd. -> jeste neni domyslene *)
let integrate_summary astate callee_pname _loc callee_summary callee_formals actuals caller_pname =
  F.printf "integrate_summary: callee_pname=%a in Darc\n" Procname.pp callee_pname;
(*  F.printf "astate %a ---------------------------------------\n" Procname.pp caller_pname;*)
(*  print_astate astate loc caller_pname;*)
(*  F.printf "summary %a --------------------------------------\n" Procname.pp callee_pname;*)
(*  print_astate callee_summary loc callee_pname;*)
(*  F.printf "callee_formals: --------------------------------------\n";*)
(*  print_formals callee_formals;*)
(*  F.printf "actuals: --------------------------------------\n";*)
(*  print_actuals actuals;*)
(*  F.printf "--------------------------------------\n";*)
(*  F.printf "locals: --------------------------------\n";*)
(*  print_locals astate;*)
  (* TODO important *)
  (* pridat do accesses vlakno, na kterem prave jsem -> v podstate to bude proste bud main nebo None *)
  (* FIXME je to pravda? Ze vzdy bude bud main nebo None?!?!?! *)
  (* podle me by tu melo byt ze se vezme current thread -> pridat do summary? nelze, 
     protoze kdyz se vytvori thread, muze jich tam byt vic current threads*)
  let current_thread =
    (* TODO change to Pname comparision to main *)
    if (ThreadSet.equal ThreadSet.empty astate.threads_active) then
      None
    else create_main_thread (* false, upravit a zmenit na neco jineho! -> mozna to neni spatne, jen upravit podminku -> main se tam da, pokud uz nam bezi main thread, ne pokud je mnozina threads_active prazdna -> to muze nastat i tehdy, pokud jeste nebezi main, ale uz jsme vytvorili nejake vlakno -> wait ale 
       poradne rozmyslet -> co kdyz v main vytvorim vlakno t1 ktere jde do foo, ve foo vytvorim t2 ktere jde do bar *)
  in
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.update_accesses_with_locks_and_threads astate.threads_active astate.lockset astate.unlockset current_thread) callee_summary.accesses in
  (* TODO formals to actuals *)
   (* snad jsou oba listy (formals i actuals) spravne serazene, ze maji spravne vars na jednotlivych indexech - vyzera, ze hej *)
   let replace_formals_with_actuals formals actuals accesses =
     F.printf "replace_formals_with_actuals, caller_pname=%a, callee_pname=%a\n" Procname.pp caller_pname Procname.pp callee_pname;
     let cnt = ref 0 in
     let accesses_ref = ref accesses in
     let rec loop = function
       | [] -> F.printf " kaniec\n"; !accesses_ref
       | formal :: tl ->
         F.printf "|F: %a on %d |" Mangled.pp (fst formal) !cnt;
         (* edit access *)
         let actual_opt = List.nth actuals !cnt in
         let actual =
           match actual_opt with
           | None -> assert false (* TODO *)
           | Some HilExp.AccessExpression actual_load -> (
             (* replace load alias *)
             (* find actual_load in load_aliases *)
             (* find in heap aliases? *)
             (* return aliased var *)
             let e_ae = actual_load in
             let e_aliased = fst_aliasing_snd e_ae astate.load_aliases ~add_deref:false in
                   F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
                   (* find e_alised in aliases *)
                   F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
                   let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
                   F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
                   HilExp.AccessExpression e_aliased_final
                   (* save alias to the load_aliases set *)
                   (*
                   let e_to_add = e_aliased_final in
                   let new_mem_alias = (id_ae, e_to_add, e) in
                     let load_aliases = new_mem_alias :: astate.load_aliases in
                     let astate = { astate with load_aliases } in
                     F.printf "load_aliases after:\n";
                     _print_load_aliases_list astate;
                     (* add all read access (if it is access to heap allocated variable with alias, there could be more accesses) *)
                     let astate_with_new_read_accesses = add_accesses_to_astate_with_aliases_or_heap_aliases e_aliased e_aliased_final ReadWriteModels.Read astate loc in
                     astate_with_new_read_accesses
                     *)
           )
           | Some actual -> actual (* TODO *)
         in
         F.printf "|A: %a on %d |" HilExp.pp actual !cnt;
         (* TODO create correct access expression - dereference etc. *)
         (* formal musi mit typ access_expression, aby se dalo porovnat s jednotlivymi var v pristupech
            nebo var prevest na neco, co se da porovnat s formal - formal je typu (Mangled.t * Typ.t) *)
            (* if HilExp.AccessExpression.t == Mangled.t *)
            (* ACCESS_EXPRESSION.TO_ACCESS_PATH -> AccessPath.t nebo .get_base -> AccessPath.base *)
            (* Mangled.t
               pvar = Pvar.mk Mangled.t Procname.t
               access_path = AccessPath.of_pvar pvar typ    nebo base
               *)
             let formal_pvar = Pvar.mk (fst formal) callee_pname in
             let formal_access_path_base = AccessPath.base_of_pvar formal_pvar (snd formal) in
             (*
             let actual_pvar = Pvar.mk (fst actual) caller_pname in
             let actual_access_path_base = AccessPath.base_of_pvar actual_pvar (snd actual) in
             *)
             (* HilExp.t list *)
             let formal_access_expression = HilExp.AccessExpression.base formal_access_path_base in
         (* let _edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_access_with_actuals formal_access_expression actual) callee_summary.accesses in *)
         accesses_ref := AccessSet.map (AccessEvent.edit_access_with_actuals formal_access_expression actual) !accesses_ref;
         cnt := !cnt + 1;
         loop tl
     in
     loop formals
     (*`
     let accesses_mutable = ref [] in
     !accesses_mutable
     *)
   in
    (*  let counter = ref 0 in *)
     (*
     )let rec loop = function
     (* match formals with *)
     | [] -> !accesses_mutable
     | hd :: tl ->
         (* if phys_equal hd (List.nth actuals !counter) then
           F.printf "counter = %d\n" !counter; *)
       !accesses_mutable
*)

   (*
     postup:
     1. go through the list of formals
     2. switch formal to actual - pozor, nahradit pouze base, ale ne nic jineho :shrunk:
   *)
   F.printf "before replacement, edited_accesses_from_callee: \n";
   print_accesses edited_accesses_from_callee;
   let accesses_with_actuals = replace_formals_with_actuals callee_formals actuals edited_accesses_from_callee in
   F.printf "after replacement, accesses_with_actuals: \n";
   print_accesses accesses_with_actuals;
   (*
   let formal_to_access_path : Mangled.t * Typ.t -> AccessPath.t = fun (name, typ) ->
     let pvar = Pvar.mk name callee_pname in
       AccessPath.base_of_pvar pvar typ, []
     in
     let get_corresponding_actual formal =
       let rec find x lst =
         match lst with
         | [] -> -1
         | h :: t -> if AccessPath.equal x (formal_to_access_path h) then 0 else 1 + find x t
       in
       List.nth actuals (find formal callee_formals)
       |> Option.value_map ~default:[] ~f:HilExp.get_access_exprs
       |> List.hd |> Option.map ~f:HilExp.AccessExpression.to_access_path
     in
     let replace_formals_with_actuals summary_set formal =
       let replace_basis ((summary_element, loc) as le) =
           if AccessPath.is_prefix (formal_to_access_path formal) summary_element then begin
             let actual = get_corresponding_actual (formal_to_access_path formal) in
             (* create an element with base of actutal and acl of summ_element*)
             match actual with
             | Some a ->
                 let new_element = (AccessPath.append a (snd summary_element), loc) in
                 new_element
             | None ->
                 le
           end
           else le
       in
       Lockset.map replace_basis summary_set
     in
     let summary_lockset =
       List.fold callee_formals ~init:callee_summary.lockset ~f:replace_formals_with_actuals in
   let new_lockset =
     Lockset.fold (fun elem acc -> Lockset.add elem acc) summary_lockset astate.lockset
   in
   let _joinos = join astate callee_summary in
   { astate with lockset=new_lockset}
   *)
   (* astate *)
  (* )let accesses_joined = AccessSet.join astate.accesses edited_accesses_from_callee in *)
  let accesses_joined = AccessSet.join astate.accesses accesses_with_actuals in
  F.printf "integrated summary: ========================================\n";
  print_astate { astate with accesses=accesses_joined } (* loc caller_pname *);
  F.printf "============================================================\n";
  (* return updated astate *)
  { astate with accesses=accesses_joined }

(* pokud se spravne naprogramuje porovnavani accessu a tim padem abstraktnich stavu,
   tak se po prvnim pridani accessu v cyklu uz pri druhem loopu zadny access neprida
   a ty dva stavy uz se vyhodnoti jako equal a mohly by se vyhodnotit na true *)

(* *)

let ( <= ) ~lhs ~rhs =
  (* F.printf "leq\n"; *)
  let accesses_leq = AccessSet.leq ~lhs:lhs.accesses ~rhs:rhs.accesses in
  let threads_leq = ThreadSet.leq ~lhs:lhs.threads_active ~rhs:rhs.threads_active in
  let lockset_leq = Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset in
  let unlockset_leq = Lockset.leq ~lhs:lhs.unlockset ~rhs:rhs.unlockset in
  (* aliases, load_aliases, heap_aliases, locals? *)
  (*
  F.printf "accesses_leq: %b\n" accesses_leq;
  F.printf "lockset_leq: %b\n" lockset_leq;
  F.printf "unlockset_leq: %b\n" unlockset_leq;
  F.printf "threads_leq: %b\n" threads_leq;
  *)
  let leq = accesses_leq && threads_leq && lockset_leq && unlockset_leq in
  (* F.printf "final leq: %b\n" leq; *)
  leq

let leq ~lhs ~rhs = (<=) ~lhs ~rhs

let rec list_union lst1 lst2 =
  match lst1 with
  | [] -> lst2
  | hd :: tl -> (
    let list_mem_opt = List.mem lst2 hd ~equal:phys_equal in
    F.printf "%b" list_mem_opt;
    match list_mem_opt with
    | true -> list_union tl lst2
    | false -> hd :: list_union tl lst2
  )

let join astate1 astate2 =
  let new_astate : t =
    let threads_active = ThreadSet.union astate1.threads_active astate2.threads_active in
    let accesses = AccessSet.union astate1.accesses astate2.accesses in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
    let aliases = AliasesSet.union astate1.aliases astate2.aliases in  (* TODO FIXME how to join aliases *)
    let load_aliases = list_union astate1.load_aliases astate2.load_aliases in
    let heap_aliases = list_union astate1.heap_aliases astate2.heap_aliases in
    let locals = list_union astate1.locals astate2.locals in
    { threads_active; accesses; lockset; unlockset; aliases; load_aliases; heap_aliases; locals }
  in
  (* F.printf "JOIN: new_astate after join:\n";
  print_astate new_astate; *)
  new_astate

let widen ~prev ~next ~num_iters:_ =
  (* F.printf "WIDEN\n";
  F.printf "prev\n";
  print_astate prev;
  F.printf "next\n";
  print_astate next; *)
  join prev next

let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "\nthreads_active=%a" ThreadSet.pp astate.threads_active;
    F.fprintf fmt "\naccesses=%a" AccessSet.pp astate.accesses;
    F.fprintf fmt "\nlockset=%a" Lockset.pp astate.lockset;
    F.fprintf fmt "\nunlockset=%a" Lockset.pp astate.unlockset;
    F.fprintf fmt "\naliases=%a" AliasesSet.pp astate.aliases;

(* TODO: summary: lockset, unlockset, accesses *)
type summary = t

let compute_data_races post = 
  let rec print_pairs_list lst =
    match lst with
    | [] -> F.printf "\n"
    | h::t -> AccessEvent.print_access_pair h; print_pairs_list t in
  
  F.printf "DATA RACES COMPUTATION\n\n";

  (* TODO create a list of accesses - sth like [(ac1, ac1); (ac1, ac2)] *)
  (* val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a *)
  let fold_add_pairs access lst = lst @ [access] in
  (* create list from set and then create a cartesian product *)

  let rec product l1 l2 = 
    match l1, l2 with
    | [], _ | _, [] -> []
    | h1::t1, h2::t2 -> (h1,h2)::(product [h1] t2)@(product t1 l2) in

  let lst1 = AccessSet.fold fold_add_pairs post.accesses [] in 
  let lst2 = AccessSet.fold fold_add_pairs post.accesses [] in 

  let list_of_access_pairs = product lst1 lst2 in
  let optimised_list = (* function removes pairs where the first access has higher loc than the second one *)
    List.filter ~f:AccessEvent.predicate_loc list_of_access_pairs in
  
  (* the final computation*)
  (* F.printf "cartesian product:\n";
  print_pairs_list list_of_access_pairs; *)
(*  F.printf "different pairs:\n";*)
(*  print_pairs_list optimised_list;*)
(*  F.printf "vars_checked:\n";*)
  let vars_checked = List.filter ~f:AccessEvent.predicate_var optimised_list in
(*  print_pairs_list vars_checked;*)
(*  F.printf "read_write_checked:\n";*)
  let read_write_checked = List.filter ~f:AccessEvent.predicate_read_write vars_checked in
(*  print_pairs_list read_write_checked;*)
  F.printf "threads_checked:\n";
  let threads_checked = List.filter ~f:AccessEvent.predicate_thread read_write_checked in
  print_pairs_list threads_checked;
  F.printf "threads_intersection_checked:\n";
  let threads_intersection_checked = List.filter ~f:AccessEvent.predicate_threads_intersection threads_checked in
  print_pairs_list threads_intersection_checked;
  F.printf "locksets_checked:\n";
  let locksets_checked = List.filter ~f:AccessEvent.predicate_locksets threads_intersection_checked in
  print_pairs_list locksets_checked;
(*   F.printf "pairs with data races:\n"; *)
(*  let list_removed_duplicates = filter_tuples locksets_checked in*)
(*  print_pairs_list list_removed_duplicates;*)
  let has_data_race = List.length locksets_checked in
  let _print = if phys_equal has_data_race 0 then
    F.printf "\nTHERE IS NO DATA RACE.\n"
  else
    F.printf "\nTHERE IS A DATA RACE.\n"
  in
  locksets_checked
