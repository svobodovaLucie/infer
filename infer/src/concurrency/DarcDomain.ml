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
  type t = 
    | Read
    | Write
    (*| NoEffect
    *)

  let read_functions = 
    [ "printf"
    ; "sprintf" ]
  
  let write_functions = 
    [ "write"
    ; "writef" ]

  let has_effect method_name =
    List.mem read_functions method_name ~equal:String.equal ||
    List.mem write_functions method_name ~equal:String.equal

  let get_read_write_effect pname num_of_args =
    match pname with
    | "printf"  -> 
        let res_list = ref [] in
        for i = num_of_args - 1 downto 1 do
          begin
            res_list := (i, Read) :: !res_list;
            F.printf "i=%d\n" i
          end
        done;
      !res_list
    | "sprintf" -> [(0, Write); (2, Read); (3, Read)] (* FIXME *)
    | _ -> []

  let access_to_string access_type = 
    match access_type with
    | Read  -> "read "
    | Write -> "write"

end

module ThreadEvent = struct
  type t = (AccessPath.t * Location.t)

  (* FIXME how to compare threads *)
  (* 
  let compare ((base, aclist) as th, loc) ((base', aclist') as th', loc') =
    let result_th =
      if phys_equal th th' then 0
      else begin
        let res = AccessPath.compare_base base base' in
        if not (Int.equal res 0) then res
        else
          List.compare AccessPath.compare_access aclist aclist'
      end
    in
    let result_loc = Location.compare loc loc'
    in
    if (result_th + result_loc > 0) then 1 else 0
    *)

  (* TODO FIXME is it necessary to also compare locations? *)
  (* 0 -> the threads are the same, 1 -> false *)
  let compare ((base, aclist) as th, _loc) ((base', aclist') as th', _sloc') =
    if phys_equal th th' then 0
    else begin
      let res = AccessPath.compare_base base base' in
      if not (Int.equal res 0) then res
      else
        List.compare AccessPath.compare_access aclist aclist'
    end

  let pp fmt (th, loc) =
    F.fprintf fmt "%a on %a" AccessPath.pp th Location.pp loc;

end

module ThreadSet = AbstractDomain.FiniteSet(ThreadEvent)

module AccessEvent = struct
  type t =
  {
    var: AccessPath.t;
    loc: Location.t;
    access_type: ReadWriteModels.t;
    locked: Lockset.t;
    unlocked: Lockset.t;
    threads_active: ThreadSet.t;
    thread: ThreadEvent.t option;
  }

  (*
  let compare (((base, aclist) as lock), _) ((((base'), aclist') as lock' ), _) =
    if phys_equal lock lock' then 0
    else begin
      let res = AccessPath.compare_base base base' in
      if not (Int.equal res 0) then res
      else
        List.compare AccessPath.compare_access aclist aclist'
    end
  *)
  (* TODO how to compare accesses? is it necessary? *)
  let compare _t1 _t2 = 1
  let _equal t1 t2 = Int.equal 0 (compare t1 t2)
  let _hash t1 = Hashtbl.hash t1.loc

  let edit_accesses threads_active lockset unlockset thread access = 
    (* create new access and use informations from astate (sth like union access.lockset & astate.lockset etc.) *)
    let locked = Lockset.diff (Lockset.union lockset access.locked) access.unlocked in
    let unlocked = Lockset.union (Lockset.diff unlockset access.locked) access.unlocked in
    let threads_active = ThreadSet.union threads_active access.threads_active in
    { var=access.var; loc=access.loc; access_type=access.access_type; locked; unlocked; threads_active; thread }

  let _cmp ((base, aclist) as th, _loc) ((base', aclist') as th', _sloc') =
    if phys_equal th th' then 0
    else begin
      let res = AccessPath.compare_base base base' in
      if not (Int.equal res 0) then res
      else
        List.compare AccessPath.compare_access aclist aclist'
    end

  let predicate_loc (a1, a2) = 
    if Location.compare a1.loc a2.loc <= 0 then true else false
  (*
  let print_access_pair (t1, t2) =
    F.printf "Printing access pair\n";
    F.printf "(%a, %a, %s, l=%a, ulo=%a, tha=%a\n"
      AccessPath.pp t1.var Location.pp t1.loc t1.access_type Lockset.pp t1.locked
      Lockset.pp t1.unlocked ThreadSet.pp t1.threads_active;
    match t1.thread with
    | Some t -> F.printf "on thread %a,,, \n" ThreadEvent.pp t;
    | None -> F.printf "on None thread,,, \n";
    
    F.printf "(%a, %a, %s, l=%a, ulo=%a, tha=%a\n"
      AccessPath.pp t2.var Location.pp t2.loc t2.access_type Lockset.pp t2.locked
      Lockset.pp t2.unlocked ThreadSet.pp t2.threads_active;
    match t2.thread with
    | Some t -> F.printf "on thread %a)\n" ThreadEvent.pp t
    | None -> F.printf "on None thread)\n"
  *)
  let print_access_pair (t1, t2) =
    let t1_access_string = ReadWriteModels.access_to_string t1.access_type in
    F.printf "(%a, %a, %s |"
      AccessPath.pp t1.var Location.pp t1.loc t1_access_string;
    (*
    match t1.thread with
    | Some t -> F.printf "on thread %a,,, \n" ThreadEvent.pp t;
    | None -> F.printf "on None thread,,, \n";
    *)
    let t2_access_string = ReadWriteModels.access_to_string t2.access_type in
    F.printf " %a, %a, %s)\n"
      AccessPath.pp t2.var Location.pp t2.loc t2_access_string
    (*
    match t2.thread with
    | Some t -> F.printf "on thread %a)\n" ThreadEvent.pp t
    | None -> F.printf "on None thread)\n"
    *)

  let pp fmt t1 =
    let acc_type = ReadWriteModels.access_to_string t1.access_type in
    F.fprintf fmt "{%a, %a, %s,\n            locked=%a,\n            unlocked=%a,\n
                threads_active=%a\n"
      AccessPath.pp t1.var Location.pp t1.loc acc_type (* t1.access_type *) Lockset.pp t1.locked
      Lockset.pp t1.unlocked ThreadSet.pp t1.threads_active;
    match t1.thread with
    | Some t -> F.fprintf fmt "on thread %a\n" ThreadEvent.pp t
    | None -> F.fprintf fmt "on None thread\n"
    
    (*
    let compare ((base, aclist) as th, _loc) ((base', aclist') as th', _sloc') =
      if phys_equal th th' then 0
      else begin
        let res = AccessPath.compare_base base base' in
        if not (Int.equal res 0) then res
        else
          List.compare AccessPath.compare_access aclist aclist'
      end
      *)
  (* let var_equals a1 a2 = compare a1.var a2.var *)
  
  (*
var != var2, thr == t2, a1 == rd and a2 == rd nebo acc == w    
  length (intersection t1 t2 } < 2
  intersection lockset 1 lockset2 == {}
    *)

  let predicate_var (a1, a2) = (* var1 != var2 -> true *)
    if phys_equal (AccessPath.compare a1.var a2.var) 0 then true else false

  let predicate_thread (a1, a2) = (* t1 != t2 -> true *)
    let t1 =
      match a1.thread with
      | Some t -> t
      | None -> assert false
    in
    let t2 =
      match a2.thread with
      | Some t -> t
      | None -> assert false
    in
    if phys_equal (ThreadEvent.compare t1 t2) 0 then false else true

  let predicate_threads_active_length (a1, _) = (* length(t1) < 2 -> false *)
    let len = ThreadSet.cardinal a1.threads_active in
    if len < 2 then false else true

  let predicate_read_write (_a1, _a2) = true (* a1 == rd and a2 == rd -> false *)
    (*
    if ((String.equal a1.access_type "rd") && (String.equal a2.access_type "rd"))
      then false else true
    *)
  let predicate_threads_intersection (a1, a2) = (* length(intersect ts1 ts2) < 2 -> false *)
    let intersect = ThreadSet.inter a1.threads_active a2.threads_active in
    let len = ThreadSet.cardinal intersect in
    if len < 2 then false else true

  let predicate_locksets (a1, a2) = (* intersect ls1 ls2 == {} -> false *)
    let both_empty = 
      if ((phys_equal a1.locked Lockset.empty) && (phys_equal a2.locked Lockset.empty)) 
        then true else false in
    let intersect = Lockset.inter a1.locked a2.locked in
    if Lockset.equal intersect Lockset.empty || not both_empty then true else false
end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

type t =
{
  threads_active: ThreadSet.t;
  accesses: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  unlockset: Lockset.t
  (* vars_declared: Access Paths sth... *)
}

let empty =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty
}

(* TODO *)
let add_thread th astate =
  (* F.printf "Adding the thread...\n"; *)
  match th with
  | Some th ->
    let threads_active = ThreadSet.add th astate.threads_active in
    (* F.printf "====== threads_active=%a\n" ThreadSet.pp threads_active; *)
    {astate with threads_active;}
  | None -> assert false

(* TODO add thread to be removed *)
(* TODO can't do simply ThreadSet.remove, bcs now the thread is joining at different location
   that it was added... these threads are not the same bcs of the different location-> 
   it is necessary to just look at the AccessPath to know if it should be removed or not. *)
let remove_thread th astate = 
  match th with
  | Some th -> 
    (* F.printf "Removing the thread...\n"; *)
    let threads_active = ThreadSet.remove th astate.threads_active in
    (* F.printf "====== threads_active=%a\n" ThreadSet.pp threads_active; *)
    {astate with threads_active;}
  | None -> assert false

let create_main_thread = 
  let pname = Procname.from_string_c_fun "main" in
  let pvar_from_pname : Pvar.t = Pvar.mk_tmp "'main_thread'" pname in
  let tvar_name = Typ.TVar "thread" in
  let typ_main_thread = Typ.mk tvar_name in
  let acc_path_from_pvar : AccessPath.t = AccessPath.of_pvar pvar_from_pname typ_main_thread in
  Some (acc_path_from_pvar, Location.dummy)

let initial_main =
  (* create main thread *)
  let main_thread = create_main_thread in
  (* add the main thread to an empty astate *)
  let initial_astate = empty in 
  add_thread main_thread initial_astate

let acquire lockid astate loc pname =
  F.printf "acquire: pname = %a in Darc\n" Procname.pp pname;
  let lock : LockEvent.t = (lockid, loc) in
  let new_astate : t =
    let lockset = Lockset.add lock astate.lockset in
    let unlockset = Lockset.remove lock astate.unlockset in
    { astate with lockset; unlockset }
  in
  new_astate

let release lockid astate loc pname =
  F.printf "release: pname = %a in Darc\n" Procname.pp pname;
  let lock : LockEvent.t = (lockid, loc) in
  let new_astate : t =
    let lockset = Lockset.remove lock astate.lockset in
    let unlockset = Lockset.add lock astate.unlockset in
    { astate with lockset; unlockset }
  in
  new_astate

(* TODO function for read_expression -> initial access_type is rd *)

(* FIXME var is any expression now (n$7 etc.) *)
let assign_expr var astate loc pname =
  F.printf "Inside assign_expr in Domain\n";
  let new_access : AccessEvent.t =
    let access_type = ReadWriteModels.Write in (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread = if (phys_equal (String.compare (Procname.to_string pname) "main") 0) then create_main_thread else 
      (* if the astate.threads_active contains main thread -> the thread is main, alse None? *) 
      (* or simply if the procedure is main -> main thread *)
      
        None in (* TODO in the case of main... *) (* TODO create_main_thread *)
    { var; loc; access_type; locked; unlocked; threads_active; thread }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  { astate with accesses }

let print_astate astate loc caller_pname = 
  F.printf "========= printing astate... ==========\n";
  F.printf "access=%a\n" AccessSet.pp astate.accesses;
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "caller_pname=%a\n" Procname.pp caller_pname;
  F.printf "loc=%a\n" Location.pp loc;
  F.printf "=======================================\n"

(* FIXME var is any expression now (n$7 etc.) *)
let add_access_to_astate var access_type astate loc pname =
  F.printf "Inside add_access_to_astate in Domain\n";
  let new_access : AccessEvent.t = (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread = if (phys_equal (String.compare (Procname.to_string pname) "main") 0) 
      then create_main_thread else 
      (* if the astate.threads_active contains main thread -> the thread is main, alse None? *) 
      (* or simply if the procedure is main -> main thread *)
      
        None in (* TODO in the case of main... *) (* TODO create_main_thread *)
    { var; loc; access_type; locked; unlocked; threads_active; thread }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  let new_astate = { astate with accesses } in
  print_astate new_astate loc pname;
  { astate with accesses }

let integrate_pthread_summary astate thread callee_pname loc callee_summary _callee_formals _actuals caller_pname =
  F.printf "integrate_pthread_summary: callee_pname=%a\n" Procname.pp callee_pname;
  F.printf "summary before --------";
  print_astate astate loc caller_pname;
  (* edit information about each access - thread, threads_aactive, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses astate.threads_active astate.lockset astate.unlockset thread) callee_summary.accesses in
  let accesses_joined = AccessSet.join astate.accesses edited_accesses_from_callee in
  { astate with accesses=accesses_joined }

let integrate_summary astate callee_pname loc _callee_summary _callee_formals _actuals caller_pname =
  F.printf "integrate_summary: callee_pname=%a in Darc\n" Procname.pp callee_pname;
  print_astate astate loc caller_pname;

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
  astate

let ( <= ) ~lhs ~rhs =
  Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset &&
  Lockset.leq ~lhs:lhs.unlockset ~rhs:rhs.unlockset

let leq ~lhs ~rhs = (<=) ~lhs ~rhs

let join astate1 astate2 =
  let new_astate : t =
    let threads_active = ThreadSet.union astate1.threads_active astate2.threads_active in
    let accesses = AccessSet.union astate1.accesses astate2.accesses in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
    { threads_active; accesses; lockset; unlockset }
  in
  new_astate

let widen ~prev ~next ~num_iters:_ =
  join prev next

let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "\nthreads_active=%a" ThreadSet.pp astate.threads_active;
    F.fprintf fmt "\naccesses=%a" AccessSet.pp astate.accesses;
    F.fprintf fmt "\nlockset=%a" Lockset.pp astate.lockset;
    F.fprintf fmt "\nunlockset=%a" Lockset.pp astate.unlockset;

(* TODO: summary: lockset, unlockset, accesses *)
type summary = t

let compute_data_races post = 
  (* F.printf "\n\nSUMMARY MAIN: %a\n\n" pp post; *)

  (* 
  type t =
  {
    threads_active: ThreadSet.t;
    accesses: AccessSet.t;
    lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
    unlockset: Lockset.t
    (* vars_declared: Access Paths sth... *)
  }
  *)

  (* F.printf "ACCESSES: %a\n" AccessSet.pp post.accesses; *)

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
  F.printf "different pairs:\n";
  print_pairs_list optimised_list;
  F.printf "threads_active_length_checked:\n";
  let threads_active_length_checked = List.filter ~f:AccessEvent.predicate_threads_active_length optimised_list in
  print_pairs_list threads_active_length_checked;
  F.printf "vars_checked:\n";  
  let vars_checked = List.filter ~f:AccessEvent.predicate_var threads_active_length_checked in
  print_pairs_list vars_checked;
  F.printf "read_write_checked:\n";
  let read_write_checked = List.filter ~f:AccessEvent.predicate_read_write vars_checked in
  print_pairs_list read_write_checked;
  F.printf "threads_checked:\n";
  let threads_checked = List.filter ~f:AccessEvent.predicate_thread read_write_checked in
  print_pairs_list threads_checked;
  F.printf "threads_intersection_checked:\n";
  let threads_intersection_checked = List.filter ~f:AccessEvent.predicate_threads_intersection threads_checked in
  print_pairs_list threads_intersection_checked;
  F.printf "locksets_checked:\n";
  let locksets_checked = List.filter ~f:AccessEvent.predicate_locksets threads_intersection_checked in
  print_pairs_list locksets_checked;
  let has_data_race = List.length locksets_checked in
  if phys_equal has_data_race 0 then
    F.printf "\nTHERE IS NO DATA RACE.\n"
  else
    F.printf "\nTHERE IS A DATA RACE.\n"  
