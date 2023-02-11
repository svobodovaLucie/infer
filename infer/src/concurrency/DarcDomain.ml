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

module Aliases = struct 
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t)

  (* TODO *)
  let compare t1 t2 = 
    HilExp.AccessExpression.compare (fst t1) (fst t2)
    (* somehow add HilExp.AccessExpression.compare (snd t1) (snd t2) *)

  let _equal t1 t2 = 
    HilExp.AccessExpression.equal (fst t1) (fst t2) &&
    HilExp.AccessExpression.equal (snd t1) (snd t2)

  let _hash t1 = Hashtbl.hash t1

  let _get_fst (fst, _) = fst

  let _get_snd (_, snd) = snd

  let pp fmt (f, s) =
    F.fprintf fmt "(%a, %a)" HilExp.AccessExpression.pp f HilExp.AccessExpression.pp s;
end

module AliasesSet = AbstractDomain.FiniteSet(Aliases)

module AccessEvent = struct
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

  (* TODO how to compare accesses? is it necessary? *)
  let compare _t1 _t2 = 1
  let _equal t1 t2 = Int.equal 0 (compare t1 t2)
  let _hash t1 = Hashtbl.hash t1.loc

  let edit_accesses threads_active lockset unlockset thread access = 
    (* create new access and use information from astate (sth like union access.lockset & astate.lockset etc.) *)
    let locked = Lockset.diff (Lockset.union lockset access.locked) access.unlocked in
    let unlocked = Lockset.union (Lockset.diff unlockset access.locked) access.unlocked in
    let threads_active = ThreadSet.union threads_active access.threads_active in
    { var=access.var; loc=access.loc; access_type=access.access_type; locked; unlocked; threads_active; thread }

  let predicate_loc (a1, a2) =
    if Location.compare a1.loc a2.loc <= 0 then true else false

  let print_access_pair (t1, t2) =
    let t1_access_string = ReadWriteModels.access_to_string t1.access_type in
    F.printf "(%a, %a, %s |" HilExp.AccessExpression.pp t1.var Location.pp t1.loc t1_access_string;
    let t2_access_string = ReadWriteModels.access_to_string t2.access_type in
    F.printf " %a, %a, %s)\n" HilExp.AccessExpression.pp t2.var Location.pp t2.loc t2_access_string

  (* pp with all information *)
  (*
  let pp fmt t1 =
    let acc_type = ReadWriteModels.access_to_string t1.access_type in
    F.fprintf fmt "{%a, %a, %s,\n            locked=%a,\n            unlocked=%a,\n
                threads_active=%a\n"
      HilExp.AccessExpression.pp t1.var Location.pp t1.loc acc_type (* t1.access_type *) Lockset.pp t1.locked
      Lockset.pp t1.unlocked ThreadSet.pp t1.threads_active;
    match t1.thread with
    | Some t -> F.fprintf fmt "on thread %a\n" ThreadEvent.pp t
    | None -> F.fprintf fmt "on None thread\n"
  *)
  (* pp short version  - accesses only *)
  let pp fmt t1 =
    F.fprintf fmt "{%a, %a, " HilExp.AccessExpression.pp t1.var Location.pp t1.loc;
    match t1.thread with
    | Some t -> F.fprintf fmt "thread %a}" ThreadEvent.pp t
    | None -> F.fprintf fmt "None thread}"

  let predicate_var (a1, a2) = (* var1 != var2 -> true *)
    if phys_equal (HilExp.AccessExpression.compare a1.var a2.var) 0 then true else false

  let predicate_thread (a1, a2) = (* t1 != t2 -> true *)
    let t1 =
      match a1.thread with
      | Some t -> t
      | None -> F.printf "first\n"; assert false
    in
    let t2 =
      match a2.thread with
      | Some t -> t
      | None -> F.printf "second\n"; assert false
    in
    if phys_equal (ThreadEvent.compare t1 t2) 0 then false else true

  let predicate_threads_active_length (a1, _) = (* length(t1) < 2 -> false *)
    let len = ThreadSet.cardinal a1.threads_active in
    if len < 2 then false else true

  let predicate_read_write (_a1, _a2) = true (* a1 == rd and a2 == rd -> false *)

  let predicate_threads_intersection (a1, a2) = (* length(intersect ts1 ts2) < 2 -> false *)
    let intersect = ThreadSet.inter a1.threads_active a2.threads_active in
    let len = ThreadSet.cardinal intersect in
    if len < 2 then false else true

  let predicate_locksets (a1, a2) = (* intersect ls1 ls2 == {} -> false *) (* TODO nestaci aby aspon lockset alespon jednoho pristupu byla prazdna? *)
    let both_empty = 
      if ((phys_equal a1.locked Lockset.empty) && (phys_equal a2.locked Lockset.empty)) 
        then true else false in
    let intersect = Lockset.inter a1.locked a2.locked in
    if Lockset.equal intersect Lockset.empty || not both_empty then true else false (* TODO wtf to nejak neodpovida *)
    (* proc tu vubec je to not both_empty, vsak intersect bude empty, i kdyz bude oboji empty -> proc to mam rozdelene wtf? *)
    (* prece kdyz maji obe both lockset, tak tam normalne data race byt muze *)

  (*
  let pp_short fmt t1 =
    F.fprintf fmt "{%a, %a, " HilExp.AccessExpression.pp t1.var Location.pp t1.loc;
    match t1.thread with
    | Some t -> F.fprintf fmt "thread %a}\n" ThreadEvent.pp t
    | None -> F.fprintf fmt "None thread}\n"
  *)
end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

(*
module Vars = struct
  type t = HilExp.AccessExpression.t
end

module VarsSet = AbstractDomain.FiniteSet(Vars)
*)

type t =
{
  threads_active: ThreadSet.t;
  accesses: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  unlockset: Lockset.t;
  aliases: AliasesSet.t;
  (* vars_declared: HilExp.AccessExpression.t list; *)
  vars_declared: (Mangled.t * Typ.t) list;
}

let empty =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  aliases = AliasesSet.empty;
  vars_declared = [];
}

let empty_with_vars vars_declared =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  aliases = AliasesSet.empty;
  vars_declared;
}

let _print_alias alias = (
  match alias with
 | None -> F.printf "print_alias: None\n";
 | Some (fst, snd) -> F.printf "print_alias: %a\n" Aliases.pp (fst, snd);
 )

let rec find_alias var aliases =  (* return Aliases.t option *)
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

let remove_alias_from_aliases alias astate = (
  match alias with
  | None -> astate
  | Some alias -> (
    let new_aliases = AliasesSet.remove alias astate.aliases in
    (* )print_astate_aliases {astate with aliases=new_aliases }; *)
    { astate with aliases=new_aliases }
  )
)

let add_new_alias_no_option astate alias = (
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

let rec check_lhs lhs lhs_current var aliases =
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      F.printf "check_lhs-if: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      let alias = find_alias var aliases in (* e.g. None | Some (y, &k) *)
      match alias with
      | Some alias -> Some alias   (* return alias *)
      | None -> Some (var, var)    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
    end
  else
    begin
      F.printf "check_lhs-else: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      let find_current_in_aliases = find_alias var aliases in (* e.g. None | Some (m, &y) *)
      let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
      match find_current_in_aliases with
      | None -> None
      | Some (_, snd) -> (
        let snd_dereference = HilExp.AccessExpression.dereference snd in
        check_lhs lhs lhs_dereference snd_dereference aliases
      )
    end

let get_base_alias lhs aliases = (* vraci None | Some (m, &y) *)
  let lhs_base = HilExp.AccessExpression.get_base lhs in
  let lhs_ae = HilExp.AccessExpression.base lhs_base in
  check_lhs lhs lhs_ae lhs_ae aliases

let get_option_fst lhs alias = (
  match alias with
  | None -> Some lhs
  | Some (fst, _) -> Some fst
)

let get_option_snd alias = (
  match alias with
  | None -> None
  | Some (_, snd) -> Some snd
)

let update_aliases lhs rhs astate =
 let aliases = AliasesSet.elements astate.aliases in
 let rec print_ae_list ae_list =
   match ae_list with
   | [] -> F.printf ".\n";
   | h::t -> F.printf "%a, " Aliases.pp h; print_ae_list t;
 in
 F.printf "aliases:\n";
 print_ae_list aliases;
 (* lhs *)
 F.printf "lhs_alias_fst:\n";
 let lhs_alias = ( (* returns None | Some (y, &x) *)
   match lhs with
   | HilExp.AccessExpression.Base _ae -> (
     F.printf "lhs_alias_fst: base: lhs: %a\n" HilExp.AccessExpression.pp lhs;
     None
   )
   | HilExp.AccessExpression.Dereference _ae -> (
     F.printf "lhs_alias_fst: dereference: lhs: %a\n" HilExp.AccessExpression.pp lhs;
     F.printf "lhs_alias:\n";
     let lhs_alias = get_base_alias lhs aliases in (* **u -> Some (y, &k) *)
     lhs_alias
   )
   | _ -> ( (* addressOf, other *)
     None (* TODO *)
   )
 )
 in
 F.printf "lhs_alias_fst:\n";
 let lhs_alias_fst = get_option_fst lhs lhs_alias in
 (* rhs *)
 F.printf "rhs_alias_snd:\n";
 let rhs_alias_snd = (
   match rhs with
   | HilExp.AccessExpression.AddressOf _ae -> (
     F.printf "rhs_alias_snd: addressOf: rhs: %a\n" HilExp.AccessExpression.pp rhs;
     Some rhs
   )
   | _ -> (  (* base, dereference etc. *)
     let rhs_alias = get_base_alias rhs aliases in (* *q -> Some (x, &z) *)
     get_option_snd rhs_alias (* Some (x, &z) -> Some &z *)
   )
 )
 in
 F.printf "new_alias:\n";
 let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in (* Some (y, &z) *)
 F.printf "new_alias: ";
 _print_alias new_alias;
 F.printf "remove_alias_from_aliases:\n";
 let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in (* astate *)
 F.printf "final_astate:\n";
 let final_astate = add_new_alias_no_option astate_alias_removed new_alias in (* astate *)
 final_astate

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

let initial_main vars_declared =
  (* create main thread *)
  let main_thread = create_main_thread in
  (* add the main thread to an empty astate *)
  (* let initial_astate = empty in *)
  let initial_astate = empty_with_vars vars_declared in
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

let print_astate astate _loc _caller_pname =
  (* F.printf "========= printing astate... ==========\n"; *)
  F.printf "access=%a\n" AccessSet.pp astate.accesses
  (*
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
  F.printf "caller_pname=%a\n" Procname.pp caller_pname;
  F.printf "loc=%a\n" Location.pp loc;
  *)
  (* F.printf "=======================================\n" *)

(*
let _print_summary_accesses astate pname =
  F.printf "---- print_summary_accesses of %a ----\n" Procname.pp pname;
  (* F.printf "%a\n" AccessSet.pp_short astate.accesses; *)
  F.printf "%a\n" AccessSet.pp astate;
  F.printf "--------------------------------------\n"
*)

let print_vars_declared astate =
  F.printf "vars_declared: {";
  let rec print_vars = function
    | [] -> F.printf "}\n"
    (* | hd :: tl -> F.printf "%a, " HilExp.AccessExpression.pp hd; print_vars tl *)
    | hd :: tl ->
      let typ_string = Typ.to_string (snd hd) in
      F.printf "|(%a, %s)|" Mangled.pp (fst hd) typ_string; print_vars tl
  in
  print_vars astate.vars_declared

let _print_astate_all astate loc caller_pname =
  F.printf "========= printing astate... ==========\n";
  F.printf "access=%a\n" AccessSet.pp astate.accesses;
  F.printf "lockset=%a\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a\n" Lockset.pp astate.unlockset;
  F.printf "threads_active=%a\n" ThreadSet.pp astate.threads_active;
  F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
  F.printf "caller_pname=%a\n" Procname.pp caller_pname;
  F.printf "loc=%a\n" Location.pp loc;
  print_vars_declared astate;
  F.printf "=======================================\n"

(*
let _print_summary_accesses astate pname =
  F.printf "---- print_summary_accesses of %a ----\n" Procname.pp pname;
  (* F.printf "%a\n" AccessSet.pp_short astate.accesses; *)
  F.printf "%a\n" AccessSet.pp astate;
  F.printf "--------------------------------------\n"
*)

(* FIXME var is any expression now (n$7 etc.`) *)
let add_access_to_astate var access_type astate loc pname =
  F.printf "Inside add_access_to_astate in Domain\n";
  let new_access : AccessEvent.t = (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread =
      (* if there is no thread in threads_active -> the access is not in main function*)
      if (ThreadSet.equal ThreadSet.empty astate.threads_active) then
        None
      else
        create_main_thread
    in
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

let print_actuals actuals =
  let rec loop = function
    | [] -> F.printf "\n"
    | hd :: tl -> F.printf "| %a |" HilExp.pp hd; loop tl
  in loop actuals

let print_formals formals =
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

(* myslim, ze integrate_summary je stejna jako uintegrate_pthread_summary, akorat se nepridava aktualne nove vlakno, 
   takze nevim, jake vlakno k tem pristupum pridat -> TODO vymyslet!! *)
(* plus tady se jeste musi nejak integrovat locks, threads atd. -> jeste neni domyslene *)
let integrate_summary astate callee_pname loc callee_summary callee_formals actuals caller_pname =
  F.printf "integrate_summary: callee_pname=%a in Darc\n" Procname.pp callee_pname;
  F.printf "astate %a ---------------------------------------\n" Procname.pp caller_pname;
  print_astate astate loc caller_pname;
  F.printf "summary %a --------------------------------------\n" Procname.pp callee_pname;
  print_astate callee_summary loc callee_pname;
  F.printf "callee_formals: --------------------------------------\n";
  print_formals callee_formals;
  F.printf "actuals: --------------------------------------\n";
  print_actuals actuals;
  F.printf "--------------------------------------\n";
  F.printf "vars_declared: --------------------------------\n";
  print_vars_declared astate;
  (* TODO important *)
  (* pridat do accesses vlakno, na kterem prave jsem -> v podstate to bude proste bud main nebo None *)
  (* FIXME je to pravda? Ze vzdy bude bud main nebo None?!?!?! *)
  (* podle me by tu melo byt ze se vezme current thread -> pridat do summary? nelze, 
     protoze kdyz se vytvori thread, muze jich tam byt vic current threads*)
  let current_thread = 
    if (ThreadSet.equal ThreadSet.empty astate.threads_active) then
      None
    else create_main_thread (* false, upravit a zmenit na neco jineho! -> mozna to neni spatne, jen upravit podminku -> main se tam da, pokud uz nam bezi main thread, ne pokud je mnozina threads_active prazdna -> to muze nastat i tehdy, pokud jeste nebezi main, ale uz jsme vytvorili nejake vlakno -> wait ale 
       poradne rozmyslet -> co kdyz v main vytvorim vlakno t1 ktere jde do foo, ve foo vytvorim t2 ktere jde do bar *)
  in
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses astate.threads_active astate.lockset astate.unlockset current_thread) callee_summary.accesses in
  let accesses_joined = AccessSet.join astate.accesses edited_accesses_from_callee in
  F.printf "integrated summary: ========================================\n";
  print_astate { astate with accesses=accesses_joined } loc caller_pname;
  F.printf "============================================================\n";
  { astate with accesses=accesses_joined }
  (* TODO formals to actuals *)
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
    let aliases = AliasesSet.union astate1.aliases astate2.aliases in  (* TODO FIXME how to join aliases*)
    let vars_declared = [] in (* TODO *)
    { threads_active; accesses; lockset; unlockset; aliases; vars_declared }
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
