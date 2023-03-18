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

  let compare at1 at2 =
    if phys_equal at1 Write && phys_equal at2 Write then 0
    else if phys_equal at1 Read && phys_equal at2 Read then 0
    else if phys_equal at1 Write && phys_equal at2 Read then 1
    else -1

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
    | Read  -> "read"
    | Write -> "write"

end

module ThreadEvent = struct
  type t = (AccessPath.t * Location.t)

  (* 0 -> the threads are the same, 1 -> false *)
  let compare ((base, aclist) as th, loc) ((base', aclist') as th', loc') =
    (* F.printf "comparing threads: %a and %a\n" AccessPath.pp th AccessPath.pp th'; *)
    let result_th =
      if (Int.equal (AccessPath.compare th th') 0) then 0
      else begin
        let res = AccessPath.compare_base base base' in
        if not (Int.equal res 0) then res
        else
          List.compare AccessPath.compare_access aclist aclist'
      end
    in
    if (Int.equal result_th 0) then
      Location.compare loc loc'
    else
      result_th


  let pp fmt (th, loc) =
    F.fprintf fmt "%a on %a" AccessPath.pp th Location.pp loc;

end

module ThreadSet = AbstractDomain.FiniteSet(ThreadEvent)

module Aliases = struct 
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t)

  (* TODO *)
  let compare t1 t2 =
    let fst_compare = HilExp.AccessExpression.compare (fst t1) (fst t2) in
    let snd_compare = HilExp.AccessExpression.compare (snd t1) (snd t2) in
    let compare_result =
      if not (Int.equal fst_compare 0) then
        fst_compare
      else
        snd_compare
    in
    (* F.printf "compare Aliases: %d, fst_compare: %d, snd_compare: %d\n" compare_result fst_compare snd_compare; *)
    compare_result

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

  let print_lockset access =
      let locked_list = Lockset.elements access.locked in
      F.printf " {";
      let rec print_list lst =
        match lst with
        | [] -> F.printf "} "
        | lock :: t -> (
          F.printf "%a " AccessPath.pp (fst lock);
          print_list t
        )
      in
      print_list locked_list

  let print_access_pair (t1, t2) =
    let t1_access_string = ReadWriteModels.access_to_string t1.access_type in
    F.printf "(%a, %a, %s, " HilExp.AccessExpression.pp t1.var Location.pp t1.loc t1_access_string;
    print_lockset t1;
    let t2_access_string = ReadWriteModels.access_to_string t2.access_type in
    F.printf "| %a, %a, %s, " HilExp.AccessExpression.pp t2.var Location.pp t2.loc t2_access_string;
    print_lockset t2;
    F.printf ")\n"

  let compare a1 a2 =
    (* F.printf "comparing accesses: \n";
    print_access_pair (a1, a2); *)
    let compare_result =
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
      (*
      F.printf "compare AccessEvent var_cmp: %d\n" var_cmp;
      F.printf "compare AccessEvent loc_cmp: %d\n" loc_cmp;
      F.printf "compare AccessEvent access_type_cmp: %d\n" access_type_cmp;
      F.printf "compare AccessEvent locked: %d\n" locked_cmp;
      F.printf "compare AccessEvent unlocked: %d\n" unlocked_cmp;
      F.printf "compare AccessEvent threads_active_cmp: %d\n" threads_active_cmp;
      F.printf "compare AccessEvent thread_cmp: %d\n" thread_cmp;
      *)
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
    in
    (* F.printf "compare AccessEvent: %d\n" compare_result; *)
    compare_result

  let _equal t1 t2 = Int.equal 0 (compare t1 t2)
  let _hash t1 = Hashtbl.hash t1.loc

  let get_var access =
    access.var

  let edit_accesses threads_active lockset unlockset thread access = 
    (* create new access and use information from astate (sth like union access.lockset & astate.lockset etc.) *)
    let locked = Lockset.diff (Lockset.union lockset access.locked) access.unlocked in
    let unlocked = Lockset.union (Lockset.diff unlockset access.locked) access.unlocked in
    let threads_active = ThreadSet.union threads_active access.threads_active in
    let thread =
      match access.thread with
      | None -> thread
      | Some th -> Some th
    in
    { var=access.var; loc=access.loc; access_type=access.access_type; locked; unlocked; threads_active; thread }

  let edit_var_in_access new_var access access_type =
    {access with var=new_var; access_type}

(* TODO zkopirovano z HilExp.ml *)
let rec replace_inner_var var actual =
      let replace_base_inner = replace_inner_var actual in
      match var with
      | HilExp.AccessExpression.Dereference (Base _) ->
          HilExp.AccessExpression.dereference actual
      | HilExp.AccessExpression.Dereference ae ->
          HilExp.AccessExpression.dereference (replace_base_inner ae)
      (* TODO muze vubec nastat? asi yes -> na r muze byt pristup k address_of! poresit *)
      | HilExp.AccessExpression. AddressOf ae ->
          let address_of_option = HilExp.AccessExpression.address_of (replace_base_inner ae) in
          let res =
            match address_of_option with
            | Some opt -> (F.printf "Some address_of: %a\n" HilExp.AccessExpression.pp opt; opt)
            | None -> (F.printf "None address_of -> check!\n"; ae) (* napr. &(&a) -> v kodu teoreticky muze nastat, ale toto neni spravny zapis! -> TODO *)
          in
          res
      (* TODO
      | Base _ ->
          Base base_new
      | FieldOffset (ae, fld) ->
          FieldOffset (replace_base_inner ae, fld)
      | ArrayOffset (ae, typ, x) ->
          ArrayOffset (replace_base_inner ae, typ, x)
      *)
      | _ ->
          actual

  let edit_accesses_with_actuals formal actual access =
    F.printf "edit_accesses_with_actuals\n";
    (* TODO convert formal to access_path nebo neco podobneho  *)
    (* TODO musim porovnavat base, ne cely access_expression *)
    (* TODO prevest base na access_expression *)
    let access_var_base = HilExp.AccessExpression.get_base access.var in
    let access_var_base_ae = HilExp.AccessExpression.base access_var_base in
    if HilExp.AccessExpression.equal access_var_base_ae formal then
      begin
      F.printf "var=%a, formal=%a\n" HilExp.AccessExpression.pp access.var HilExp.AccessExpression.pp formal;
      F.printf "YAY\n";
      let result =
        match actual with
        | HilExp.AccessExpression ae ->
          (* TODO replace base -> musim replacnout base, ale ne ty hvezdicky a ampersandy *)
          (* TODO co je remove_deref_after_base? *)
          (* potrebuji z toho udelat ten typ, jakeho bylo access.var, ale s tim, ze ta promenna bude proste actual -> pozor ale, actual je ae, neni to base! *)
          let replaced = replace_inner_var access.var ae in
          F.printf "replaced=%a\n" HilExp.AccessExpression.pp replaced;
          (* ani jedno z veci above neni spravne,
             potrebuji nahradit formal za actual, ale nechat access expression type jako byl ve var,
             tzn. napr. f=r, a=&i, var=*(r) -> do var dostat *(&i) *)
          { access with var=replaced }
        | _ -> (* assert false TODO *)
          F.printf "Not an AccessExpression in procedure edit_accesses_with_actuals in DarcDomain.ml\n";
          (* access nepridavat -> TODO vyresit, jak to udelat, aby se proste odstranil *)
          access
      in
      result
      (* edited access *)
      end
    else
      begin
      F.printf "var=%a, formal=%a\n" HilExp.AccessExpression.pp access.var HilExp.AccessExpression.pp formal;
      F.printf "access.var and formal are not the equal - TODO what are they?\n";
      access
      end

  let predicate_loc (a1, a2) =
    if Location.compare a1.loc a2.loc <= 0 then true else false



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
    F.fprintf fmt "{%a, %s, %a, " HilExp.AccessExpression.pp t1.var (ReadWriteModels.access_to_string t1.access_type) Location.pp t1.loc;
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

  let predicate_read_write (a1, a2) = (* a1 == rd and a2 == rd -> false *)
    match (a1.access_type, a2.access_type) with
    | (ReadWriteModels.Read, ReadWriteModels.Read) -> false
    | _ -> true

  let predicate_threads_intersection (a1, a2) = (* length(intersect ts1 ts2) < 2 -> false *)
    let intersect = ThreadSet.inter a1.threads_active a2.threads_active in
    let len = ThreadSet.cardinal intersect in
    if len < 2 then false else true

  let predicate_locksets (a1, a2) = (* intersect ls1 ls2 == {} -> false *) (* TODO nestaci aby aspon lockset alespon jednoho pristupu byla prazdna? *)
    let _both_empty =
      if ((phys_equal a1.locked Lockset.empty) && (phys_equal a2.locked Lockset.empty)) 
        then true else false in
    let intersect = Lockset.inter a1.locked a2.locked in
    if Lockset.equal intersect Lockset.empty (* && not both_empty *) then true else false (* TODO wtf to nejak neodpovida *)
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
  load_aliases: (HilExp.AccessExpression.t * HilExp.AccessExpression.t * Exp.t) list;
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

let print_load_aliases (ae1, ae2, e) =
  F.printf "(%a, %a, %a), e: " HilExp.AccessExpression.pp ae1 HilExp.AccessExpression.pp ae2 Exp.pp e;
  match e with
  | Exp.Var var -> F.printf "Var %a\n" Ident.pp var
  | Exp.UnOp _ -> F.printf "UnOp\n" (* of Unop.t * t * Typ.t option  (** Unary operator with type of the result if known *) *)
  | Exp.BinOp _ -> F.printf "BinOp\n" (* of Binop.t * t * t  (** Binary operator *) *)
  | Exp.Exn _exn -> F.printf "Exn\n" (* of t  (** Exception *) *)
  | Exp.Closure closure ->  F.printf "Closure %a\n" Exp.pp_closure closure (* of closure  (** Anonymous function *) *)
  | Exp.Const _const -> F.printf "Const\n" (* Const.pp const  (** Constants *)*)
  | Exp.Cast _ -> F.printf "Cast\n" (* of Typ.t * t  (** Type cast *) *)
  | Exp.Lvar lvar -> F.printf "Lvar %a\n" Pvar.pp_value lvar (** The address of a program variable *)
  | Exp.Lfield (exp, fieldname, _typ) -> F.printf "Lfield exp: %a fieldname: %a\n" Exp.pp exp Fieldname.pp fieldname (* of t * Fieldname.t * Typ.t *)
                    (** A field offset, the type is the surrounding struct type *)
  | Exp.Lindex _ -> F.printf "Lindex\n" (* )of t * t  (** An array index offset: [exp1\[exp2\]] *) *)
  | Exp.Sizeof _ -> F.printf "Sizeof\n" (*  sizeof_data *)

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

let rec find_mem_alias var aliases =  (* return Aliases.t option *)
 match aliases with
 | [] -> F.printf "find_mem_alias: None\n"; None
 | (fst, snd, _)::t -> (
   F.printf "find_mem_alias: fst: %a, snd: %a, lhs: %a\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd HilExp.AccessExpression.pp var;
   if ((HilExp.AccessExpression.equal fst var)) (* || (HilExp.AccessExpression.equal snd var)) *) then (
     F.printf "find_mem_alias: %a, rhs: .a\n" Aliases.pp (fst, snd) (* HilExp.AccessExpression.pp rhs *);
     Some (fst, snd)
   ) else (
     find_mem_alias var t
   )
 )

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

(* funkce projde pres vsechny aliasy a prida je do mnoziny, ktera je nasledne ve volajici funkci sloucena s mnozinou accesses z astate *)
let rec record_all_aliased_accesses lhs lhs_current var aliases accesses_set access_to_modify access_type =
(*  F.printf "----------------- record_all_aliased_accesses: ------------------\n";*)
(*  F.printf "accesses_before: %a\n" AccessSet.pp accesses_set;*)
  if (HilExp.AccessExpression.equal lhs lhs_current) then
    begin
      F.printf "NO check_lhs-if: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      (* add var to accesses as Write TODO: (pokud je to lhs, pokud rhs, tak vzdy Read) *)
      (* if addressOf -> zapsat lhs, else zapsat var *)
      let var_to_add =
        match lhs with
        | HilExp.AccessExpression.AddressOf _ -> ( F.printf "addressOf %a\n" HilExp.AccessExpression.pp lhs; lhs )
        | _ -> (F.printf "%a, returning %a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp var; var )
      in
      let new_access = AccessEvent.edit_var_in_access var_to_add access_to_modify access_type in
      let new_accesses_set = AccessSet.add new_access accesses_set in
      F.printf "Adding new access - Write...\n";

      (* mam access -> jen zmenim var *)
      F.printf "new_accesses_after: %a\n" AccessSet.pp new_accesses_set;
      new_accesses_set
      (* TODO proc je tu tohle:
      let alias = find_alias var aliases in (* e.g. None | Some (y, &k) *)
      match alias with
      | Some alias -> Some alias   (* return alias *)
      | None -> Some (var, var)    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
      *)
    end
  else
    begin
      (* NOT ADDING READ ACCESSES ANYMORE - it was used before the switch to SIL *)
      F.printf "NO check_lhs-else: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
      (* add var to accesses as Read *)
      (* if addressOf -> zapsat lhs, else zapsat var *)
      match lhs with
      | HilExp.AccessExpression.AddressOf _ -> (
         (* TODO is it still valid? *)
(*         F.printf "addressOf\n";*)
         (* add to accesses, ale uz nepokracovat rekurzi *)
         let new_access = AccessEvent.edit_var_in_access lhs access_to_modify ReadWriteModels.Read in
         let new_accesses_set = AccessSet.add new_access accesses_set in
         F.printf "new_accesses_after: %a\n" AccessSet.pp new_accesses_set;
         new_accesses_set
       )
      | _ -> (
        (* not using anymore because of SIL LOAD
        let new_access = AccessEvent.edit_var_in_access var access_to_modify ReadWriteModels.Read (* TODO vzdy je tu Read I think *) in
        let new_accesses_set = AccessSet.add new_access accesses_set in
        F.printf "Adding new access - Read...\n";
        (* mam access -> jen zmenim var *)
        F.printf "new_accesses_after: %a\n" AccessSet.pp new_accesses_set;
        *)
        let find_current_in_aliases = find_alias var aliases in (* e.g. None | Some (m, &y) *)
        let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *)
        match find_current_in_aliases with
        | None -> (* new_accesses_set *) accesses_set
        | Some (_, snd) -> (
          let snd_dereference = HilExp.AccessExpression.dereference snd in
          (* rekurze s tim, co je vpravo v aliasu *)
          record_all_aliased_accesses lhs lhs_dereference snd_dereference aliases (* new_accesses_set *) accesses_set access_to_modify access_type
        )
      )
    end

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

let get_base_alias lhs aliases = (* vraci None | Some (m, &y) *)
  let lhs_base = HilExp.AccessExpression.get_base lhs in
  let lhs_ae = HilExp.AccessExpression.base lhs_base in
  check_lhs lhs lhs_ae lhs_ae aliases

let replace_var_with_aliases var aliases = (* if alias is not found, var is returned *)
  let var_base = HilExp.AccessExpression.get_base var in
  let var_ae = HilExp.AccessExpression.base var_base in
  let result_option = check_lhs var var_ae var_ae aliases in
  match result_option with
  | None -> var
  | Some (_, snd) -> snd

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
  let var_base = HilExp.AccessExpression.get_base var in
  let var_ae = HilExp.AccessExpression.base var_base in
  let result_option = check_lhs_without_address_of var var_ae var_ae aliases in
  match result_option with
  | None -> (
    (* zkusime najit v heap_aliases a vratit list aliasu, za ktere se to aliasuje -> pak musime udelat pristup ke kazdemu *)
    var
  )
  | Some (_, snd) -> (
    snd
  )


(* TODO add when malloc *)
let add_heap_alias var loc astate =
  let new_heap_alias = (var, loc) in
  F.printf "add_heap_alias: (%a, %a)\n" HilExp.AccessExpression.pp var Location.pp loc;
  F.printf "add_heap_alias before:\n";
  _print_heap_aliases_list astate;
  let new_heap_aliases = new_heap_alias :: astate.heap_aliases in
  let new_astate = {astate with heap_aliases = new_heap_aliases} in
  F.printf "add_heap_alias after:\n";
  _print_heap_aliases_list new_astate;
  new_astate

(* TODO remove when free (and aliasing to other variable?) *)
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

let rec find_heap_alias_by_var var heap_aliases =
  match heap_aliases with
  | [] -> (F.printf "find_heap_alias_by_var: None\n"; None)
  | (fst, loc) :: t -> (
    if HilExp.AccessExpression.equal var fst then
      begin
        F.printf "find_heap_alias_by_var: loc:%a\n" Location.pp loc;
        Some loc
      end
    else
      begin
        F.printf "find_heap_alias_by_var: var: %a, fst: %a - else\n" HilExp.AccessExpression.pp var HilExp.AccessExpression.pp fst;
        find_heap_alias_by_var var t
      end
  )

let rec find_load_alias_by_var var load_aliases =
  match load_aliases with
  | [] -> None
  | (fst, snd, _) :: t -> (
    if HilExp.AccessExpression.equal var fst then
      Some (fst, snd)
    else
      find_load_alias_by_var var t
  )

let remove_heap_alias_by_var_name var astate =
  (* find var alias in heap_aliases, return loc *)
  let loc_of_alias_to_be_removed = find_heap_alias_by_var var astate.heap_aliases in
  match loc_of_alias_to_be_removed with
  | Some loc ->
    (* remove all heap_aliases with the returned loc *)
    let updated_heap_aliases = remove_heap_aliases_by_loc loc astate in
    let new_astate = { astate with heap_aliases=updated_heap_aliases } in
    F.printf "heap_aliases after remove by free: ";
    _print_heap_aliases_list new_astate;
    new_astate
  | None -> astate

let find_heap_aliases_with_same_loc loc list =
  let rec find loc list acc =
    match list with
    | [] -> acc
    | (var, snd)::t -> (
      if Location.equal loc snd then
        find loc t (var::acc)
      else
        find loc t acc
    )
  in
  find loc list []

let find_in_heap_aliases var heap_aliases : HilExp.AccessExpression.t list =
  (* rekurzivne projit heap_aliases a kazdy alias vratit *)
  (* tzn. nejdriv najit jeden, z toho si vzit loc a pak projit cely list znovu a kazdou promennou se stejnym loc vratit *)
  let heap_alias =
    let rec find_heap_alias var list =
      match list with
      | [] -> None
      | (fst, loc)::t -> (
        if HilExp.AccessExpression.equal fst var then
          Some (fst, loc)
        else
        find_heap_alias var t
      )
    in
    find_heap_alias var heap_aliases
  in
  match heap_alias with
  | None -> []
  | Some (_, loc) ->
    (* projit heap aliases a kazdy alias s loc pridat do listu aliasu *)
    find_heap_aliases_with_same_loc loc heap_aliases

(* tato funkce pracuje s heap aliases - vraci list, ktery muze byt i empty, nebo obsahuje promenne, ke kterym ma byt vytvoren pristup *)
let _replace_var_with_aliases_without_address_of_list var astate : HilExp.AccessExpression.t list = (* if alias is not found, var is returned *)
  let var_base = HilExp.AccessExpression.get_base var in
  let var_ae = HilExp.AccessExpression.base var_base in
  let result_option = check_lhs_without_address_of var var_ae var_ae (AliasesSet.elements astate.aliases) in
  match result_option with
  | None -> (
    (* zkusime najit v heap_aliases a vratit list aliasu, za ktere se to aliasuje -> pak musime udelat pristup ke kazdemu *)
    let list_with_accesses = find_in_heap_aliases var astate.heap_aliases in
    list_with_accesses
    (* FIXME vratit var, pokud bude list empty? bude vubec nekdy empty? vzdy by mel byt k pointeru bud alias na stacku, nebo na heapu *)
    (*var*)
  )
  | Some (_, snd) -> (
    [snd]
  )

(* funkce vraci mnozinu novych pristupu *)
let add_aliased_vars_to_accesses var var_access aliases access_type =
  let empty_accesses = AccessSet.empty in
  let var_base = HilExp.AccessExpression.get_base var in
  let var_ae = HilExp.AccessExpression.base var_base in
  (* returns accesses with new access *)
  record_all_aliased_accesses var var_ae var_ae aliases empty_accesses var_access access_type
  (*
  match result_option with
  | None -> var
  | Some (_, snd) -> snd
  *)

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

(* TODO vyresit, kdyz se prida nejaky pointer na malloc, ktery uz predtim ale byl v aliases
   -> napr bylo (p, &j), ale ted jsme pridali p jako pointer na malloc -> musi se odstranit
   z aliases uplne *)
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
     (* TODO bylo tu None -> proc? *)
     (* None *)
     find_alias lhs (AliasesSet.elements astate.aliases)
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
 match rhs with
   | HilExp.AccessExpression.AddressOf _ae -> (
     F.printf "rhs_alias_snd: addressOf: rhs: %a\n" HilExp.AccessExpression.pp rhs;
     let rhs_alias_snd = Some rhs in
     F.printf "new_alias:\n";
             let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in (* Some (y, &z) *)
             F.printf "new_alias: ";
             _print_alias new_alias;
             F.printf "remove_alias_from_aliases:\n";
            F.printf "aliases: %a\n" AliasesSet.pp astate.aliases;
            F.printf "alias to be removed: \n";
            _print_alias lhs_alias;
             let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in (* astate *)
             F.printf "aliases_removed: %a\n" AliasesSet.pp astate_alias_removed.aliases;
             F.printf "final_astate:\n";
             let final_astate = add_new_alias_no_option astate_alias_removed new_alias in (* astate *)
             F.printf "final_astate: %a\n" AliasesSet.pp final_astate.aliases;
             final_astate
   )
   | _ -> (  (* base, dereference etc. *)
     let rhs_alias = get_base_alias rhs aliases in (* *q -> Some (x, &z) *)
     match rhs_alias with
     | Some _alias -> (
       let rhs_alias_snd = get_option_snd rhs_alias (* Some (x, &z) -> Some &z *) in
       (* TODO rovnou tady pridat do aliases a vratit novy astate *)
        F.printf "new_alias:\n";
        let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in (* Some (y, &z) *)
        F.printf "new_alias: ";
        _print_alias new_alias;
        F.printf "remove_alias_from_aliases:\n";
       F.printf "aliases: %a\n" AliasesSet.pp astate.aliases;
       F.printf "alias to be removed: \n";
       _print_alias lhs_alias;
        let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in (* astate *)
        F.printf "aliases_removed: %a\n" AliasesSet.pp astate_alias_removed.aliases;
        F.printf "final_astate:\n";
        let final_astate = add_new_alias_no_option astate_alias_removed new_alias in (* astate *)
        F.printf "final_astate: %a\n" AliasesSet.pp final_astate.aliases;
        final_astate
     )
     | None -> (
       (* TODO find in heap aliases, pokud je v heap aliases, pak pridat i lhs do heap aliases, jinak netusim, asi nic, nemelo by nastat *)
       (* ma to vracet access_expression - pozor, zaridit, at se dale neprida hlavne do nejakych normalnich aliases! *)
       (* TODO rovnou pak heap alias pridat do heap aliases a vratit novy astate *)
       (* find rhs in heap aliases *)
       let rhs_heap_alias_loc = find_heap_alias_by_var rhs astate.heap_aliases in
       let new_astate =
         match rhs_heap_alias_loc with
         | None -> (
           (* FIXME muze nastat? a co s tim? *)
           F.printf "rhs_heap_alias_loc was not found\n";
           astate
         )
         | Some loc -> (
           F.printf "alias found: (%a, %a), lhs: %a\n" HilExp.AccessExpression.pp rhs Location.pp loc HilExp.AccessExpression.pp lhs;
           (* add lhs - ne rhs?? with loc to heap aliases *)
           (* add new heap aliases to astate *)
           let astate_with_new_heap_alias = add_heap_alias lhs loc astate in
           (* remove lhs alias from aliases, TODO: pripadne from heap aliases, pokud uz tam byl *)
           let astate_alias_removed = remove_alias_from_aliases lhs_alias astate_with_new_heap_alias in (* astate *)
           (* return new astate *)
           astate_alias_removed
         )
       in
       (* return new astate *)
       new_astate
     )
   )

(* in*)
(* F.printf "new_alias:\n";*)
(* let new_alias = create_new_alias lhs_alias_fst rhs_alias_snd in (* Some (y, &z) *)*)
(* F.printf "new_alias: ";*)
(* _print_alias new_alias;*)
(* F.printf "remove_alias_from_aliases:\n";*)
(*F.printf "aliases: %a\n" AliasesSet.pp astate.aliases;*)
(*F.printf "alias to be removed: \n";*)
(*_print_alias lhs_alias;*)
(* let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in (* astate *)*)
(* F.printf "aliases_removed: %a\n" AliasesSet.pp astate_alias_removed.aliases;*)
(* F.printf "final_astate:\n";*)
(* let final_astate = add_new_alias_no_option astate_alias_removed new_alias in (* astate *)*)
(* F.printf "final_astate: %a\n" AliasesSet.pp final_astate.aliases;*)
(* final_astate*)
 (*
 FIXME malloc extension:
 ...lhs alias najit a ulozit si, prootze pokud bude nalezen  rhs v heap_aliases, musi byt lhs alias odstranen
 ...rhs alias zkontrolovat, pokud je po get_base_alias None, tak prohledat heap_aliases
 a pokud byl nejaky heap_alias nalezen, pak odstranit lhs alias a pridat rhs do heap_aliases

 *)

(* function returns None or Some (thread, loc) *)
let create_thread_from_load_ae load loc astate =
    let thread_load_alias = find_load_alias_by_var load astate.load_aliases in
    match thread_load_alias with
    | None -> (
      let load_ap = HilExp.AccessExpression.to_access_path load in
      (load_ap, loc)
    )
    | Some (_, final_thread) -> (
      (* create new thread *)
      let final_thread_ap = HilExp.AccessExpression.to_access_path final_thread in
      (final_thread_ap, loc)
    )

let add_thread thread astate =
  let threads_active = ThreadSet.add thread astate.threads_active in
  { astate with threads_active }

(* return None or Some (thread_ae, thread_loc) *)
let find_thread_in_threads_active thread_name threads =
  let threads_list : (AccessPath.t * Location.t) list = ThreadSet.elements threads in
  let rec find lst =
    match lst with
    | [] -> None
    | (th_ap, _) as th :: t -> (
      if (AccessPath.equal th_ap thread_name) then
        Some th
      else
        find t
    )
  in
  find threads_list

let remove_thread load astate =
  (* find thread by its name in threads *)
  let thread_load_alias = find_load_alias_by_var load astate.load_aliases in
  match thread_load_alias with
  | None -> astate
  | Some (_, thread_ae) -> (
    let thread_name = HilExp.AccessExpression.to_access_path thread_ae in
    (* find the thread in threads_active *)
    let thread = find_thread_in_threads_active thread_name astate.threads_active in
    match thread with
    | Some th ->
      F.printf "Removing thread: %a \n" ThreadEvent.pp th;
      (* remove the thread *)
      let threads_active = ThreadSet.remove th astate.threads_active in
      { astate with threads_active }
    | None -> astate
  )

let create_main_thread = 
  let pname = Procname.from_string_c_fun "main" in
  let pvar_from_pname : Pvar.t = Pvar.mk_tmp "'main_thread'" pname in
  let tvar_name = Typ.TVar "thread" in
  let typ_main_thread = Typ.mk tvar_name in
  let acc_path_from_pvar : AccessPath.t = AccessPath.of_pvar pvar_from_pname typ_main_thread in
  Some (acc_path_from_pvar, Location.dummy)

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


let print_astate astate  =
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

(* FIXME var is any expression now (n$7 etc.`) *)
let add_access_to_astate var access_type astate loc =
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
  print_astate new_astate;
  { astate with accesses }

(* TODO function for read_expression -> initial access_type is rd *)
let _load_first id e typ loc astate =
  F.printf "load ---\n";
  let id_ae = HilExp.AccessExpression.of_id id typ in
  F.printf "id_ae: %a\n" HilExp.AccessExpression.pp id_ae;
  let e_var = Var.of_id id in
  let add_deref = match (e_var : Var.t) with LogicalVar _ -> true | ProgramVar _ -> false in
  let e_hil_exp = transform_sil_expr_to_hil e typ add_deref in
  F.printf "e_ae: %a\n" HilExp.pp e_hil_exp;
  match e_hil_exp with
  | HilExp.AccessExpression e_ae -> (
    let astate =
      match e with
      | Exp.Lvar _lvar -> (
        (* add read access *)
        F.printf "lvar: %a\n" HilExp.AccessExpression.pp e_ae;
        add_access_to_astate e_ae ReadWriteModels.Read astate loc
      )
      | Exp.Lfield _ -> (
        (* add read access of field? TODO *)
        astate
      )
      | Exp.Lindex _ -> (
        (* TODO *)
        astate
      )
      | _ -> astate
    in
    F.printf "e_ae: %a\n" HilExp.AccessExpression.pp e_ae;
    (* add to aliases or sth like aliases for local load *)
    let alias = (id_ae, e_ae) in
    let new_aliases = AliasesSet.add alias astate.aliases in
    F.printf "aliases before=%a\n" AliasesSet.pp astate.aliases;
    let astate = { astate with aliases=new_aliases } in
    F.printf "aliases after=%a\n" AliasesSet.pp astate.aliases;
    (* if e_ae je dereference, pak se pres aliasy chci zkusit dostat
       k puvodni promenne -> pokud neni v aliases, mel by to byt malloc
       nebo neco podobneho a nechame to pak ve tvaru *p *)
    (* vlastne musim zapisovat vsechno, pres co v aliasech prejdu - TODO jo? jakoze pristup k *p i j? *)
    let accesses =
      match e_ae with
      | HilExp.AccessExpression.Dereference _ ->
        (* find in aliases *)
        (* var_access -> access, ktery je k var, mel by obsahovat vsechno info o zamcich, vlaknech atd. TODO *)
        let var_access : AccessEvent.t =
            (* z replace_var_with_aliases dostanu jen jednu promennou - ale potrebuji vsechny, pres ktere to jde (jako Read krome posledni) *)
            (* let lhs_var_aliased = replace_var_with_aliases var (AliasesSet.elements astate.aliases) in *)
            (* var je zatim dummy_var *)
            let access_type = ReadWriteModels.Read in (* TODO appropriate access_type*)
            let locked = astate.lockset in
            let unlocked = astate.unlockset in
            let threads_active = astate.threads_active in
            (* let thread = if (phys_equal (String.compare (Procname.to_string pname) "main") 0) then create_main_thread else
              (* if the astate.threads_active contains main thread -> the thread is main, alse None? *)
              (* or simply if the procedure is main -> main thread *)
                None in (* TODO in the case of main... *) (* TODO create_main_thread *) *)
            let thread = None in (* TODO!!!!!!!!!!! *)
            { var=e_ae; loc; access_type; locked; unlocked; threads_active; thread }
        in
        let new_accesses = add_aliased_vars_to_accesses e_ae var_access (AliasesSet.elements astate.aliases) ReadWriteModels.Read in
        AccessSet.union astate.accesses new_accesses

      | _ -> astate.accesses
    in
    { astate with accesses }
  )
  | _ -> (
    F.printf "not an access expression\n";
    astate
  )

let fst_aliasing_snd exp mem_aliased : HilExp.AccessExpression.t =
  F.printf "fst_aliasing_snd:\n";
(*  let rec find e list = *)
(*    match list with *)
(*    | [] -> *)
  let exp_base = HilExp.AccessExpression.get_base exp in
  let exp_base_ae = HilExp.AccessExpression.base exp_base in
    let (* rec *) check_lhs lhs lhs_current var aliases =
      F.printf "-----------------mem_aliased:check_lhs:------------------\n";
(*      if (HilExp.AccessExpression.equal lhs lhs_current) then*)
(*        begin*)
          F.printf "mem_aliased:check_lhs: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
          match lhs with
          | HilExp.AccessExpression.AddressOf _addressOf -> lhs
          | _ -> (
            let alias = find_mem_alias var aliases in (* e.g. None | Some (y, &k) *)
            (* TODO rekurze!!! *)
            match alias with
            | Some (_, snd) -> snd   (* return alias *)
            | None -> (    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
              F.printf "BLAAAAAAAAAAAAAAAH tady bych mela provest heap_aliases projduti a vraceni seznamu vsech ae, ke kterym se pristupuje\n";
              (* jenze tahle funkce vraci jenom jeden vyraz, ale ja potrebuju list *)
              var
              (*pouzit new_astate = add_accesses_with_aliases_or_heap_aliases *)
              (* pokud puvodni lhs byla addressOf -> vratit zase addressOf! *)
            )
          )
(*        end*)
(*      else*)
(*        begin*)
(*          F.printf "mem_aliased:check_lhs-else: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;*)
(*          let find_current_in_aliases = find_alias var aliases in (* e.g. None | Some (m, &y) *) *)
(*          let lhs_dereference = HilExp.AccessExpression.dereference lhs_current in (* *m *) *)
(*          match find_current_in_aliases with*)
(*          | None -> None*)
(*          | Some (_, snd) -> ( *)
(*    (*        F.printf "else Some snd\n";*) *)
(*            let snd_dereference = HilExp.AccessExpression.dereference snd in*)
(*            check_lhs lhs lhs_dereference snd_dereference aliases*)
(*          )*)
(*        end*)
      in
      let res = check_lhs exp exp_base_ae exp_base_ae mem_aliased in
      F.printf "exp: %a, res: %a\n" HilExp.AccessExpression.pp exp HilExp.AccessExpression.pp res;
      match exp with
      | HilExp.AccessExpression.Dereference _ -> HilExp.AccessExpression.dereference res
      | _ -> res

let fst_aliasing_snd_with_dereference_counter exp mem_aliased : HilExp.AccessExpression.t =
  F.printf "fst_aliasing_snd_with_dereference_counter\n";
  let exp_base = HilExp.AccessExpression.get_base exp in
  let exp_base_ae = HilExp.AccessExpression.base exp_base in
    let (* rec *) check_lhs lhs lhs_current var aliases =
      F.printf "-----------------mem_aliased:check_lhs:------------------\n";
          F.printf "mem_aliased:check_lhs: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
          let alias = find_mem_alias var aliases in (* e.g. None | Some (y, &k) *)
          (* TODO rekurze!!! *)
          match alias with
          | Some (_, snd) -> HilExp.AccessExpression.dereference snd   (* var was found in aliases -> return alias *)
          | None -> ( (* the var is not in aliases *)
            (* try to find the var in heap_aliases *)
(*            let _loc_opt = find_heap_alias_by_var var astate in *)
            (* if exists, then projdi heap_aliases a pridej pristup ke kazdemu aliasu se stejnou loc *)
            (* if doesn't exist, nepridavej nic *)
            (* FIXME return var (only the second variable will be needed later) *)
            var
          )
      in
      let res = check_lhs exp exp_base_ae exp_base_ae mem_aliased in
      F.printf "exp: %a, res: %a\n" HilExp.AccessExpression.pp exp HilExp.AccessExpression.pp res;
      match exp with
      | HilExp.AccessExpression.Dereference _ -> HilExp.AccessExpression.dereference res
      | _ -> res

let store_with_alias e1 e2 loc astate =
  F.printf "store_with_alias---\n";
  let alias = (e1, e2) in
  (* TODO melo by byt rafinovanejsi - pokud uz nejaky alias je, musi se najit a dal aliasovat atd. *)
  let new_aliases = AliasesSet.add alias astate.aliases in
  F.printf "aliases before=%a\n" AliasesSet.pp astate.aliases;
  let astate = { astate with aliases=new_aliases } in
  F.printf "aliases after=%a\n" AliasesSet.pp astate.aliases;
  add_access_to_astate e1 ReadWriteModels.Write astate loc

let store e1 loc astate =
  F.printf "store ---\n";
(*  add_access_to_astate e1 ReadWriteModels.Write astate loc*)
  let var_access : AccessEvent.t =
    (* z replace_var_with_aliases dostanu jen jednu promennou - ale potrebuji vsechny, pres ktere to jde (jako Read krome posledni) *)
    (* let lhs_var_aliased = replace_var_with_aliases var (AliasesSet.elements astate.aliases) in *)
    (* var je zatim dummy_var *)
    let access_type = ReadWriteModels.Write in (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    (* let thread = if (phys_equal (String.compare (Procname.to_string pname) "main") 0) then create_main_thread else
    (* if the astate.threads_active contains main thread -> the thread is main, alse None? *)
    (* or simply if the procedure is main -> main thread *)
     None in (* TODO in the case of main... *) (* TODO create_main_thread *) *)
    let thread = None in (* TODO!!!!!!!!!!! *)
    { var=e1; loc; access_type; locked; unlocked; threads_active; thread }
  in
  let new_accesses = add_aliased_vars_to_accesses e1 var_access (AliasesSet.elements astate.aliases) ReadWriteModels.Write in
  let accesses = AccessSet.union astate.accesses new_accesses in
  { astate with accesses }


(*
  malloc:
    CALL malloc, ret_id: n$7, loc
    STORE e1:&n, e2: n$7

    -> malloc: heap_tmp: [(n$7, loc)]
    -> store:
         vidim (n$7, loc), mam (&n, n$7)
         hledam v heap_tmp e2 -> pak ho vezmu, vyrobim (e1, loc) a pridam do heap_aliases
*)


(*
  tmp_heap: [(n$7, loc), (n$8, loc)]
  astate.heap_aliases: [...]

  muzu vlozit ref na extras jako parametr funkce? ze by se to pak nemuselo vracet, ale rovnou by se to menilo
  a vse by bylo jednodussi a krasnejsi

  STORE e1 = &n, e2: n$7
  match tmp_aliases with
  | [] -> basic_store ... vraci astate
  | tmp_heap_not_empty ->
    NOVA FUNKCE not_basic_store ... vraci astate (ale nejak musim poresit tmp_heap)
    - idealne dat axtras ref jako argument a vracet proste jen astate
    | [] -> (astate, tmp_heap)
    | (var_tmp, loc_tmp) :: t -> (
      if (var_tmp == e2_ae) then (
      let var_ae = to_ae e1 in
      let new_astate = heap_store (var_ae, loc_tmp) in
      (* aktuLIZOVAT TMP_HEAP -> NEPRIDAVAT TENHLE member *)
      let new_tmp_heap = tmp_heap in
      (new_astate, tmp_heap)
      ) else (
      (* aktualizovat tmp_heap - pridat i tenhle member *)
      astate je furt astate
      new_tmp_heap = (var_tmp, loc_tmp) :: tmp_heap
      (astate, new_tmp_heap)
    )
  )
*)
(* TODO handle Cast ()n$4 etc. *)
let add_heap_alias_when_malloc e1_ae e2_ae loc astate tmp_heap =
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
  let astate_with_new_write_access = add_access_to_astate e1_ae ReadWriteModels.Write astate loc in
  (astate_with_new_write_access, tmp_heap)


let store_with_heap_alloc _e1 _typ _e2 _loc astate _pname _heap_tmp_list =
  astate
  (*
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
  (* go through the list *)
  (* find var member in load aliases *)
  (* vytvor alias ze (var, loc) *)
  (* pridej alias do astate.heap_aliases *)
  let rec for_each_heap_tmp list acc =
    match list with
    | [] -> astate
    | (ae, heap_tmp_loc)::t -> (
      (* if ae == e2 then (e1, loc), add to heap_aliases a odstran z heap_tmp - nebo nemusi se odstranovat - pak se maze *)


      (* find ae in load_aliases and get the var *)
      let loc = find_load_alias_by_var ae load_aliases in
      (* create (var, loc) heap alias *)
      let new_heap_alias = (var, loc) in
      let heap_aliases = new_heap_alias :: astate.heap_aliases in
      let astate = {astate with heap_aliases} in
      for_each_heap_tmp t astate
    )
  in
  for_each_heap_tmp heap_tmp_list astate []

  astate
  *)

(* go through aliases and add to acc every var with the same loc *)
let get_list_of_heap_aliases_with_same_loc_as_var var (astate : t) =
  (* find var in aliases *)
  let var_base = HilExp.AccessExpression.get_base var in
  let var_base_ae = HilExp.AccessExpression.base var_base in
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


let add_accesses_to_astate_with_aliases_or_heap_aliases e1_ae e1_aliased_final access_type astate loc =
  if (HilExp.AccessExpression.equal e1_ae e1_aliased_final) then
    begin
      F.printf "add_accesses_to_astate_with_aliases_or_heap_aliases: if, e1_ea: %a, e1_aliased_final: %a\n" HilExp.AccessExpression.pp e1_ae HilExp.AccessExpression.pp e1_aliased_final;
      (* var was not aliased - maybe it is in heap aliases and if not, add access to var *)
      let list_of_new_accesses_from_heap_aliases = get_list_of_heap_aliases_with_same_loc_as_var e1_ae astate in
      match list_of_new_accesses_from_heap_aliases with
      | [] -> (
        (* var was not in heap aliases -> add access to var *)
        add_access_to_astate e1_aliased_final access_type astate loc (* returns astate *)
      )
      | _ -> (
        (* recursively add access to the next var *)
        let rec add_heap_accesses accesses_to_add_list astate = (* returns astate *)
          match accesses_to_add_list with
          | [] -> astate
          | var_heap :: t -> (
            (* add access to var *)
            (* check if there is the dereference!!! or double dereference etc. *)
            let new_astate = add_access_to_astate var_heap access_type astate loc (* returns astate *) in
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
      add_access_to_astate e1_aliased_final access_type astate loc (* returns astate *)
    end

let load id_ae e_ae e (_typ: Typ.t) loc astate =
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
      let e_aliased = fst_aliasing_snd e_ae astate.load_aliases in
      F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
      (* find e_alised in aliases *)
      F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
      let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
      (* save alias to the load_aliases set *)
      let e_to_add = e_aliased_final in
      let new_mem_alias = (id_ae, e_to_add, e) in
        let load_aliases = new_mem_alias :: astate.load_aliases in
        let astate = { astate with load_aliases } in
        F.printf "load_aliases after:\n";
        _print_load_aliases_list astate;
        (* add all read access (if it is access to heap allocated variable with alias, there could be more accesses) *)
        let astate_with_new_read_accesses = add_accesses_to_astate_with_aliases_or_heap_aliases e_aliased e_aliased_final ReadWriteModels.Read astate loc in
        astate_with_new_read_accesses
  )
  | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> (
    F.printf "Lvar or Lfield or Lindex\n";
    let new_mem_alias = (id_ae, e_ae, e) in
      let load_aliases = new_mem_alias :: astate.load_aliases in
      let astate = { astate with load_aliases } in
      F.printf "load_aliases after:\n";
      _print_load_aliases_list astate;
      (* add read access *)
      let astate_with_new_read_access = add_access_to_astate e_ae ReadWriteModels.Read astate loc in
      astate_with_new_read_access
  )
  | _ -> (
    F.printf "other e, nemelo by nastat\n";
    let new_mem_alias = (id_ae, e_ae, e) in
      let load_aliases = new_mem_alias :: astate.load_aliases in
      let astate = { astate with load_aliases } in
      F.printf "load_aliases after:\n";
      _print_load_aliases_list astate;
      (* add read access *)
      let astate_with_new_read_access = add_access_to_astate e_ae ReadWriteModels.Read astate loc in
      astate_with_new_read_access
  )

let store_vol2 e1 typ e2 loc astate _pname =
  F.printf "handle_store_vol2 -------------\n";
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
      let e1_aliased = fst_aliasing_snd_with_dereference_counter e1_ae astate.load_aliases in
      F.printf "e1_aliased: %a\n" HilExp.AccessExpression.pp e1_aliased;
      (* find e_alised in aliases *)
      F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
      let e1_aliased_final = replace_var_with_aliases_without_address_of e1_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e1_aliased_final: %a\n" HilExp.AccessExpression.pp e1_aliased_final;
      (* TODO nerozbije vec napsana na radku niz cele pristupy k nepointerovskym promennym? ty totiz nebudou v zadnem aliasu a var muze se rovnat var *)
      (* astate vytvorit na zaklade toho, zda se var == e1_ae nebo ne - pokud rovna, find in heap_aliases, pokud nerovna, pridat normalni pristup *)
      let astate = add_accesses_to_astate_with_aliases_or_heap_aliases e1_aliased e1_aliased_final ReadWriteModels.Write astate loc in
      (* save alias to the load_aliases set *)
(*      let astate = add_access_to_astate e1_aliased_final ReadWriteModels.Write astate loc in*)
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
(*            add_deref*)
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
        match e2_hil with(* TODO LOVE *)
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
              let e2_aliased = fst_aliasing_snd e2_ae astate.load_aliases in
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

(* FIXME var is any expression now (n$7 etc.) *)
let assign_expr var astate loc pname access_type =
  F.printf "Inside assign_expr in Domain\n";
  let new_access : AccessEvent.t =
    (* z replace_var_with_aliases dostanu jen jednu promennou - ale potrebuji vsechny, pres ktere to jde (jako Read krome posledni) *)
    (* let lhs_var_aliased = replace_var_with_aliases var (AliasesSet.elements astate.aliases) in *)
    (* var je zatim dummy_var *)
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
  (* mam dummy access, ale pokud je to nejaky pointerovsky pristup, je potreba do accesses ulozit vsechny ty pristupy *)
  (* tzn. vytvorit tolik pristupu, kolikrat je promenna odkazovana pres pointery *)
  let new_accesses_from_assign = add_aliased_vars_to_accesses var new_access (AliasesSet.elements astate.aliases) access_type in
  (* let accesses = AccessSet.add new_access astate.accesses in *)
  let accesses = AccessSet.union astate.accesses new_accesses_from_assign in
  { astate with accesses }
(* FIXME var is any expression now (n$7 etc.) *)


let print_accesses accesses =
  F.printf "accesses: -----\n%a\n" AccessSet.pp accesses
(*
let _print_summary_accesses astate pname =
  F.printf "---- print_summary_accesses of %a ----\n" Procname.pp pname;
  (* F.printf "%a\n" AccessSet.pp_short astate.accesses; *)
  F.printf "%a\n" AccessSet.pp astate;
  F.printf "--------------------------------------\n"
*)


let _print_alias_opt alias =
  F.printf "print_alias_opt...\n";
  match alias with
  | None -> F.printf "None\n"
  | Some (fst, snd) -> F.printf "(%a, %a)\n" HilExp.AccessExpression.pp fst HilExp.AccessExpression.pp snd

(* implicitly Read *)
let _add_rhs_expr_to_accesses var astate loc pname =
  F.printf "Inside add_rhs_expr_to_accesses in Domain\n";
  let new_access : AccessEvent.t =
    let var_aliased = replace_var_with_aliases var (AliasesSet.elements astate.aliases) in
    let access_type = ReadWriteModels.Read in (* TODO appropriate access_type*)
    let locked = astate.lockset in
    let unlocked = astate.unlockset in
    let threads_active = astate.threads_active in
    let thread = if (phys_equal (String.compare (Procname.to_string pname) "main") 0) then create_main_thread else
      (* if the astate.threads_active contains main thread -> the thread is main, alse None? *)
      (* or simply if the procedure is main -> main thread *)

        None in (* TODO in the case of main... *) (* TODO create_main_thread *)
    { var=var_aliased; loc; access_type; locked; unlocked; threads_active; thread }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  F.printf "Accesses old: ------------\n";
  print_accesses astate.accesses;
  F.printf "Accesses new: ------------\n";
  print_accesses accesses;
  { astate with accesses }

let print_accesses accesses =
  F.printf "accesses: -----\n%a\n" AccessSet.pp accesses
(*
let _print_summary_accesses astate pname =
  F.printf "---- print_summary_accesses of %a ----\n" Procname.pp pname;
  (* F.printf "%a\n" AccessSet.pp_short astate.accesses; *)
  F.printf "%a\n" AccessSet.pp astate;
  F.printf "--------------------------------------\n"
*)

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

(*
let _print_summary_accesses astate pname =
  F.printf "---- print_summary_accesses of %a ----\n" Procname.pp pname;
  (* F.printf "%a\n" AccessSet.pp_short astate.accesses; *)
  F.printf "%a\n" AccessSet.pp astate;
  F.printf "--------------------------------------\n"
*)
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
    let actual_base = HilExp.AccessExpression.get_base actual_ae in
    let actual_base_ae = HilExp.AccessExpression.base actual_base in
    let is_in_locals = List.mem locals actual_base_ae ~equal:HilExp.AccessExpression.equal in
    match is_in_locals with
    | true -> remove_from_locals actual_base_ae locals []
    | false -> locals
  )
  | _ -> locals

(* TODO if argument funkce je null, pak nepredelavat formals na actuals a nepridavat ty pristupy k formals! *)
let integrate_pthread_summary astate thread callee_pname loc callee_summary callee_formals actuals caller_pname =
  F.printf "integrate_pthread_summary: callee_pname=%a on %a\n" Procname.pp callee_pname Location.pp loc;
  F.printf "summary of caller_pname=%a before --------" Procname.pp caller_pname;
  print_astate astate (* loc caller_pname *);
  F.printf "\nsummary of callee_pname=%a before --------" Procname.pp callee_pname;
  print_astate callee_summary (* loc caller_pname *);
  (* edit information about each access - thread, threads_active, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses astate.threads_active astate.lockset astate.unlockset (Some thread)) callee_summary.accesses in
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
        let e_aliased = fst_aliasing_snd e_ae astate.load_aliases in
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
        AccessSet.map (AccessEvent.edit_accesses_with_actuals callee_formal actual) edited_accesses_from_callee
    in
    (* join callee and caller accesses *)
    let accesses_joined = AccessSet.join astate.accesses edited_accesses in
    let astate = { astate with accesses=accesses_joined } in
    (* remove the variable from locals - remove base? *)
    let updated_locals = remove_var_from_locals actual astate.locals in
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
    if (ThreadSet.equal ThreadSet.empty astate.threads_active) then
      None
    else create_main_thread (* false, upravit a zmenit na neco jineho! -> mozna to neni spatne, jen upravit podminku -> main se tam da, pokud uz nam bezi main thread, ne pokud je mnozina threads_active prazdna -> to muze nastat i tehdy, pokud jeste nebezi main, ale uz jsme vytvorili nejake vlakno -> wait ale 
       poradne rozmyslet -> co kdyz v main vytvorim vlakno t1 ktere jde do foo, ve foo vytvorim t2 ktere jde do bar *)
  in
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses astate.threads_active astate.lockset astate.unlockset current_thread) callee_summary.accesses in
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
             let e_aliased = fst_aliasing_snd e_ae astate.load_aliases in
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
         (* let _edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses_with_actuals formal_access_expression actual) callee_summary.accesses in *)
         accesses_ref := AccessSet.map (AccessEvent.edit_accesses_with_actuals formal_access_expression actual) !accesses_ref;
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
  { astate with accesses=accesses_joined }

(* pokud se spravne naprogramuje porovnavani accessu a tim padem abstraktnich stavu,
   tak se po prvnim pridani accessu v cyklu uz pri druhem loopu zadny access neprida
   a ty dva stavy uz se vyhodnoti jako equal a mohly by se vyhodnotit na true *)

(* *)

let ( <= ) ~lhs ~rhs =
  F.printf "leq\n";
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
  F.printf "JOIN: new_astate after join:\n";
  print_astate new_astate;
  new_astate

let widen ~prev ~next ~num_iters:_ =
  F.printf "WIDEN\n";
  F.printf "prev\n";
  print_astate prev;
  F.printf "next\n";
  print_astate next;
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
  let rec _print_pairs_list lst =
    match lst with
    | [] -> F.printf "\n"
    | h::t -> AccessEvent.print_access_pair h; _print_pairs_list t in
  
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
(*  F.printf "threads_active_length_checked:\n";*)
  let threads_active_length_checked = List.filter ~f:AccessEvent.predicate_threads_active_length optimised_list in
(*  print_pairs_list threads_active_length_checked;*)
(*  F.printf "vars_checked:\n";  *)
  let vars_checked = List.filter ~f:AccessEvent.predicate_var threads_active_length_checked in
(*  print_pairs_list vars_checked;*)
(*  F.printf "read_write_checked:\n";*)
  let read_write_checked = List.filter ~f:AccessEvent.predicate_read_write vars_checked in
(*  print_pairs_list read_write_checked;*)
(*  F.printf "threads_checked:\n";*)
  let threads_checked = List.filter ~f:AccessEvent.predicate_thread read_write_checked in
(*  print_pairs_list threads_checked;*)
(*  F.printf "threads_intersection_checked:\n";*)
  let threads_intersection_checked = List.filter ~f:AccessEvent.predicate_threads_intersection threads_checked in
(*  print_pairs_list threads_intersection_checked;*)
(*  F.printf "locksets_checked:\n";*)
  let locksets_checked = List.filter ~f:AccessEvent.predicate_locksets threads_intersection_checked in
  F.printf "pairs with data races:\n";
  _print_pairs_list locksets_checked;
  let has_data_race = List.length locksets_checked in
  if phys_equal has_data_race 0 then
    F.printf "\nTHERE IS NO DATA RACE.\n"
  else
    F.printf "\nTHERE IS A DATA RACE.\n"  

let astate_with_clear_load_aliases astate =
  (*F.printf "load_aliases before clear: \n";*)
  (*_print_load_aliases_list astate;*)
  {astate with load_aliases=[]}

let find_in_list var locals =
  let rec go lst =
    match lst with
    | [] -> None
    | h :: t ->
      if (HilExp.AccessExpression.equal var h) then Some h else go t
  in go locals

let go_through_accesses_and_remove_locals summary =
  F.printf "locals:\n";
  print_locals summary;
  let list_of_accesses = AccessSet.elements summary.accesses in
  let rec go accesses_to_be_checked _locals new_accesses =
    match accesses_to_be_checked with
    | [] -> new_accesses
    | access :: t -> (
      let var = AccessEvent.get_var access in
      let var_base = HilExp.AccessExpression.get_base var in
      let var_base_ae = HilExp.AccessExpression.base var_base in
(*      let (found : bool) = List.member var new_accesses in*)
(*      F.printf "found: %b\n" found;*)
      F.printf "var: %a\n" HilExp.AccessExpression.pp (AccessEvent.get_var access);
      F.printf "var_base: %a\n" HilExp.AccessExpression.pp var_base_ae;
      match (find_in_list var_base_ae _locals) with
      | None -> go t _locals (access :: new_accesses)
      | Some _ -> go t _locals new_accesses
(*      if (HilExp.AccessExpression.equal var )*)
      (* check if any local is equal to var *)
    )
(*    if (AccessSet.equal accesses_to_be_checked AccessSet.empty) then *)
(*      begin *)
(*        new_accesses *)
(*      end  *)
(*    else *)
(*      begin *)
(*        (* jeste tam neco je v tech accesses *)*)
(*      end*)
  in
  let new_accesses_list = go list_of_accesses summary.locals [] in
  (* list to AccessSet *)
  let new_accesses_set = AccessSet.of_list new_accesses_list in
  F.printf "new_accesses_after_remove:\n";
  print_accesses new_accesses_set;
  new_accesses_set

let remove_local_accesses summary_option =
  F.printf "remove_local_accesses --- \n";
  match summary_option with
  | None -> None
  | Some summary -> (
    (*  *)
    let accesses_without_locals = go_through_accesses_and_remove_locals summary in
    Some {summary with accesses=accesses_without_locals}
  )

let add_heap_aliases_to_astate astate heap_aliases =
  let heap_aliases_joined = astate.heap_aliases @ heap_aliases in
  {astate with heap_aliases=heap_aliases_joined}