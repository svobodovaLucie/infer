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
    | Read  -> "read"
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
  load_aliases: (HilExp.AccessExpression.t * HilExp.AccessExpression.t * Exp.t) list;
  locals: (Mangled.t * Typ.t) list; (* TODO maybe use HilExp.AccessExpression.t? *)
}

let empty =
{
  threads_active = ThreadSet.empty;
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty;
  aliases = AliasesSet.empty;
  load_aliases = [];
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
      | HilExp.AccessExpression.Dereference _ -> (
        let alias = find_alias lhs aliases in (* e.g. None | Some (y, &k) *)
        match alias with
        | Some alias -> Some alias   (* return alias *)
        | None -> Some (var, var)    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
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

let replace_var_with_aliases_without_address_of var aliases = (* if alias is not found, var is returned *)
  let var_base = HilExp.AccessExpression.get_base var in
  let var_ae = HilExp.AccessExpression.base var_base in
  let result_option = check_lhs_without_address_of var var_ae var_ae aliases in
  match result_option with
  | None -> var
  | Some (_, snd) -> snd

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
F.printf "aliases: %a\n" AliasesSet.pp astate.aliases;
F.printf "alias to be removed: \n";
_print_alias lhs_alias;
 let astate_alias_removed = remove_alias_from_aliases lhs_alias astate in (* astate *)
 F.printf "aliases_removed: %a\n" AliasesSet.pp astate_alias_removed.aliases;
 F.printf "final_astate:\n";
 let final_astate = add_new_alias_no_option astate_alias_removed new_alias in (* astate *)
 F.printf "final_astate: %a\n" AliasesSet.pp final_astate.aliases;
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

let initial_main locals =
  (* create main thread *)
  let main_thread = create_main_thread in
  (* add the main thread to an empty astate *)
  (* let initial_astate = empty in *)
  let initial_astate = empty_with_locals locals in
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
          let alias = find_mem_alias var aliases in (* e.g. None | Some (y, &k) *)
          (* TODO rekurze!!! *)
          match alias with
          | Some (_, snd) -> snd   (* return alias *)
          | None -> var    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
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
  let exp_base = HilExp.AccessExpression.get_base exp in
  let exp_base_ae = HilExp.AccessExpression.base exp_base in
    let (* rec *) check_lhs lhs lhs_current var aliases =
      F.printf "-----------------mem_aliased:check_lhs:------------------\n";
          F.printf "mem_aliased:check_lhs: lhs=%a, lhs_current=%a, var=%a\n" HilExp.AccessExpression.pp lhs HilExp.AccessExpression.pp lhs_current HilExp.AccessExpression.pp var;
          let alias = find_mem_alias var aliases in (* e.g. None | Some (y, &k) *)
          (* TODO rekurze!!! *)
          match alias with
          | Some (_, snd) -> HilExp.AccessExpression.dereference snd   (* return alias *)
          | None -> var    (* the var is not in aliases -> return var (only the second variable will be needed later) *)
      in
      let res = check_lhs exp exp_base_ae exp_base_ae mem_aliased in
      F.printf "exp: %a, res: %a\n" HilExp.AccessExpression.pp exp HilExp.AccessExpression.pp res;
      match exp with
      | HilExp.AccessExpression.Dereference _ -> HilExp.AccessExpression.dereference res
      | _ -> res

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
  let e_to_add =
  match e with
  | Exp.Var _ -> (
    F.printf "Var\n";
    (* DEALIASING *)
    (* find e in load_aliases jako fst -> return snd -> ale rekurzivne!!! *)
      let e_aliased = fst_aliasing_snd e_ae astate.load_aliases in
      F.printf "e_aliased: %a\n" HilExp.AccessExpression.pp e_aliased;
      (* find e_alised in aliases *)
      F.printf "aliases=%a\n" AliasesSet.pp astate.aliases;
      let e_aliased_final = replace_var_with_aliases_without_address_of e_aliased (AliasesSet.elements astate.aliases) in
      F.printf "e_aliased_final: %a\n" HilExp.AccessExpression.pp e_aliased_final;
      (* save alias to the load_aliases set *)
      e_aliased_final
  )
  | Exp.Lvar _ | Exp.Lfield _ | Exp.Lindex _ -> (
    F.printf "Lvar or Lfield or Lindex\n";
    e_ae
  )
  | _ -> (
    F.printf "other e, nemelo by nastat\n";
    e_ae
  )
  in
  let new_mem_alias = (id_ae, e_to_add, e) in
  let load_aliases = new_mem_alias :: astate.load_aliases in
  let astate = { astate with load_aliases } in
  F.printf "load_aliases after:\n";
  _print_load_aliases_list astate;
  (* add read access *)
  let astate_with_new_read_access = add_access_to_astate e_to_add ReadWriteModels.Read astate loc in
  astate_with_new_read_access

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
      (* save alias to the load_aliases set *)
      let astate = add_access_to_astate e1_aliased_final ReadWriteModels.Write astate loc in
      if (Typ.is_pointer typ) then (* TODO pridat alias, pokud typ je pointer *)
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
            let add_deref =
              match (var : Var.t) with
              | LogicalVar _ -> (F.printf "%a je LogicalVar -> true\n" Var.pp var; true)
              | ProgramVar _ -> (F.printf "%a je ProgramVar -> false\n" Var.pp var; false)
            in
            add_deref
          )
          | _ -> (
            F.printf "other -> add_deref=false\n";
            false (* TODO right? *)
          )
        in
        let e2_hil = transform_sil_expr_to_hil e2 typ add_deref in
        F.printf "\n";
        match e2_hil with
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
              e2_ae
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
    (* | hd :: tl -> F.printf "%a, " HilExp.AccessExpression.pp hd; print_vars tl *)
    | hd :: tl ->
      let typ_string = Typ.to_string (snd hd) in
      F.printf "|(%a, %s)|" Mangled.pp (fst hd) typ_string; print_vars tl
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

let integrate_pthread_summary astate thread callee_pname _loc callee_summary _callee_formals _actuals _caller_pname =
  F.printf "integrate_pthread_summary: callee_pname=%a\n" Procname.pp callee_pname;
  F.printf "summary before --------";
  print_astate astate (* loc caller_pname *);
  (* edit information about each access - thread, threads_aactive, lockset, unlockset *)
  let edited_accesses_from_callee = AccessSet.map (AccessEvent.edit_accesses astate.threads_active astate.lockset astate.unlockset thread) callee_summary.accesses in
  let accesses_joined = AccessSet.join astate.accesses edited_accesses_from_callee in
  { astate with accesses=accesses_joined }

let _print_actuals actuals =
  F.printf "print_actuals: \n";
  let rec loop = function
    | [] -> F.printf "\n"
    | hd :: tl -> F.printf "| %a |" HilExp.pp hd; loop tl
  in loop actuals

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
           | Some opt -> opt
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
    let load_aliases = astate1.load_aliases @ astate2.load_aliases in (* TODO fix and check *)
    let locals = [] in (* TODO *)
    { threads_active; accesses; lockset; unlockset; aliases; load_aliases; locals }
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
(*  print_pairs_list locksets_checked;*)
  let has_data_race = List.length locksets_checked in
  if phys_equal has_data_race 0 then
    F.printf "\nTHERE IS NO DATA RACE.\n"
  else
    F.printf "\nTHERE IS A DATA RACE.\n"  
