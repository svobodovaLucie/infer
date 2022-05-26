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

module AccessEvent = struct
  (* type t =
    AccessPath.t * Location.t *)
  type t =
  {
    var: AccessPath.t;
    loc: Location.t;
    (* access_wr: Boolean.t; *)
    locked: Lockset.t;
    unlocked: Lockset.t
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
  let compare _t1 _t2 = 0

  let _equal lock lock' = Int.equal 0 (compare lock lock')

  (* let _hash (lock, _) = Hashtbl.hash lock *)
  let _hash t1 = Hashtbl.hash t1.loc

  (*
  let pp fmt ((((_,_), _) as access), loc) =
    F.fprintf fmt "access %a on %a" AccessPath.pp access Location.pp loc;
  *)
  let pp fmt t1 =
    F.fprintf fmt "var %a on %a" AccessPath.pp t1.var Location.pp t1.loc;
end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

type t =
{
  accesses: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  unlockset: Lockset.t
}

let empty =
{
  accesses = AccessSet.empty;
  lockset = Lockset.empty;
  unlockset = Lockset.empty
}

let acquire lockid astate loc pname =
  F.printf "acquire: pname = %a in Darc\n" Procname.pp pname;
  let lock : LockEvent.t = (lockid, loc) in
  let new_astate : t =
    let lockset =
      Lockset.add lock astate.lockset
    in
    { astate with lockset }
  in
  new_astate

let release _lockid astate _loc pname =
  F.printf "release: pname = %a in Darc\n" Procname.pp pname;
  let new_astate : t =
    let lockset =
      astate.lockset
    in
    { astate with lockset }
  in
  new_astate

(* FIXME var is any expreasion now (n$7 etc.) *)
let assign_expr var astate loc =
  F.printf "Inside assign_expr in Domain\n";
  let new_access : AccessEvent.t =
    let locked = Lockset.empty in
    let unlocked = Lockset.empty in
    { var; loc; locked; unlocked; }
  in
  let accesses = AccessSet.add new_access astate.accesses in
  {astate with accesses;}

let _join astate1 astate2 =
  let new_astate : t =
    let accesses : AccessSet.t = AccessSet.union astate1.accesses astate2.accesses in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
    { accesses; lockset; unlockset }
  in
  new_astate

let integrate_summary astate callee_pname loc _callee_summary _callee_formals _actuals caller_pname =
  F.printf "===================\n";
  F.printf "access=%a in Darc\n" AccessSet.pp astate.accesses;
  F.printf "loc=%a in Darc\n" Location.pp loc;
  F.printf "lockset=%a in Darc\n" Lockset.pp astate.lockset;
  F.printf "unlockset=%a in Darc\n" Lockset.pp astate.unlockset;
  F.printf "callee_pname=%a in Darc\n" Procname.pp callee_pname;
  F.printf "caller_pname=%a in Darc\n" Procname.pp caller_pname;
  F.printf "===================\n";

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
    let accesses = AccessSet.union astate1.accesses astate2.accesses in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let unlockset = Lockset.union astate1.unlockset astate2.unlockset in
    { accesses; lockset; unlockset }
  in
  new_astate

let widen ~prev ~next ~num_iters:_ =
  join prev next

let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "accesses=%a\n" AccessSet.pp astate.accesses;
    F.fprintf fmt "lockset=%a\n" Lockset.pp astate.lockset;
    F.fprintf fmt "unlockset=%a\n" Lockset.pp astate.unlockset;

type summary = t