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
  type t =
    AccessPath.t * Location.t

  let compare (((base, aclist) as lock), _) ((((base'), aclist') as lock' ), _) =
    if phys_equal lock lock' then 0
    else begin
      let res = AccessPath.compare_base base base' in
      if not (Int.equal res 0) then res
      else
        List.compare AccessPath.compare_access aclist aclist'
    end

  let _equal lock lock' = Int.equal 0 (compare lock lock')

  let _hash (lock, _) = Hashtbl.hash lock

  let pp fmt ((((_,_), _) as access), loc) =
    F.fprintf fmt "access %a on %a" AccessPath.pp access Location.pp loc;
end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)

type t =
{
  sth: AccessSet.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  some_int: int  (* experiment *)
}

let empty =
{
  sth = AccessSet.empty;
  lockset = Lockset.empty;
  some_int = 0
}

let acquire lockid astate loc pname =
  F.printf "acquire: pname = %a in Darc\n" Procname.pp pname;
  let lock : LockEvent.t = (lockid, loc) in
  let new_astate : t =
    let lockset =
      Lockset.add lock astate.lockset
    in
    let some_int = astate.some_int + 1
    in
    { astate with lockset; some_int }
  in
  new_astate

let release _lockid astate _loc pname =
  F.printf "release: pname = %a in Darc\n" Procname.pp pname;
  let new_astate : t =
    let lockset =
      astate.lockset
    in
    let some_int = astate.some_int + 1
    in
    { astate with lockset; some_int }
  in
  new_astate

let assign_expr expr astate loc =
  F.printf "Inside assign_expr in Domain\n";
  let blah = AccessSet.add (expr, loc) astate.sth in
  {astate with sth = blah;}

let join astate1 astate2 =
  let new_astate : t =
    let sth = AccessSet.union astate1.sth astate2.sth in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let some_int = astate1.some_int + astate2.some_int in
    { sth; lockset; some_int }
  in
  new_astate

let integrate_summary astate callee_pname loc callee_summary callee_formals actuals caller_pname =
  F.printf "===================\n";
  F.printf "access=%a in Darc\n" AccessSet.pp astate.sth;
  F.printf "loc=%a in Darc\n" Location.pp loc;
  F.printf "lockset=%a in Darc\n" Lockset.pp astate.lockset;
  F.printf "callee_pname=%a in Darc\n" Procname.pp callee_pname;
  F.printf "caller_pname=%a in Darc\n" Procname.pp caller_pname;
  F.printf "===================\n";


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

let ( <= ) ~lhs ~rhs =
  Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset &&
  lhs.some_int <= rhs.some_int

let leq ~lhs ~rhs = (<=) ~lhs ~rhs

let join astate1 astate2 =
  let new_astate : t =
    let sth = AccessSet.union astate1.sth astate2.sth in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let some_int = astate1.some_int + astate2.some_int in
    { sth; (* access; *) lockset; some_int }
  in
  new_astate

let widen ~prev ~next ~num_iters:_ =
  join prev next

let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "sth=%a\n" AccessSet.pp astate.sth;
    F.fprintf fmt "lockset=%a\n" Lockset.pp astate.lockset;
    F.fprintf fmt "some_int=%d\n" astate.some_int;

type summary = t