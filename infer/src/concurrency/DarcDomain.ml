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

(*
module AccessType = struct
  type t =
    | Read of {exp: AccessExpression.t}
    | Write of {exp: AccessExpression.t}
    (* maybe add another later *)

  let pp fmt = function
    | Read {exp} ->
        F.fprintf fmt "Read of %a" AccessExpression.pp exp
    | Write {exp} ->
        F.fprintf fmt "Write to %a" AccessExpression.pp exp
    | _ -> F.printf "Another type of access\n"

end
*)

module Accesses = AbstractDomain.FiniteSet(HilExp.AccessExpression)

(*
module AccessEvent = struct
  (* type as n-tuple or set with names? *)
  type t =
  {
    access_path: Accesses.t;
    loc: Location.t
     (* * type, locks, locks_un, threads_active, thread *)
  }

  let pp fmt ((((_,_), _) as access), loc) =
    F.fprintf fmt "access %a on %a" AccessPath.pp access Location.pp loc;
end

module AccessSet = AbstractDomain.FiniteSet(AccessEvent)
*)
(* module Accesses = AbstractDomain.FiniteSet(HilExp.AccessExpression) *)

type t =
{
  access: Accesses.t;
  lockset: Lockset.t;  (* Lockset from Deadlock.ml *)
  some_int: int  (* experiment *)
}

let empty =
{
  access = Accesses.empty; (*HilExp.AccessExpression.bottom; *)
  lockset = Lockset.empty;
  some_int = 0
}

(* let acquire lockid astate loc _extras pname = *)
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
  (* let lock : LockEvent.t = (lockid, loc) in *)
  let new_astate : t =
    let lockset =
      (* Lockset.remove lock astate.lockset *)
      astate.lockset
    in
    let some_int = astate.some_int + 1
    in
    { astate with lockset; some_int }
  in
  new_astate
(*
let inc astate =
  {astate.lockset; astate.some_int + 1}
*)
(* let integrate_summary astate _callee_pname _loc _callee_summary _callee_formals _actuals _caller_pname = *)

let assign_expr expr astate _loc =
  F.printf "Inside assign_expr in Domain\n";
  let var = Accesses.add expr astate.access in
  {astate with access = var;}

let integrate_summary astate callee_pname caller_pname =
  F.printf "lockset=%a in Darc\n" Lockset.pp astate.lockset;
  F.printf "callee_pname=%a in Darc\n" Procname.pp callee_pname;
  F.printf "caller_pname=%a in Darc\n" Procname.pp caller_pname;
  astate

  (* replace formals with actuals...
  let formal_to_access_path : Mangled.t * Typ.t -> AccessPath.t = fun (name, typ) ->
    let pvar = Pvar.mk name callee_pname in
    AccessPath.base_of_pvar pvar typ, []
  in
  ...*)
  (*
  new_astate : t =

    let lockset = Lockset.fold (fun elem acc ->
      Lockset.add elem acc
    ) callee_summary.lockset astate.lockset
    in
    let some_int = callee_summary.some_int + astate.some_int
    in
    (* let lockset = summary_lockset in
    let some_int = *)
  in
  new_astate
  *)

let ( <= ) ~lhs ~rhs =
  Lockset.leq ~lhs:lhs.lockset ~rhs:rhs.lockset &&
  lhs.some_int <= rhs.some_int

let leq ~lhs ~rhs = (<=) ~lhs ~rhs

let join astate1 astate2 =
  let new_astate : t =
    let access = Accesses.union astate1.access astate2.access in
    let lockset = Lockset.union astate1.lockset astate2.lockset in
    let some_int = astate1.some_int + astate2.some_int in
    { access; lockset; some_int }
  in
  new_astate

let widen ~prev ~next ~num_iters:_ =
  join prev next

let pp : F.formatter -> t -> unit =
  fun fmt astate ->
    F.fprintf fmt "access=%a\n" Accesses.pp astate.access;
    F.fprintf fmt "lockset=%a\n" Lockset.pp astate.lockset;
    F.fprintf fmt "some_int=%d\n" astate.some_int;

type summary = t

(*
module LockEvent = struct
  type t = AccessPath.t * Location.t

  (* compare (AccessPath.t * Location.t) (AccessPath.t * Location.t) *)
  (* AccessPath.t = base * access list *)
  let compare (((base, aclist) as lock), _) ((((base'), aclist') as lock' ), _) =
    if phys_equal lock lock' then 0
    else begin
      let res = AccessPath.compare_base base base' in
      if not (Int.equal res 0) then res
      else
        List.compare AccessPath.compare_access aclist aclist'
    end

  let equal lock lock' = Int.equal 0 (compare lock lock')

  let hash (lock, _) = Hashtbl.hash lock

  let pp fmt ((((_,_), _) as lock), loc) =
    F.fprintf fmt "lock %a on %a in Darc Checker" AccessPath.pp lock Location.pp loc;
end
*)



(* module FiniteBounds = struct
    type t = int

    let leq ~lhs ~rhs = lhs <= rhs

    let join a b = Stdlib.max a b

    let widen ~prev ~next ~num_iters:_ = join prev next

    let pp fmt astate = F.fprintf fmt "%d" astate
end *)

(*
module BoundsWithTop = struct
    open AbstractDomain.Types
    include AbstractDomain.TopLifted (FiniteBounds)

    let widening_threshold = 5

    let widen ~prev ~next ~num_iters =
        match (prev, next) with
        | Top, _ | _, Top ->
            Top
        | NonTop prev, NonTop next when num_iters < widening_threshold ->
            NonTop (FiniteBounds.join prev next)
        | NonTop _, NonTop _ ->
            Top
end

module ReturnsPrintf = AbstractDomain.BooleanOr
include AbstractDomain.Pair (BoundsWithTop) (ReturnsPrintf)
open AbstractDomain.Types

(* let inc fc = fc + 1 *)
let inc = function
    | (Top, _) as astate ->
        astate
    | NonTop num, has_printf ->
        (NonTop (num + 1), has_printf)

let initial = (NonTop 0, false)

let has_printf = function
    | Top, _ ->
        true
    | NonTop x, _ when x > 0 ->
        true
    | NonTop _, _ ->
        false

let apply_summary ~summary:(summary_count, summary_has_printf) (current_count, current_has_printf) =
    let new_count =
        match current_count with
        | Top ->
            Top
        | NonTop current_count ->
            let return_count = if summary_has_printf then 1 else 0 in
            let summary_count =
                match summary_count with Top -> 0 | NonTop count -> count
            in
            NonTop (summary_count + current_count + return_count)
        in
        (new_count, current_has_printf)



type astate = t

type summary = t
*)