(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)
 (* Data Race Checker Domain *)

open! IStd

include AbstractDomain.S
module LockEvent = DeadlockDomain.LockEvent
module Lockset = DeadlockDomain.Lockset

val empty : t

val acquire : AccessPath.t -> t -> Location.t -> Procname.t -> t

val release : AccessPath.t -> t -> Location.t -> Procname.t -> t

(* val assign_expr : HilExp.AccessExpression.t -> t -> Location.t -> t *)
(* val assign_expr : HilExp.access_expression -> t -> Location.t -> t *)
val assign_expr : AccessPath.t -> t -> Location.t -> t

val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t
(*
val inc : t -> t
*)
type summary = t


(* type astate = t

val has_printf : t -> bool

val apply_summary : summary : t -> t -> t

type summary = t
*)
