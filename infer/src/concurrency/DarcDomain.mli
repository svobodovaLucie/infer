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

val assign_expr : AccessPath.t -> t -> Location.t -> t

val add_thread : Thread.t -> t -> t

val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

type summary = t