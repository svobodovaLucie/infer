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

module ReadWriteModels : sig
  type t = 
    | Read
    | Write

  val has_effect : String.t -> bool

  val get_read_write_effect : string -> int -> (int * t) list

  val access_to_string : t -> string

end

module ThreadEvent : sig
  type t = (AccessPath.t * Location.t)
end

module Aliases : sig
  type t = (HilExp.AccessExpression.t * HilExp.AccessExpression.t)
end

val update_aliases : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> t -> t

val empty : t

val empty_with_vars : (Mangled.t * Typ.t) list -> t

val initial_main : (Mangled.t * Typ.t) list -> t

val acquire : AccessPath.t -> t -> Location.t -> Procname.t -> t

val release : AccessPath.t -> t -> Location.t -> Procname.t -> t

val assign_expr : HilExp.AccessExpression.t -> t -> Location.t -> Procname.t -> t

val add_access_to_astate : HilExp.AccessExpression.t -> ReadWriteModels.t -> t -> Location.t -> Procname.t -> t

val add_thread : ThreadEvent.t option -> t -> t

val remove_thread : ThreadEvent.t option -> t -> t

val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

val integrate_pthread_summary : t -> ThreadEvent.t option-> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

val print_astate : t -> Location.t -> Procname.t -> unit

type summary = t

val compute_data_races : summary -> unit