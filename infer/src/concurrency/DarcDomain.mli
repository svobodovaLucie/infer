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
  (* type of ReadWriteModels *)
  type t = Read | Write

  (* function returns access type as a string *)
  val access_to_string : t -> string
end

module ThreadEvent : sig
  (* type of ThreadEvent *)
  type t
end

module PointsTo : sig
  (* type of PointsTo *)
  type t
end

module Locals : sig
  type t
end

module LocalsSet : sig
  type t

  val empty : t
end

module AccessEvent : sig
  (* type of AccessEvent *)
  type t

  (* function returns line of code of an access *)
  val get_loc : t -> Location.t

  (* pretty print function used for reporting *)
  val pp_report_long : Format.formatter -> t -> unit
end

val update_aliases : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> t -> t

val empty : t

(*val empty_with_locals : (Mangled.t * Typ.t) list -> t*)
val empty_with_locals : LocalsSet.t -> t

(*val initial_main : (Mangled.t * Typ.t) list -> t*)
val initial_main : LocalsSet.t -> t

val acquire_lock : HilExp.t -> t -> Location.t -> t

val release_lock : HilExp.t -> t -> Location.t -> t

val transform_sil_expr_to_hil : Exp.t -> Typ.t -> bool -> HilExp.t

val transform_sil_exprs_to_hil_list : (Exp.t * Typ.t) list -> bool -> HilExp.t list

val add_access_with_heap_alias_when_malloc : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Location.t -> t -> (HilExp.AccessExpression.t * Location.t) list -> Procname.t -> (t * (HilExp.AccessExpression.t * Location.t) list)

val load : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Exp.t -> Typ.t -> Location.t -> t -> Procname.t -> t

val store : Exp.t -> Typ.t -> Exp.t -> Location.t -> t -> Procname.t -> t

val new_thread : HilExp.AccessExpression.t -> Location.t -> t -> ThreadEvent.t

val add_thread : ThreadEvent.t -> t -> t

val remove_thread : HilExp.AccessExpression.t -> t -> t

val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

val integrate_pthread_summary : t -> ThreadEvent.t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> (Exp.t * Typ.t) -> Procname.t -> t

val print_astate : t (* -> Location.t -> Procname.t *) -> unit

type summary = t

val compute_data_races : summary -> (AccessEvent.t * AccessEvent.t) list

val astate_with_clear_load_aliases : t -> int -> t

val add_heap_aliases_to_astate : t -> (HilExp.AccessExpression.t * Location.t) list -> t

val add_var_to_locals : HilExp.AccessExpression.t -> LocalsSet.t -> LocalsSet.t
