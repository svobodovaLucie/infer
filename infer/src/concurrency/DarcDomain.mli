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

val empty_with_locals : (Mangled.t * Typ.t) list -> t

val initial_main : (Mangled.t * Typ.t) list -> t

val acquire : AccessPath.t -> t -> Location.t -> Procname.t -> t

val release : AccessPath.t -> t -> Location.t -> Procname.t -> t

val assign_expr : HilExp.AccessExpression.t -> t -> Location.t -> Procname.t -> ReadWriteModels.t -> t

(* val store : HilExp.AccessExpression.t -> t -> Location.t -> Procname.t -> ReadWriteModels.t -> t *)

val transform_sil_expr_to_hil : Exp.t -> Typ.t -> bool -> HilExp.t

val transform_sil_exprs_to_hil_list : (Exp.t * Typ.t) list -> bool -> HilExp.t list

(*val load : Ident.t -> Exp.t -> Typ.t -> Location.t -> t -> t*)

val add_heap_alias_when_malloc : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Location.t -> t -> (HilExp.AccessExpression.t * Location.t) list -> (t * (HilExp.AccessExpression.t * Location.t) list)

val load : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Exp.t -> Typ.t -> Location.t -> t -> t

val store_with_alias : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Location.t -> t -> t

val store_vol2 : Exp.t -> Typ.t -> Exp.t -> Location.t -> t -> Procname.t -> t

val store_with_heap_alloc : Exp.t -> Typ.t -> Exp.t -> Location.t -> t -> Procname.t -> (HilExp.AccessExpression.t * Location.t) list -> t

val store : HilExp.AccessExpression.t -> Location.t -> t -> t

val _add_rhs_expr_to_accesses : HilExp.AccessExpression.t -> t -> Location.t -> Procname.t -> t

val add_access_to_astate : HilExp.AccessExpression.t -> ReadWriteModels.t -> t -> Location.t (* -> Procname.t *) -> t

val add_thread : ThreadEvent.t option -> t -> t

val remove_thread : ThreadEvent.t option -> t -> t

val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

val integrate_pthread_summary : t -> ThreadEvent.t option-> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list -> Procname.t -> t

val print_astate : t (* -> Location.t -> Procname.t *) -> unit

type summary = t

val compute_data_races : summary -> unit

val astate_with_clear_load_aliases : t -> t