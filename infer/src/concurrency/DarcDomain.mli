(*
 * Author: Lucie Svobodová (xsvobo1x@stud.fit.vutbr.cz), 2022-present
 * Automated Analysis and Verification Research Group (VeriFIT)
 * Faculty of Information Technology, Brno University of Technology, CZ
 *)
 (* Data Race Checker Domain *)

open! IStd
include AbstractDomain.S
module LockEvent = DeadlockDomain.LockEvent
module Lockset = DeadlockDomain.Lockset

(* module used for handling threads *)
module ThreadEvent : sig
  (* type of ThreadEvent *)
  type t
end

(* module used for handling local variables *)
module LocalsSet : sig
  (* type of Locals *)
  type t

  (* empty set of locals *)
  val empty : t
end

(* module defining the types of accesses *)
module ReadWriteModels : sig
  (* type of ReadWriteModels *)
  type t = Read | Write

  (* function returns access type as a string *)
  val access_to_string : t -> string
end

(* module used for dealing with accesses *)
module AccessEvent : sig
  (* type of AccessEvent *)
  type t

  (* function returns line of code of an access *)
  val get_loc : t -> Location.t

  (* pretty print function used for reporting - short version *)
  val pp_report_short : Format.formatter -> t -> unit

  (* pretty print function used for reporting - long version (with threads and locks) *)
  val pp_report_long : Format.formatter -> t -> unit
end

(* the type of a DarC summary *)
type summary = t

(* empty type t with locals *)
val empty_with_locals : LocalsSet.t -> t

(* function returns empty astate with main thread in threads_active and locals *)
val initial_main : LocalsSet.t -> t

(* function prints the current abstract state *)
val print_astate : t -> unit

(* function adds a lock to the lockset and removes it from the unlockset *)
val acquire_lock : HilExp.t -> t -> Location.t -> t

(* function removes a lock from the lockset and adds it to the unlockset *)
val release_lock : HilExp.t -> t -> Location.t -> t

(* function transforms a SIL expression to the HIL expression *)
val transform_sil_expr_to_hil : Exp.t -> Typ.t -> bool -> HilExp.t

(* function transforms list of SIL expressions to HIL expressions *)
val transform_sil_exprs_to_hil_list : (Exp.t * Typ.t) list -> bool -> HilExp.t list

(* function adds new access to astate and updates the list of tmp_heap used when dynamically allocating memory *)
val add_access_with_heap_alias_when_malloc : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Location.t ->
  t -> (HilExp.AccessExpression.t * Location.t) list -> Procname.t -> (t *(HilExp.AccessExpression.t * Location.t) list)

(* function handles the LOAD instruction *)
val load : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> Exp.t -> Typ.t -> Location.t -> t -> Procname.t ->t

(* function handles the STORE instruction *)
val store : Exp.t -> Typ.t -> Exp.t -> Location.t -> t -> Procname.t -> t

(* function creates new thread from its load alias *)
val new_thread : HilExp.AccessExpression.t -> Location.t -> t -> ThreadEvent.t

(* function adds a thread to the current abstract state *)
val add_thread : ThreadEvent.t -> t -> t

(* function removes a thread from the current abstract state *)
val remove_thread : HilExp.AccessExpression.t -> t -> t

(* function integrates summary of callee to the current abstract state when function call occurs,
   it replaces all accesses to formals in callee_summary to accesses to actuals, and joins the
   callee summary with the current abstract state *)
val integrate_summary : t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list -> HilExp.t list ->
                                                                                                         Procname.t -> t

(* function integrates summary of callee to the current astate when function call to pthread_create() occurs,
   it replaces all accesses to formal in callee_summary to accesses to actual, joins the callee summary
   with the current abstract state, and creates a new active thread *)
val integrate_pthread_summary : t -> ThreadEvent.t -> Procname.t -> Location.t -> t -> (Mangled.t * IR.Typ.t) list ->
                                                                                                      HilExp.t list -> t

(* function checks if there are any data races in the program
   by creating pairs of accesses and checking on which pairs data race could occur *)
val compute_data_races : summary -> (AccessEvent.t * AccessEvent.t) list

(* function deletes load_aliases from astate *)
val astate_with_clear_load_aliases : t -> int -> t

(* function updates points-to and heap points-to relations *)
val update_aliases : HilExp.AccessExpression.t -> HilExp.AccessExpression.t -> t -> weak_update:bool -> t

(* functions joins astate.heap_points_to with heap_aliases *)
val add_heap_aliases_to_astate : t -> (HilExp.AccessExpression.t * Location.t * bool) list -> t

(* function adds a variable var to the set of locals *)
val add_var_to_locals : HilExp.AccessExpression.t -> LocalsSet.t -> LocalsSet.t
