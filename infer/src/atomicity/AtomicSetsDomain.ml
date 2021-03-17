(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
open AtomicityUtils
module F = Format
module Set = Caml.Set

(** Detection of atomic sets domain implementation. *)

(* ************************************ Types *************************************************** *)

(** A pair of sets of calls. Calls without a lock followed by calls with a lock. *)
type callsPair = SSet.t * SSet.t [@@deriving compare, equal]

(** A pair of sets of calls with a lock. *)
type callsPairLock = callsPair * Lock.t [@@deriving compare, equal]

(* ************************************ Modules ************************************************* *)

(** A set of pairs of sets of calls. *)
module CallsPairSet = Set.Make (struct
  type t = callsPair [@@deriving compare, equal]
end)

(** A set of sets of strings. *)
module SSSet = Set.Make (SSet)

(** A set of pairs of sets of calls with locks. *)
module CallsPairLockSet = Set.Make (struct
  type t = callsPairLock [@@deriving compare, equal]
end)

(* ************************************ Astate ************************************************** *)

(** An element of an abstract state. *)
type tElement =
  { calls: SSet.t
  ; callsPairs: CallsPairLockSet.t
  ; finalCallsPairs: CallsPairSet.t
  ; allOccurrences: SSet.t list
  ; guards: Guards.t }
[@@deriving compare, equal]

(** A set of types tElement is an abstract state. *)
module TSet = Set.Make (struct
  type t = tElement [@@deriving compare, equal]
end)

type t = TSet.t [@@deriving compare, equal]

type astate = t [@@deriving compare, equal]

let initial : t =
  assert_user
    (Config.atomic_sets_widen_limit > 0)
    "Input argument '--atomic-sets-widen-limit' should be greater than 0, %d given."
    Config.atomic_sets_widen_limit ;
  assert_user
    (Config.atomic_sets_locked_functions_limit > 0)
    "Input argument '--atomic-sets-locked-functions-limit' should be greater than 0, %d given."
    Config.atomic_sets_locked_functions_limit ;
  assert_user
    (Config.atomic_sets_functions_depth_limit >= 0)
    "Input argument '--atomic-sets-functions-depth-limit' should be greater than or equal to 0, %d \
     given."
    Config.atomic_sets_functions_depth_limit ;
  (* An initial abstract state is a set with a single empty element. *)
  TSet.singleton
    { calls= SSet.empty
    ; callsPairs= CallsPairLockSet.empty
    ; finalCallsPairs= CallsPairSet.empty
    ; allOccurrences= [SSet.empty]
    ; guards= Guards.empty }


let pp (fmt : F.formatter) (astate : t) : unit =
  F.pp_print_string fmt "\n" ;
  let iterator (astateEl : tElement) : unit =
    F.pp_print_string fmt "{\n" ;
    (* calls *)
    F.fprintf fmt "\t{%s};\n" (String.concat (SSet.elements astateEl.calls) ~sep:", ") ;
    (* callsPairs *)
    F.pp_print_string fmt "\t" ;
    let lastCallsPair : callsPairLock option = CallsPairLockSet.max_elt_opt astateEl.callsPairs in
    let print_calls_pair (((pFst, pSnd), lock) as callsPair : callsPairLock) : unit =
      let withoutLock : string = String.concat (SSet.elements pFst) ~sep:", "
      and withLock : string = String.concat (SSet.elements pSnd) ~sep:", " in
      F.fprintf fmt "%a{%s} ( {%s} )" Lock.pp lock withoutLock withLock ;
      if not (equal_callsPairLock callsPair (Option.value_exn lastCallsPair)) then
        F.pp_print_string fmt " | "
    in
    CallsPairLockSet.iter print_calls_pair astateEl.callsPairs ;
    F.pp_print_string fmt ";\n" ;
    (* finalCallsPairs *)
    F.pp_print_string fmt "\t" ;
    let lastFinalCallsPair : callsPair option = CallsPairSet.max_elt_opt astateEl.finalCallsPairs in
    let print_final_calls_pair ((pFst, pSnd) as callsPair : callsPair) : unit =
      let withoutLock : string = String.concat (SSet.elements pFst) ~sep:", "
      and withLock : string = String.concat (SSet.elements pSnd) ~sep:", " in
      F.fprintf fmt "{%s} ( {%s} )" withoutLock withLock ;
      if not (equal_callsPair callsPair (Option.value_exn lastFinalCallsPair)) then
        F.pp_print_string fmt " | "
    in
    CallsPairSet.iter print_final_calls_pair astateEl.finalCallsPairs ;
    F.pp_print_string fmt ";\n" ;
    (* allOccurrences *)
    F.pp_print_string fmt "\t{\n" ;
    let print_all_occurrences (i : int) (allOccurrences : SSet.t) : unit =
      F.fprintf fmt "\t\t%i: {%s};\n" i (String.concat (SSet.elements allOccurrences) ~sep:", ")
    in
    List.iteri astateEl.allOccurrences ~f:print_all_occurrences ;
    F.pp_print_string fmt "\t};\n" ;
    (* guards *)
    F.fprintf fmt "%a" Guards.pp astateEl.guards ;
    F.pp_print_string fmt "}\n"
  in
  TSet.iter iterator astate ;
  F.pp_print_string fmt "\n"


(** Modifies an element of an abstract state after addition of function calls. *)
let update_astate_el_after_calls (astateEl : tElement) : tElement =
  let finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs in
  let callsPairs : CallsPairLockSet.t =
    let filter (((pFst, pSnd), _) : callsPairLock) : bool =
      if SSet.cardinal pSnd > Config.atomic_sets_locked_functions_limit then (
        finalCallsPairs := CallsPairSet.add (pFst, SSet.empty) !finalCallsPairs ;
        false )
      else true
    in
    CallsPairLockSet.filter filter astateEl.callsPairs
  in
  {astateEl with callsPairs; finalCallsPairs= !finalCallsPairs}


let apply_call ~(fName : string) : t -> t =
  let mapper (astateEl : tElement) : tElement =
    let calls : SSet.t = SSet.add fName astateEl.calls
    and callsPairs : CallsPairLockSet.t =
      CallsPairLockSet.map
        (fun (((pFst, pSnd), lock) : callsPairLock) : callsPairLock ->
          ((pFst, SSet.add fName pSnd), lock))
        astateEl.callsPairs
    and allOccurrences : SSet.t list =
      List.mapi astateEl.allOccurrences ~f:(fun (i : int) : (SSet.t -> SSet.t) ->
          if Int.equal i 0 then SSet.add fName else Fn.id)
    in
    (* Update the calls and the calls pairs and the all occurrences. *)
    update_astate_el_after_calls {astateEl with calls; callsPairs; allOccurrences}
  in
  TSet.map mapper


let apply_locks (locksPaths : AccessPath.t list) : t -> t =
  let mapper (astateEl : tElement) : tElement =
    let lockAppended : bool ref = ref false
    and locksPaths : AccessPath.t list = Guards.reveal_locks astateEl.guards locksPaths in
    let callsPairs : CallsPairLockSet.t =
      let fold (callsPairs : CallsPairLockSet.t) (path : AccessPath.t) : CallsPairLockSet.t =
        let found : bool ref = ref false in
        let mapper ((p, lock) as pairLock : callsPairLock) : callsPairLock =
          if AccessPath.equal path (Lock.path lock) then (
            found := true ;
            (p, Lock.lock lock) )
          else pairLock
        in
        let callsPairs : CallsPairLockSet.t = CallsPairLockSet.map mapper callsPairs in
        if !found then callsPairs
        else (
          lockAppended := true ;
          CallsPairLockSet.add ((astateEl.calls, SSet.empty), Lock.create path) callsPairs )
      in
      List.fold locksPaths ~init:astateEl.callsPairs ~f:fold
    and calls : SSet.t = if !lockAppended then SSet.empty else astateEl.calls in
    (* Clear the calls and update the calls pairs. *)
    {astateEl with calls; callsPairs}
  in
  TSet.map mapper


let apply_unlocks (locksPaths : AccessPath.t list) : t -> t =
  let mapper (astateEl : tElement) : tElement =
    let lockRemoved : bool ref = ref false
    and finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs
    and locksPaths : AccessPath.t list = Guards.reveal_locks astateEl.guards locksPaths in
    let callsPairs : CallsPairLockSet.t =
      let mapper ((p, lock) as pairLock : callsPairLock) : callsPairLock =
        if List.mem locksPaths (Lock.path lock) ~equal:AccessPath.equal then (
          let lock : Lock.t = Lock.unlock lock in
          if not (Lock.is_locked lock) then (
            lockRemoved := true ;
            finalCallsPairs := CallsPairSet.add p !finalCallsPairs ) ;
          (p, lock) )
        else pairLock
      in
      let callsPairs : CallsPairLockSet.t = CallsPairLockSet.map mapper astateEl.callsPairs in
      CallsPairLockSet.filter (Fn.compose Lock.is_locked snd) callsPairs
    and calls : SSet.t = if !lockRemoved then SSet.empty else astateEl.calls in
    (* Clear the calls, update the calls pairs and the final calls pairs. *)
    {astateEl with calls; callsPairs; finalCallsPairs= !finalCallsPairs}
  in
  TSet.map mapper


let apply_guard_construct (guardPath : AccessPath.t) (locksPaths : AccessPath.t list)
    ~(acquire : bool) : t -> t =
  let add_guard : t -> t =
    TSet.map (fun (astateEl : tElement) : tElement ->
        {astateEl with guards= Guards.add guardPath locksPaths astateEl.guards})
  in
  if acquire then Fn.compose (apply_locks locksPaths) add_guard else add_guard


let apply_guard_release (guardPath : AccessPath.t) : t -> t =
  TSet.map (fun (astateEl : tElement) : tElement ->
      {astateEl with guards= Guards.remove guardPath astateEl.guards})


let apply_guard_destroy (guardPath : AccessPath.t) : t -> t =
  Fn.compose (apply_guard_release guardPath) (apply_unlocks [guardPath])


let update_at_the_end_of_function : t -> t =
  let mapper (astateEl : tElement) : tElement =
    let finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs in
    CallsPairLockSet.iter
      (fun ((p, _) : callsPairLock) : unit ->
        finalCallsPairs := CallsPairSet.add p !finalCallsPairs)
      astateEl.callsPairs ;
    if not (SSet.is_empty astateEl.calls) then
      finalCallsPairs := CallsPairSet.add (astateEl.calls, SSet.empty) !finalCallsPairs ;
    (* Clear the calls and the calls pairs, and update the final calls pairs. *)
    { astateEl with
      calls= SSet.empty
    ; callsPairs= CallsPairLockSet.empty
    ; finalCallsPairs= !finalCallsPairs }
  in
  TSet.map mapper


(* ************************************ Operators *********************************************** *)

let leq ~(lhs : t) ~(rhs : t) : bool =
  (* The lhs is less or equal to the rhs if lhs is a subset of the rhs. *)
  if phys_equal lhs rhs then true else TSet.subset lhs rhs


let join (astate1 : t) (astate2 : t) : t =
  (* Union of abstract states. *)
  if phys_equal astate1 astate2 then astate1 else TSet.union astate1 astate2


let widen ~(prev : t) ~(next : t) ~(num_iters : int) : t =
  (* Join previous and next abstract states. *)
  if phys_equal prev next then prev
  else if num_iters <= Config.atomic_sets_widen_limit then join prev next
  else prev


(* ************************************ Summary ************************************************* *)

module Summary = struct
  type t = {atomicFunctions: SSSet.t; allOccurrences: SSet.t list} [@@deriving compare, equal]

  let pp (fmt : F.formatter) (summary : t) : unit =
    F.pp_print_string fmt "\n" ;
    (* atomicFunctions *)
    let lastAtomicFunctions : SSet.t option = SSSet.max_elt_opt summary.atomicFunctions in
    let print_atomic_functions (atomicFunctions : SSet.t) : unit =
      F.fprintf fmt "{%s}" (String.concat (SSet.elements atomicFunctions) ~sep:", ") ;
      if not (SSet.equal atomicFunctions (Option.value_exn lastAtomicFunctions)) then
        F.pp_print_char fmt ' '
    in
    F.pp_print_string fmt "atomicFunctions: " ;
    SSSet.iter print_atomic_functions summary.atomicFunctions ;
    F.pp_print_string fmt "\n" ;
    (* allOccurrences *)
    let print_all_occurrences (i : int) (allOccurrences : SSet.t) : unit =
      F.fprintf fmt "\t%i: {%s};\n" i (String.concat (SSet.elements allOccurrences) ~sep:", ")
    in
    F.pp_print_string fmt "allOccurrences:\n{\n" ;
    List.iteri summary.allOccurrences ~f:print_all_occurrences ;
    F.pp_print_string fmt "}\n" ;
    F.pp_print_string fmt "\n"


  let create (astate : astate) : t =
    (* Derivates atomic functions and all occurrences from the final calls pairs of elements of the
       abstract state. *)
    let atomicFunctions : SSSet.t ref = ref SSSet.empty
    and allOccurrences : SSet.t list ref = ref [] in
    let iterator (astateEl : tElement) : unit =
      let iterator ((_, pSnd) : callsPair) : unit =
        if not (SSet.is_empty pSnd) then atomicFunctions := SSSet.add pSnd !atomicFunctions
      in
      CallsPairSet.iter iterator astateEl.finalCallsPairs ;
      let iterator (i : int) (occurrences : SSet.t) : unit =
        allOccurrences :=
          match List.nth !allOccurrences i with
          | Some (_ : SSet.t) ->
              List.mapi !allOccurrences ~f:(fun (j : int) : (SSet.t -> SSet.t) ->
                  if Int.equal i j then SSet.union occurrences else Fn.id)
          | None ->
              if SSet.is_empty occurrences then !allOccurrences else !allOccurrences @ [occurrences]
      in
      List.iteri astateEl.allOccurrences ~f:iterator
    in
    TSet.iter iterator astate ;
    {atomicFunctions= !atomicFunctions; allOccurrences= !allOccurrences}


  let print_atomic_sets (summary : t) ~(fName : string) (oc : Out_channel.t) : int * int =
    if SSSet.is_empty summary.atomicFunctions then (0, 0)
    else (
      Out_channel.fprintf oc "%s: " fName ;
      let lastAtomicFunctions : SSet.t option = SSSet.max_elt_opt summary.atomicFunctions in
      let print_atomic_functions (atomicFunctions : SSet.t) : unit =
        Out_channel.fprintf oc "{%s}" (String.concat (SSet.elements atomicFunctions) ~sep:", ") ;
        if not (SSet.equal atomicFunctions (Option.value_exn lastAtomicFunctions)) then
          Out_channel.output_char oc ' '
      in
      SSSet.iter print_atomic_functions summary.atomicFunctions ;
      Out_channel.newline oc ;
      ( SSSet.cardinal summary.atomicFunctions
      , SSSet.fold
          (fun (atomicFunctions : SSet.t) : (int -> int) -> ( + ) (SSet.cardinal atomicFunctions))
          summary.atomicFunctions 0 ) )
end

let apply_summary (summary : Summary.t) : t -> t =
  (* Adds all occurrences from a given summary to the calls pairs and to the calls of each element
     of the abstract state. And merges all occurrences from a given summary with the all occurrences
     of each element of the abstract state. *)
  let mapper (astateEl : tElement) : tElement =
    let allOccurrences : SSet.t list ref = ref astateEl.allOccurrences
    and joinedAllOccurrences : SSet.t ref = ref SSet.empty in
    let iterator (i : int) (occurrences : SSet.t) : unit =
      ( if i + 1 < Config.atomic_sets_functions_depth_limit then
        allOccurrences :=
          match List.nth !allOccurrences (i + 1) with
          | Some (_ : SSet.t) ->
              List.mapi !allOccurrences ~f:(fun (j : int) : (SSet.t -> SSet.t) ->
                  if Int.equal (i + 1) j then SSet.union occurrences else Fn.id)
          | None ->
              if SSet.is_empty occurrences then !allOccurrences else !allOccurrences @ [occurrences]
      ) ;
      if i < Config.atomic_sets_functions_depth_limit then
        joinedAllOccurrences := SSet.union !joinedAllOccurrences occurrences
    in
    List.iteri summary.allOccurrences ~f:iterator ;
    let calls : SSet.t = SSet.union astateEl.calls !joinedAllOccurrences
    and callsPairs : CallsPairLockSet.t =
      CallsPairLockSet.map
        (fun (((pFst, pSnd), lock) : callsPairLock) : callsPairLock ->
          ((pFst, SSet.union pSnd !joinedAllOccurrences), lock))
        astateEl.callsPairs
    in
    (* Update the calls and the calls pairs and the all occurrences. *)
    update_astate_el_after_calls {astateEl with calls; callsPairs; allOccurrences= !allOccurrences}
  in
  TSet.map mapper
