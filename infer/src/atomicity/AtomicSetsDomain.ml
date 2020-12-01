(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module Set = Caml.Set
module SSet = AtomicityUtils.SSet

(** Detection of atomic sets domain implementation. *)

(* ************************************ Types *************************************************** *)

(** A pair of sets of calls. Calls without a lock followed by calls with a lock. *)
type callsPair = SSet.t * SSet.t [@@deriving compare, equal]

(** A pair of sets of calls with an access path. *)
type callsPairWithPath = callsPair * AccessPath.t option [@@deriving compare, equal]

(* ************************************ Modules ************************************************* *)

(** A set of pairs of sets of calls. *)
module CallsPairSet = Set.Make (struct
  type t = callsPair [@@deriving compare, equal]
end)

(** A set of sets of strings. *)
module SSSet = Set.Make (SSet)

(** A set of pairs of sets of calls with an access path. *)
module CallsPairWithPathSet = Set.Make (struct
  type t = callsPairWithPath [@@deriving compare, equal]
end)

(* ************************************ Astate ************************************************** *)

(** An element of an abstract state. *)
type tElement =
  { calls: SSet.t
  ; callsPairs: CallsPairWithPathSet.t
  ; finalCallsPairs: CallsPairSet.t
  ; allOccurrences: SSet.t list }
[@@deriving compare, equal]

(** A set of types tElement is an abstract state. *)
module TSet = Set.Make (struct
  type t = tElement [@@deriving compare, equal]
end)

type t = TSet.t [@@deriving compare, equal]

type astate = t [@@deriving compare, equal]

let initial : t =
  (* An initial abstract state is a set with a single empty element. *)
  TSet.singleton
    { calls= SSet.empty
    ; callsPairs= CallsPairWithPathSet.empty
    ; finalCallsPairs= CallsPairSet.empty
    ; allOccurrences= [SSet.empty] }


(** A pretty printer of an abstract state. *)
let pp (fmt : F.formatter) (astate : t) : unit =
  F.pp_print_string fmt "\n" ;
  let iterator (astateEl : tElement) : unit =
    F.pp_print_string fmt "{\n" ;
    (* calls *)
    F.fprintf fmt "\t{%s};\n" (String.concat (SSet.elements astateEl.calls) ~sep:", ") ;
    (* callsPairs *)
    F.pp_print_string fmt "\t" ;
    let lastCallsPair : callsPairWithPath option =
      CallsPairWithPathSet.max_elt_opt astateEl.callsPairs
    in
    let print_calls_pair (((pFst, pSnd), path) as callsPair : callsPairWithPath) : unit =
      let withoutLock : string = String.concat (SSet.elements pFst) ~sep:", "
      and withLock : string = String.concat (SSet.elements pSnd) ~sep:", " in
      ( match path with
      | Some (path : AccessPath.t) ->
          F.fprintf fmt "%a: {%s} ( {%s} )" AccessPath.pp path withoutLock withLock
      | None ->
          F.fprintf fmt "{%s} ( {%s} )" withoutLock withLock ) ;
      if not (equal_callsPairWithPath callsPair (Option.value_exn lastCallsPair)) then
        F.pp_print_string fmt " | "
    in
    CallsPairWithPathSet.iter print_calls_pair astateEl.callsPairs ;
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
    F.pp_print_string fmt "}\n"
  in
  TSet.iter iterator astate ;
  F.pp_print_string fmt "\n"


(** Modifies an element of an abstract state after addition of function calls. *)
let update_astate_el_after_calls (astateEl : tElement) : tElement =
  let finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs in
  let callsPairs : CallsPairWithPathSet.t =
    let filter (((pFst, pSnd), _) : callsPairWithPath) : bool =
      if SSet.cardinal pSnd > Config.atomic_sets_locked_functions_limit then (
        finalCallsPairs := CallsPairSet.add (pFst, SSet.empty) !finalCallsPairs ;
        false )
      else true
    in
    CallsPairWithPathSet.filter filter astateEl.callsPairs
  in
  {astateEl with callsPairs; finalCallsPairs= !finalCallsPairs}


let apply_call (astate : t) (f : string) : t =
  let mapper (astateEl : tElement) : tElement =
    let calls : SSet.t = SSet.add f astateEl.calls
    and callsPairs : CallsPairWithPathSet.t =
      CallsPairWithPathSet.map
        (fun (((pFst, pSnd), path) : callsPairWithPath) -> ((pFst, SSet.add f pSnd), path))
        astateEl.callsPairs
    and allOccurrences : SSet.t list =
      List.mapi astateEl.allOccurrences ~f:(fun (i : int) (occurrences : SSet.t) ->
          if Int.equal i 0 then SSet.add f occurrences else occurrences)
    in
    (* Update the calls and the calls pairs and the all occurrences. *)
    update_astate_el_after_calls {astateEl with calls; callsPairs; allOccurrences}
  in
  TSet.map mapper astate


let apply_lock ?ap:(lockPath : AccessPath.t option = None) (astate : t) : t =
  let mapper (astateEl : tElement) : tElement =
    let callsPairs : CallsPairWithPathSet.t =
      CallsPairWithPathSet.add ((astateEl.calls, SSet.empty), lockPath) astateEl.callsPairs
    in
    (* Clear the calls and update the calls pairs. *)
    {astateEl with calls= SSet.empty; callsPairs}
  in
  TSet.map mapper astate


let apply_unlock ?ap:(lockPath : AccessPath.t option = None) (astate : t) : t =
  let mapper (astateEl : tElement) : tElement =
    let finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs in
    let callsPairs : CallsPairWithPathSet.t =
      let filter ((p, path) : callsPairWithPath) : bool =
        if Option.equal AccessPath.equal path lockPath then (
          finalCallsPairs := CallsPairSet.add p !finalCallsPairs ;
          false )
        else true
      in
      CallsPairWithPathSet.filter filter astateEl.callsPairs
    in
    (* Clear the calls, update the calls pairs and the final calls pairs. *)
    {astateEl with calls= SSet.empty; callsPairs; finalCallsPairs= !finalCallsPairs}
  in
  TSet.map mapper astate


let update_at_the_end_of_function (astate : t) : t =
  let mapper (astateEl : tElement) : tElement =
    let finalCallsPairs : CallsPairSet.t ref = ref astateEl.finalCallsPairs in
    CallsPairWithPathSet.iter
      (fun ((p, _) : callsPairWithPath) -> finalCallsPairs := CallsPairSet.add p !finalCallsPairs)
      astateEl.callsPairs ;
    if not (SSet.is_empty astateEl.calls) then
      finalCallsPairs := CallsPairSet.add (astateEl.calls, SSet.empty) !finalCallsPairs ;
    (* Clear the calls and the calls pairs, and update the final calls pairs. *)
    { astateEl with
      calls= SSet.empty
    ; callsPairs= CallsPairWithPathSet.empty
    ; finalCallsPairs= !finalCallsPairs }
  in
  TSet.map mapper astate


(* ************************************ Operators *********************************************** *)

(** A comparison operator of abstract states. The lhs is less or equal to the rhs if lhs is a subset
    of the rhs. *)
let leq ~lhs:(l : t) ~rhs:(r : t) : bool = TSet.subset l r

(** A join operator of abstract states. Union of abstract states. *)
let join (astate1 : t) (astate2 : t) : t = TSet.union astate1 astate2

(** A widen operator of abstract states. Join previous and next abstract states. *)
let widen ~prev:(p : t) ~next:(n : t) ~num_iters:(i : int) : t =
  if i <= Config.atomic_sets_widen_limit then join p n else p


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
        F.pp_print_string fmt " "
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


  let make (astate : astate) : t =
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
              let mapper (j : int) (jOccurrences : SSet.t) : SSet.t =
                if Int.equal i j then SSet.union jOccurrences occurrences else jOccurrences
              in
              List.mapi !allOccurrences ~f:mapper
          | None ->
              if SSet.is_empty occurrences then !allOccurrences else !allOccurrences @ [occurrences]
      in
      List.iteri astateEl.allOccurrences ~f:iterator
    in
    TSet.iter iterator astate ;
    {atomicFunctions= !atomicFunctions; allOccurrences= !allOccurrences}


  let print_atomic_sets (summary : t) ~f_name:(f : string) (oc : Out_channel.t) : int * int =
    if SSSet.is_empty summary.atomicFunctions then (0, 0)
    else (
      Out_channel.fprintf oc "%s: " f ;
      let lastAtomicFunctions : SSet.t option = SSSet.max_elt_opt summary.atomicFunctions in
      let print_atomic_functions (atomicFunctions : SSet.t) : unit =
        Out_channel.fprintf oc "{%s}" (String.concat (SSet.elements atomicFunctions) ~sep:", ") ;
        if not (SSet.equal atomicFunctions (Option.value_exn lastAtomicFunctions)) then
          Out_channel.output_string oc " "
      in
      SSSet.iter print_atomic_functions summary.atomicFunctions ;
      Out_channel.newline oc ;
      ( SSSet.cardinal summary.atomicFunctions
      , SSSet.fold
          (fun (atomicFunctions : SSet.t) (sum : int) -> sum + SSet.cardinal atomicFunctions)
          summary.atomicFunctions 0 ) )
end

let apply_summary (astate : t) (summary : Summary.t) : t =
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
              let mapper (j : int) (jOccurrences : SSet.t) : SSet.t =
                if Int.equal (i + 1) j then SSet.union jOccurrences occurrences else jOccurrences
              in
              List.mapi !allOccurrences ~f:mapper
          | None ->
              if SSet.is_empty occurrences then !allOccurrences else !allOccurrences @ [occurrences]
      ) ;
      if i < Config.atomic_sets_functions_depth_limit then
        joinedAllOccurrences := SSet.union !joinedAllOccurrences occurrences
    in
    List.iteri summary.allOccurrences ~f:iterator ;
    let calls : SSet.t = SSet.union astateEl.calls !joinedAllOccurrences
    and callsPairs : CallsPairWithPathSet.t =
      CallsPairWithPathSet.map
        (fun (((pFst, pSnd), path) : callsPairWithPath) ->
          ((pFst, SSet.union pSnd !joinedAllOccurrences), path))
        astateEl.callsPairs
    in
    (* Update the calls and the calls pairs and the all occurrences. *)
    update_astate_el_after_calls {astateEl with calls; callsPairs; allOccurrences= !allOccurrences}
  in
  TSet.map mapper astate
