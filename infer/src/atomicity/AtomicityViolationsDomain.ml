(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
open AtomicityUtils
module F = Format
module L = Logging
module Set = Caml.Set

(** Detection of atomicity violations domain implementation. *)

(* ************************************ Types *************************************************** *)

(** A pair of atomic functions. *)
type atomic_pair = string * string [@@deriving compare, equal]

(** A pair of atomic functions with a lock. *)
type atomic_pair_lock = atomic_pair * Lock.t [@@deriving compare, equal]

(* ************************************ Constants *********************************************** *)

(** An empty pair of atomic functions. *)
let emptyAtomicPair : atomic_pair = ("", "")

(* ************************************ Modules ************************************************* *)

(** A set of pairs of atomic functions. *)
module AtomicPairSet = Set.Make (struct
  type t = atomic_pair [@@deriving compare, equal]
end)

(** A module that represents atomicity violations to be reported. *)
module Violations : sig
  include PrettyPrintable.PrintableEquatableOrderedType

  (** A severity of an atomicity violation to be reported. *)
  type violation_severity = private
    | Warning  (** WARNING severity - used for local atomicity violations. *)
    | Error  (** ERROR severity - used for real (global) atomicity violations. *)
  [@@deriving compare, equal]

  val empty : t
  (** Creates an empty module. *)

  val is_empty : t -> bool
  (** Checks whether there are any violations to be reported. *)

  val add : atomic_pair -> Location.t -> t -> t
  (** Adds a new violation to be reported. *)

  val union : t -> t -> t
  (** Makes an union of atomicity violations to be reported. *)

  val fold : f:(atomic_pair * Location.t * violation_severity -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold ~f:f s a] computes (f xN ... (f x2 (f x1 a))...), where x1 ... xN are the elements of s,
      in increasing order. *)

  val make_all_warnings : t -> t
  (** Labels all atomicity violations to be reported as warnings. *)

  val severity_to_issue_type : violation_severity -> IssueType.t
  (** Converts the severity of a violation to IssueType. *)
end = struct
  type violation_severity = Warning | Error [@@deriving compare, equal]

  (** A structure that represents a single atomicity violation to be reported. *)
  type violation =
    {pair: atomic_pair; line: int; col: int; file: string; severity: violation_severity}
  [@@deriving compare, equal]

  (** A set of atomicity violations to be reported. *)
  module ViolationSet = Set.Make (struct
    type t = violation [@@deriving compare, equal]
  end)

  type t = ViolationSet.t [@@deriving compare, equal]

  let pp (fmt : F.formatter) (violations : t) : unit =
    let lastViolation : violation option = ViolationSet.max_elt_opt violations in
    let print_violation (violation : violation) : unit =
      let pp_severity (fmt : F.formatter) : violation_severity -> unit = function
        | Warning ->
            F.pp_print_string fmt "WARNING"
        | Error ->
            F.pp_print_string fmt "ERROR"
      in
      F.fprintf fmt "%s:%i:%i: %a -> (%s, %s)" violation.file violation.line violation.col
        pp_severity violation.severity (fst violation.pair) (snd violation.pair) ;
      if not (equal_violation violation (Option.value_exn lastViolation)) then
        F.pp_print_string fmt " | "
    in
    ViolationSet.iter print_violation violations


  let empty : t = ViolationSet.empty

  let is_empty : t -> bool = ViolationSet.is_empty

  let add (pair : atomic_pair) (loc : Location.t) : t -> t =
    ViolationSet.add
      {pair; line= loc.line; col= loc.col; file= SourceFile.to_abs_path loc.file; severity= Error}


  let union : t -> t -> t = ViolationSet.union

  let fold ~(f : atomic_pair * Location.t * violation_severity -> 'a -> 'a) : t -> 'a -> 'a =
    ViolationSet.fold (fun (violation : violation) : ('a -> 'a) ->
        let loc : Location.t =
          {line= violation.line; col= violation.col; file= SourceFile.from_abs_path violation.file}
        in
        f (violation.pair, loc, violation.severity))


  let make_all_warnings : t -> t =
    ViolationSet.map (fun (violation : violation) : violation -> {violation with severity= Warning})


  let severity_to_issue_type : violation_severity -> IssueType.t = function
    | Warning ->
        IssueType.atomicity_violation_warning
    | Error ->
        IssueType.atomicity_violation_error
end

(** A set of pairs of atomic functions with locks. *)
module AtomicPairLockSet = Set.Make (struct
  type t = atomic_pair_lock [@@deriving compare, equal]
end)

(* ************************************ Classes ************************************************* *)

(** A class that works with atomic pairs loaded from the first phase of the analysis. *)
class atomic_pairs =
  object (self)
    (** Is the class initialised? *)
    val mutable initialised : bool = false

    (** A set of pairs of functions that should be called atomically. *)
    val mutable pairs : AtomicPairSet.t = AtomicPairSet.empty

    (** Initialises the class. *)
    method private init : unit =
      if not initialised then (
        initialised <- true ;
        (* Check existence of the input file with atomic sets. *)
        ( match Sys.file_exists atomicSetsFile with
        | `Yes ->
            ()
        | _ ->
            L.die UserError
              "File '%s' does not exist. Run the detection of atomic sets first using \
               '--atomic-sets-only'."
              atomicSetsFile ) ;
        (* Read atomic pairs from the input file. *)
        let ic : In_channel.t = In_channel.create ~binary:false atomicSetsFile
        and read_line (l : string) : unit =
          if is_line_empty l then ()
          else
            let l : string = String.strip l in
            (* Truncate the function name and split by atomic sets. *)
            let sets : string list =
              Str.split (Str.regexp "}[ \t]+{") (Str.replace_first (Str.regexp "^.+:[ \t]+") "" l)
            and iterator (set : string) : unit =
              (* Truncate parentheses and commas and split by functions. *)
              let functions : string list =
                Str.split (Str.regexp ",[ \t]+")
                  (String.strip (Str.global_replace (Str.regexp "}\\|{") "" set))
              in
              let functionsCount : int = List.length functions in
              if Int.equal functionsCount 1 then
                pairs <- AtomicPairSet.add ("", List.nth_exn functions 0) pairs
              else
                for i = 0 to functionsCount - 1 do
                  for j = i + 1 to functionsCount - 1 do
                    pairs <-
                      AtomicPairSet.add (List.nth_exn functions i, List.nth_exn functions j) pairs ;
                    pairs <-
                      AtomicPairSet.add (List.nth_exn functions j, List.nth_exn functions i) pairs
                  done
                done
            in
            List.iter sets ~f:iterator
        in
        In_channel.iter_lines ~fix_win_eol:true ic ~f:read_line ;
        In_channel.close ic )

    (** Checks whether an atomic pair is violating atomicity. *)
    method check_violating_atomicity ?(checkFirstEmpty : bool = false)
        ((_, pSnd) as p : atomic_pair) ~(violations : Violations.t ref)
        ~(lockedLastPairs : AtomicPairLockSet.t) (loc : Location.t) : unit =
      self#init ;
      let check (p : atomic_pair) : unit =
        let is_pair_locked (p : atomic_pair) : bool =
          let fold ((((_, pSnd') as p'), _) : atomic_pair_lock) : bool -> bool =
            ( || ) (equal_atomic_pair p' p || (checkFirstEmpty && equal_atomic_pair ("", pSnd') p))
          in
          AtomicPairLockSet.fold fold lockedLastPairs false
        in
        if AtomicPairSet.mem p pairs && not (is_pair_locked p) then
          violations := Violations.add p loc !violations
      in
      check p ;
      if checkFirstEmpty then check ("", pSnd)
  end

(** An instance of the 'atomic_pairs' class. *)
let atomicPairs : atomic_pairs = new atomic_pairs

(* ************************************ Astate ************************************************** *)

(** An element of an abstract state. *)
type t_element =
  { firstCall: string
  ; lastPair: atomic_pair
  ; nestedLastCalls: SSet.t
  ; violations: Violations.t
  ; lockedLastPairs: AtomicPairLockSet.t
  ; guards: Guards.t
  ; allCalls: SSet.t }
[@@deriving compare, equal]

(** A set of types tElement is an abstract state. *)
module TSet = Set.Make (struct
  type t = t_element [@@deriving compare, equal]
end)

type t = TSet.t [@@deriving compare, equal]

type astate = t [@@deriving compare, equal]

let initial : t =
  assert_user
    (Config.atomicity_violations_widen_limit > 0)
    "Input argument '--atomicity-violations-widen-limit' should be greater than 0, %d given."
    Config.atomicity_violations_widen_limit ;
  (* An initial abstract state is a set with a single empty element. *)
  TSet.singleton
    { firstCall= ""
    ; lastPair= emptyAtomicPair
    ; nestedLastCalls= SSet.empty
    ; violations= Violations.empty
    ; lockedLastPairs= AtomicPairLockSet.empty
    ; guards= Guards.empty
    ; allCalls= SSet.empty }


let pp (fmt : F.formatter) (astate : t) : unit =
  F.pp_print_string fmt "\n" ;
  let iterator (astateEl : t_element) : unit =
    F.pp_print_string fmt "{\n" ;
    (* firstCall *)
    F.fprintf fmt "\t%s;\n" astateEl.firstCall ;
    (* lastPair *)
    F.fprintf fmt "\t(%s, %s);\n" (fst astateEl.lastPair) (snd astateEl.lastPair) ;
    (* nestedLastCalls *)
    F.fprintf fmt "\t{%s};\n" (String.concat (SSet.elements astateEl.nestedLastCalls) ~sep:", ") ;
    (* atomicityViolations *)
    F.fprintf fmt "\t%a;\n" Violations.pp astateEl.violations ;
    (* lockedLastPairs *)
    F.pp_print_string fmt "\t" ;
    let lastLockedLastPair : atomic_pair_lock option =
      AtomicPairLockSet.max_elt_opt astateEl.lockedLastPairs
    in
    let print_locked_last_pair (((pFst, pSnd), lock) as lockedLastPair : atomic_pair_lock) : unit =
      F.fprintf fmt "%a: (%s, %s)" Lock.pp lock pFst pSnd ;
      if not (equal_atomic_pair_lock lockedLastPair (Option.value_exn lastLockedLastPair)) then
        F.pp_print_string fmt " | "
    in
    AtomicPairLockSet.iter print_locked_last_pair astateEl.lockedLastPairs ;
    F.pp_print_string fmt ";\n" ;
    (* guards *)
    F.fprintf fmt "\t{\n%a\t};\n" Guards.pp astateEl.guards ;
    (* allCalls *)
    F.fprintf fmt "\t{%s};\n" (String.concat (SSet.elements astateEl.allCalls) ~sep:", ") ;
    F.pp_print_string fmt "}\n"
  in
  TSet.iter iterator astate ;
  F.pp_print_string fmt "\n"


let apply_call ~(fName : string) (loc : Location.t) : t -> t =
  let mapper (astateEl : t_element) : t_element =
    let atomic_pair_push ((_, pSnd) : atomic_pair) : string -> atomic_pair = Tuple2.create pSnd in
    let firstCall : string =
      if String.is_empty astateEl.firstCall then fName else astateEl.firstCall
    and lastPair : atomic_pair = atomic_pair_push astateEl.lastPair fName
    and violations : Violations.t ref = ref astateEl.violations
    and lockedLastPairs : AtomicPairLockSet.t =
      (* Updates pairs of atomic functions. *)
      AtomicPairLockSet.map
        (fun ((p, lock) : atomic_pair_lock) : atomic_pair_lock -> (atomic_pair_push p fName, lock))
        astateEl.lockedLastPairs
    and allCalls : SSet.t = SSet.add fName astateEl.allCalls in
    (* Check whether the last pair is violating atomicity. *)
    atomicPairs#check_violating_atomicity lastPair ~violations ~lockedLastPairs loc
      ~checkFirstEmpty:true ;
    let iterator (lastCall : string) : unit =
      let p : atomic_pair = (lastCall, fName) in
      let lockedLastPairs : AtomicPairLockSet.t =
        AtomicPairLockSet.map
          (fun ((p', lock) : atomic_pair_lock) : atomic_pair_lock ->
            ((if String.is_empty (fst p') then p' else p), lock))
          lockedLastPairs
      in
      (* Check whether each pair begining with the nested last call and ending with the current
         function call is violating atomicity. *)
      atomicPairs#check_violating_atomicity p ~violations ~lockedLastPairs loc
    in
    SSet.iter iterator astateEl.nestedLastCalls ;
    { astateEl with
      firstCall
    ; lastPair
    ; nestedLastCalls= SSet.empty
    ; violations= !violations
    ; lockedLastPairs
    ; allCalls }
  in
  TSet.map mapper


let apply_locks (locksPaths : AccessPath.t list) : t -> t =
  let mapper (astateEl : t_element) : t_element =
    let locksPaths : AccessPath.t list = Guards.reveal_locks astateEl.guards locksPaths in
    let lockedLastPairs : AtomicPairLockSet.t =
      let fold (lockedLastPairs : AtomicPairLockSet.t) (path : AccessPath.t) : AtomicPairLockSet.t =
        let found : bool ref = ref false in
        let mapper ((p, lock) as pairLock : atomic_pair_lock) : atomic_pair_lock =
          if AccessPath.equal path (Lock.path lock) then (
            found := true ;
            (p, Lock.lock lock) )
          else pairLock
        in
        let lockedLastPairs : AtomicPairLockSet.t = AtomicPairLockSet.map mapper lockedLastPairs in
        if !found then lockedLastPairs
        else AtomicPairLockSet.add (emptyAtomicPair, Lock.create path) lockedLastPairs
      in
      List.fold locksPaths ~init:astateEl.lockedLastPairs ~f:fold
    in
    {astateEl with lockedLastPairs}
  in
  TSet.map mapper


let apply_unlocks (locksPaths : AccessPath.t list) : t -> t =
  let mapper (astateEl : t_element) : t_element =
    let locksPaths : AccessPath.t list = Guards.reveal_locks astateEl.guards locksPaths in
    let lockedLastPairs : AtomicPairLockSet.t =
      let mapper ((p, lock) as pairLock : atomic_pair_lock) : atomic_pair_lock option =
        let ((_, lock) as pairLock : atomic_pair_lock) =
          if List.mem locksPaths (Lock.path lock) ~equal:AccessPath.equal then (p, Lock.unlock lock)
          else pairLock
        in
        if Lock.is_locked lock then Some pairLock else None
      in
      AtomicPairLockSet.filter_map mapper astateEl.lockedLastPairs
    in
    {astateEl with lockedLastPairs}
  in
  TSet.map mapper


let apply_guard_construct (guardPath : AccessPath.t) (locksPaths : AccessPath.t list)
    ~(acquire : bool) : t -> t =
  let add_guard : t -> t =
    TSet.map (fun (astateEl : t_element) : t_element ->
        {astateEl with guards= Guards.add guardPath locksPaths astateEl.guards})
  in
  if acquire then Fn.compose (apply_locks locksPaths) add_guard else add_guard


let apply_guard_release (guardPath : AccessPath.t) : t -> t =
  TSet.map (fun (astateEl : t_element) : t_element ->
      {astateEl with guards= Guards.remove guardPath astateEl.guards})


let apply_guard_destroy (guardPath : AccessPath.t) : t -> t =
  Fn.compose (apply_guard_release guardPath) (apply_unlocks [guardPath])


(* ************************************ Operators *********************************************** *)

let leq ~(lhs : t) ~(rhs : t) : bool =
  (* The lhs is less or equal to the rhs if the lhs is a subset of the rhs. *)
  if phys_equal lhs rhs then true else TSet.subset lhs rhs


let join (astate1 : t) (astate2 : t) : t =
  (* Union of abstract states. *)
  if phys_equal astate1 astate2 then astate1 else TSet.union astate1 astate2


let widen ~(prev : t) ~(next : t) ~(num_iters : int) : t =
  (* Join previous and next abstract states. *)
  if phys_equal prev next then prev
  else if num_iters <= Config.atomicity_violations_widen_limit then join prev next
  else prev


(* ************************************ Summary ************************************************* *)

module Summary = struct
  type t =
    { mutable firstCalls: SSet.t
    ; mutable lastCalls: SSet.t
    ; mutable violations: Violations.t
    ; mutable allCalls: SSet.t }
  [@@deriving compare, equal]

  let pp (fmt : F.formatter) (summary : t) : unit =
    F.pp_print_string fmt "\n" ;
    (* firstCalls *)
    F.fprintf fmt "firstCalls: {%s}\n" (String.concat (SSet.elements summary.firstCalls) ~sep:", ") ;
    (* lastCalls *)
    F.fprintf fmt "lastCalls: {%s}\n" (String.concat (SSet.elements summary.lastCalls) ~sep:", ") ;
    (* violations *)
    F.fprintf fmt "violations: %a\n" Violations.pp summary.violations ;
    (* allCalls *)
    F.fprintf fmt "allCalls: {%s}\n" (String.concat (SSet.elements summary.allCalls) ~sep:", ") ;
    F.pp_print_string fmt "\n"


  let create (astate : astate) : t =
    (* Derivates the first calls and the last calls from the first calls and from the last pairs of
       elements of the abstract state. *)
    let summary : t =
      { firstCalls= SSet.empty
      ; lastCalls= SSet.empty
      ; violations= Violations.empty
      ; allCalls= SSet.empty }
    in
    let iterator (astateEl : t_element) : unit =
      if not (String.is_empty astateEl.firstCall) then
        summary.firstCalls <- SSet.add astateEl.firstCall summary.firstCalls ;
      if not (String.is_empty (snd astateEl.lastPair)) then
        summary.lastCalls <- SSet.add (snd astateEl.lastPair) summary.lastCalls ;
      summary.violations <- Violations.union astateEl.violations summary.violations ;
      summary.allCalls <- SSet.union astateEl.allCalls summary.allCalls
    in
    TSet.iter iterator astate ;
    summary


  let is_top_level_fun (pName : Procname.t) : (Procname.t * t) list -> bool =
    List.for_all ~f:(fun ((pName' : Procname.t), (summary : t)) : bool ->
        Procname.equal pName' pName || not (SSet.mem (Procname.to_string pName) summary.allCalls))


  let report_atomicity_violations
      ~(f : Location.t -> msg:string -> IssueType.t -> IssueLog.t -> IssueLog.t) (summary : t) :
      IssueLog.t -> IssueLog.t =
    (* Report atomicity violations from atomicity violations stored in the summary. *)
    let fold
        (((fst, snd) : atomic_pair), (loc : Location.t), (severity : Violations.violation_severity))
        (issueLog : IssueLog.t) : IssueLog.t =
      if String.is_empty fst && String.is_empty snd then issueLog
      else
        let msg : string =
          let warningMsg : string =
            match severity with Warning -> " within a Current Function" | _ -> ""
          in
          if (not (String.is_empty fst)) && not (String.is_empty snd) then
            F.asprintf
              "Atomicity Violation%s! - Functions '%s' and '%s' should be called atomically."
              warningMsg fst snd
          else
            F.asprintf "Atomicity Violation%s! - Function '%s' should be called atomically."
              warningMsg
              (if String.is_empty fst then snd else fst)
        in
        f loc ~msg (Violations.severity_to_issue_type severity) issueLog
    in
    Violations.fold ~f:fold summary.violations
end

let apply_summary (summary : Summary.t) (loc : Location.t) : t -> t =
  (* Add the last calls from a given summary to the nested last calls of the abstract state and
     check for atomicity violations with the first calls of a given summary. *)
  if
    SSet.is_empty summary.firstCalls && SSet.is_empty summary.lastCalls
    && Violations.is_empty summary.violations
  then Fn.id
  else
    let mapper (astateEl : t_element) : t_element =
      let violations : Violations.t ref =
        let summaryViolations : Violations.t =
          if AtomicPairLockSet.is_empty astateEl.lockedLastPairs then summary.violations
          else Violations.make_all_warnings summary.violations
        in
        ref (Violations.union astateEl.violations summaryViolations)
      and lastCall : string = snd astateEl.lastPair in
      let iterator (firstCall : string) : unit =
        let p : atomic_pair = (lastCall, firstCall) in
        let lockedLastPairs : AtomicPairLockSet.t =
          AtomicPairLockSet.map (Fn.compose (Tuple2.create p) snd) astateEl.lockedLastPairs
        in
        (* Check whether each pair begining with the last called function and ending witch the first
           call of a given summary is violating atomicity. *)
        atomicPairs#check_violating_atomicity p ~violations ~lockedLastPairs loc
      in
      SSet.iter iterator summary.firstCalls ;
      {astateEl with nestedLastCalls= summary.lastCalls; violations= !violations}
    in
    TSet.map mapper
