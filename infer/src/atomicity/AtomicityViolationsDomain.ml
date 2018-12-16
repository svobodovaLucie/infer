(* Author: Dominik Harmim <xharmi00@stud.fit.vutbr.cz> *)

open! IStd
module F = Format
module L = Logging
module Set = Caml.Set
module SSet = AtomicityUtils.SSet

(** Detection of atomicity violations domain implementation. *)

(* ************************************ Types *************************************************** *)

(** A pair of atomic functions. *)
type atomicPair = string * string [@@deriving compare]

(** A pair of atomic functions with its location. *)
type atomicPairLoc = {pair: atomicPair; line: int; col: int; file: string} [@@deriving compare]

(** A pair of atomic functions with an access path. *)
type atomicPairWithPath = atomicPair * AccessPath.t option [@@deriving compare]

(* ************************************ Functions *********************************************** *)

(** Makes a pair of atomic funcions with its location based on Location. *)
let make_atomic_pair_loc (p : atomicPair) (loc : Location.t) : atomicPairLoc =
  {pair= p; line= loc.line; col= loc.col; file= SourceFile.to_abs_path loc.file}


(** Pushes an element into an atomic pair. *)
let atomic_pair_push ((_, pSnd) : atomicPair) (s : string) : atomicPair = (pSnd, s)

(** Checks whether atomic pairs are equal. *)
let atomic_pairs_eq : atomicPair -> atomicPair -> bool = [%compare.equal: atomicPair]

(** Checks whether atomic pairs with a location are equal. *)
let atomic_pairs_loc_eq : atomicPairLoc -> atomicPairLoc -> bool = [%compare.equal: atomicPairLoc]

(** Checks whether atomic pairs with a path are equal. *)
let atomic_pairs_with_path_eq : atomicPairWithPath -> atomicPairWithPath -> bool =
  [%compare.equal: atomicPairWithPath]


(** An empty pair of atomic functions. *)
let emptyAtomicPair : atomicPair = ("", "")

(* ************************************ Modules ************************************************* *)

(** A set of pairs of atomic functions. *)
module AtomicPairSet = Set.Make (struct
  type t = atomicPair [@@deriving compare]
end)

(** A set of pairs of atomic functions with its location. *)
module AtomicPairLocSet = Set.Make (struct
  type t = atomicPairLoc [@@deriving compare]
end)

(** A set of pairs of atomic functions with an access path. *)
module AtomicPairWithPathSet = Set.Make (struct
  type t = atomicPairWithPath [@@deriving compare]
end)

(* ************************************ Global data ********************************************* *)

(** A type of global data. *)
type globalData = {initialised: bool; atomicPairs: AtomicPairSet.t} [@@deriving compare]

(** A global data reference. *)
let globalData : globalData ref = ref {initialised= false; atomicPairs= AtomicPairSet.empty}

(** Checks whether an atomic pair is violating atomicity. *)
let check_violating_atomicity ?(checkFirstEmpty : bool = false) ((_, pSnd) as p : atomicPair)
    ~(atomicityViolations : AtomicPairLocSet.t ref) ~(lockedLastPairs : AtomicPairWithPathSet.t)
    (loc : Location.t) : unit =
  let check (p : atomicPair) : unit =
    let is_pair_locked (p : atomicPair) : bool =
      let locked : bool ref = ref false in
      let iterator ((((_, pSnd') as p'), _) : atomicPairWithPath) : unit =
        if atomic_pairs_eq p' p || (checkFirstEmpty && atomic_pairs_eq ("", pSnd') p) then
          locked := true
      in
      AtomicPairWithPathSet.iter iterator lockedLastPairs ;
      !locked
    in
    if AtomicPairSet.mem p !globalData.atomicPairs && not (is_pair_locked p) then
      atomicityViolations := AtomicPairLocSet.add (make_atomic_pair_loc p loc) !atomicityViolations
  in
  check p ;
  if checkFirstEmpty then check ("", pSnd)


(* ************************************ Initialisation ****************************************** *)

let initialise (_ : unit) : unit =
  if not !globalData.initialised then (
    (* Check existence of the input file with atomic sets. *)
    ( match Sys.file_exists AtomicityUtils.atomicSetsFile with
    | `Yes ->
        ()
    | _ ->
        L.(die UserError)
          "File '%s' does not exist. Run the detection of atomic sets first using \
           '--atomic-sets-only'."
          AtomicityUtils.atomicSetsFile ) ;
    let atomicPairs : AtomicPairSet.t ref = ref AtomicPairSet.empty in
    (* Read atomic pairs from the input file. *)
    let ic : In_channel.t = In_channel.create ~binary:false AtomicityUtils.atomicSetsFile
    and read_line (l : string) : unit =
      (* Truncate the function name and split by atomic sets. *)
      let sets : string list =
        Str.split (Str.regexp "} {") (Str.replace_first (Str.regexp "^.+: ") "" l)
      in
      let iterator (set : string) : unit =
        (* Truncate parentheses and commas and split by functions. *)
        let functions : string list =
          Str.split (Str.regexp ", ") (Str.global_replace (Str.regexp "}\\|{") "" set)
        in
        let functionsCount : int = List.length functions in
        if Int.equal functionsCount 1 then
          atomicPairs := AtomicPairSet.add ("", List.nth_exn functions 0) !atomicPairs
        else
          for i = 0 to functionsCount - 1 do
            for j = i + 1 to functionsCount - 1 do
              atomicPairs :=
                AtomicPairSet.add (List.nth_exn functions i, List.nth_exn functions j) !atomicPairs ;
              atomicPairs :=
                AtomicPairSet.add (List.nth_exn functions j, List.nth_exn functions i) !atomicPairs
            done
          done
      in
      List.iter sets ~f:iterator
    in
    In_channel.iter_lines ~fix_win_eol:true ic ~f:read_line ;
    In_channel.close ic ;
    globalData := {initialised= true; atomicPairs= !atomicPairs} )


(* ************************************ Astate ************************************************** *)

(** An element of an abstract state. *)
type tElement =
  { firstCall: string
  ; lastPair: atomicPair
  ; nestedLastCalls: SSet.t
  ; atomicityViolations: AtomicPairLocSet.t
  ; lockedLastPairs: AtomicPairWithPathSet.t }
[@@deriving compare]

(** A set of types tElement is an abstract state. *)
module TSet = Set.Make (struct
  type t = tElement [@@deriving compare]
end)

type t = TSet.t [@@deriving compare]

type astate = t [@@deriving compare]

let initial : t =
  (* An initial abstract state is a set with a single empty element. *)
  TSet.singleton
    { firstCall= ""
    ; lastPair= emptyAtomicPair
    ; nestedLastCalls= SSet.empty
    ; atomicityViolations= AtomicPairLocSet.empty
    ; lockedLastPairs= AtomicPairWithPathSet.empty }


(** A pretty printer of an abstract state. *)
let pp (fmt : F.formatter) (astate : t) : unit =
  F.pp_print_string fmt "\n" ;
  let iterator (astateEl : tElement) : unit =
    F.pp_print_string fmt "{\n" ;
    (* firstCall *)
    F.fprintf fmt "\t%s;\n" astateEl.firstCall ;
    (* lastPair *)
    F.fprintf fmt "\t(%s, %s);\n" (fst astateEl.lastPair) (snd astateEl.lastPair) ;
    (* nestedLastCalls *)
    F.fprintf fmt "\t{%s};\n" (String.concat (SSet.elements astateEl.nestedLastCalls) ~sep:", ") ;
    (* atomicityViolations *)
    F.pp_print_string fmt "\t" ;
    let lastAtomicityViolationsPair : atomicPairLoc option =
      AtomicPairLocSet.max_elt_opt astateEl.atomicityViolations
    in
    let print_atomicity_violations_pair (p : atomicPairLoc) : unit =
      F.fprintf fmt "%s:%i:%i -> (%s, %s)" p.file p.line p.col (fst p.pair) (snd p.pair) ;
      if not (atomic_pairs_loc_eq p (Option.value_exn lastAtomicityViolationsPair)) then
        F.pp_print_string fmt " | "
    in
    AtomicPairLocSet.iter print_atomicity_violations_pair astateEl.atomicityViolations ;
    F.pp_print_string fmt ";\n" ;
    (* lockedLastPairs *)
    F.pp_print_string fmt "\t" ;
    let lastLockedLastPair : atomicPairWithPath option =
      AtomicPairWithPathSet.max_elt_opt astateEl.lockedLastPairs
    in
    let print_locked_last_pair (((pFst, pSnd), path) as lockedLastPair : atomicPairWithPath) : unit
        =
      ( match path with
      | Some (path : AccessPath.t) ->
          F.fprintf fmt "%a: (%s, %s)" AccessPath.pp path pFst pSnd
      | None ->
          F.fprintf fmt "(%s, %s)" pFst pSnd ) ;
      if not (atomic_pairs_with_path_eq lockedLastPair (Option.value_exn lastLockedLastPair)) then
        F.pp_print_string fmt " | "
    in
    AtomicPairWithPathSet.iter print_locked_last_pair astateEl.lockedLastPairs ;
    F.pp_print_string fmt ";\n" ;
    F.pp_print_string fmt "}\n"
  in
  TSet.iter iterator astate ;
  F.pp_print_string fmt "\n"


let apply_call (astate : t) (f : string) (loc : Location.t) : t =
  let mapper (astateEl : tElement) : tElement =
    let firstCall : string = if String.is_empty astateEl.firstCall then f else astateEl.firstCall
    and lastPair : atomicPair = atomic_pair_push astateEl.lastPair f
    and atomicityViolations : AtomicPairLocSet.t ref = ref astateEl.atomicityViolations
    and lockedLastPairs : AtomicPairWithPathSet.t =
      (* Updates pairs of atomic functions. *)
      AtomicPairWithPathSet.map
        (fun ((p, path) : atomicPairWithPath) -> (atomic_pair_push p f, path))
        astateEl.lockedLastPairs
    in
    (* Check whether the last pair is violating atomicity. *)
    check_violating_atomicity lastPair ~atomicityViolations ~lockedLastPairs loc
      ~checkFirstEmpty:true ;
    let iterator (lastCall : string) : unit =
      let p : atomicPair = (lastCall, f) in
      let lockedLastPairs : AtomicPairWithPathSet.t =
        AtomicPairWithPathSet.map
          (fun ((p', path) : atomicPairWithPath) ->
            ((if String.is_empty (fst p') then p' else p), path))
          lockedLastPairs
      in
      (* Check whether each pair begining with the nested last call and ending with the current
         function call is violating atomicity. *)
      check_violating_atomicity p ~atomicityViolations ~lockedLastPairs loc
    in
    SSet.iter iterator astateEl.nestedLastCalls ;
    (* Update the first call, the last pair, the atomicity violations, the locked last pairs, and
       clear the nested last calls. *)
    { firstCall
    ; lastPair
    ; nestedLastCalls= SSet.empty
    ; atomicityViolations= !atomicityViolations
    ; lockedLastPairs }
  in
  TSet.map mapper astate


let apply_lock ?ap:(lockPath : AccessPath.t option = None) (astate : t) : t =
  let mapper (astateEl : tElement) : tElement =
    let lockedLastPairs : AtomicPairWithPathSet.t =
      AtomicPairWithPathSet.add (emptyAtomicPair, lockPath) astateEl.lockedLastPairs
    in
    {astateEl with lockedLastPairs}
  in
  TSet.map mapper astate


let apply_unlock ?ap:(lockPath : AccessPath.t option = None) (astate : t) : t =
  let mapper (astateEl : tElement) : tElement =
    let lockedLastPairs : AtomicPairWithPathSet.t =
      AtomicPairWithPathSet.filter
        (fun ((_, path) : atomicPairWithPath) -> not (Option.equal AccessPath.equal path lockPath))
        astateEl.lockedLastPairs
    in
    {astateEl with lockedLastPairs}
  in
  TSet.map mapper astate


let report_atomicity_violations (astate : t) ~f:(report : Location.t -> msg:string -> unit) : unit =
  (* Report atomicity violations from atomicity violations stored in the abstract state. *)
  let iterator (astateEl : tElement) : unit =
    let iterator (p : atomicPairLoc) : unit =
      let (fst, snd) : atomicPair = p.pair in
      if (not (String.is_empty fst)) || not (String.is_empty snd) then
        let loc : Location.t = {line= p.line; col= p.col; file= SourceFile.from_abs_path p.file}
        and msg : string =
          if (not (String.is_empty fst)) && not (String.is_empty snd) then
            F.asprintf "Atomicity Violation! - Functions '%s' and '%s' should be called atomically."
              fst snd
          else
            F.asprintf "Atomicity Violation! - Function '%s' should be called atomically."
              (if String.is_empty fst then snd else fst)
        in
        report loc ~msg
    in
    AtomicPairLocSet.iter iterator astateEl.atomicityViolations
  in
  TSet.iter iterator astate


(* ************************************ Operators *********************************************** *)

(** A comparison operator of abstract states. The lhs is less or equal to the rhs if the lhs is a
    subset of the rhs. *)
let leq ~lhs:(l : t) ~rhs:(r : t) : bool = TSet.subset l r

(** A join operator of abstract states. Union of abstract states. *)
let join (astate1 : t) (astate2 : t) : t = TSet.union astate1 astate2

(** A widen operator of abstract states. Join previous and next abstract states. *)
let widen ~prev:(p : t) ~next:(n : t) ~num_iters:(i : int) : t =
  if i <= Config.atomicity_violations_widen_limit then join p n else p


(* ************************************ Summary ************************************************* *)

module Summary = struct
  type t = {firstCalls: SSet.t; lastCalls: SSet.t} [@@deriving compare]

  let pp (fmt : F.formatter) (summary : t) : unit =
    F.pp_print_string fmt "\n" ;
    (* firstCalls *)
    F.fprintf fmt "firstCalls: {%s}\n" (String.concat (SSet.elements summary.firstCalls) ~sep:", ") ;
    (* lastCalls *)
    F.fprintf fmt "lastCalls: {%s}\n" (String.concat (SSet.elements summary.lastCalls) ~sep:", ") ;
    F.pp_print_string fmt "\n"


  let make (astate : astate) : t =
    (* Derivates the first calls and the last calls from the first calls and from the last pairs of
       elements of the abstract state. *)
    let firstCalls : SSet.t ref = ref SSet.empty and lastCalls : SSet.t ref = ref SSet.empty in
    let iterator (astateEl : tElement) : unit =
      if not (String.is_empty astateEl.firstCall) then
        firstCalls := SSet.add astateEl.firstCall !firstCalls ;
      if not (String.is_empty (snd astateEl.lastPair)) then
        lastCalls := SSet.add (snd astateEl.lastPair) !lastCalls
    in
    TSet.iter iterator astate ;
    {firstCalls= !firstCalls; lastCalls= !lastCalls}
end

let apply_summary (astate : t) (summary : Summary.t) (loc : Location.t) : t =
  (* Add the last calls from a given summary to the nested last calls of the abstract state and
     check for atomicity violations with the first calls of a given summary. *)
  if SSet.is_empty summary.firstCalls && SSet.is_empty summary.lastCalls then astate
  else
    let mapper (astateEl : tElement) : tElement =
      let atomicityViolations : AtomicPairLocSet.t ref = ref astateEl.atomicityViolations
      and lastCall : string = snd astateEl.lastPair in
      let iterator (firstCall : string) : unit =
        let p : atomicPair = (lastCall, firstCall) in
        let lockedLastPairs : AtomicPairWithPathSet.t =
          AtomicPairWithPathSet.map
            (fun ((_, path) : atomicPairWithPath) -> (p, path))
            astateEl.lockedLastPairs
        in
        (* Check whether each pair begining with the last called function and ending witch the first
           call of a given summary is violating atomicity. *)
        check_violating_atomicity p ~atomicityViolations ~lockedLastPairs loc
      in
      SSet.iter iterator summary.firstCalls ;
      {astateEl with nestedLastCalls= summary.lastCalls; atomicityViolations= !atomicityViolations}
    in
    TSet.map mapper astate
