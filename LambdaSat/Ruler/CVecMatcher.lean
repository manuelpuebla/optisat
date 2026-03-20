/-
  LambdaSat — Ruler/CVecMatcher: CVec-Based Candidate Pair Generation
  Fase 20 Subfase 3: Group patterns by CVec, generate candidate equalities.
  Fase 14 (v2.1): Multi-mode matching for non-equality relations.

  Patterns with identical CVecs are candidates for equality rules.
  This module groups patterns by their CVec hash and generates all
  candidate pairs within each bucket.

  v2.1 extension: `DetectedRelation` tags each candidate with the
  relation detected (eq/le/dvd/modN/conditional). `cvecMatchWithMode`
  and `cvecMatchMultiMode` scan for non-equality relations.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `CandidatePair`: two patterns with matching CVecs + detected relation
  - `cvecMatch`: group by CVec hash, generate equality candidate pairs
  - `cvecMatchWithMode`: generate candidates for a specific relation mode
  - `cvecMatchMultiMode`: scan all modes, return best match per pair
-/
import LambdaSat.Ruler.CVecEngine

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CandidatePair
-- ══════════════════════════════════════════════════════════════════

/-- The type of relation detected by CVec matching. -/
inductive DetectedRelation where
  /-- Equality: lhs = rhs -/
  | eq : DetectedRelation
  /-- Less-or-equal: lhs ≤ rhs -/
  | le : DetectedRelation
  /-- Divisibility: lhs ∣ rhs -/
  | dvd : DetectedRelation
  /-- Modular congruence: lhs ≡ rhs (mod n) -/
  | modN (n : Nat) : DetectedRelation
  /-- Conditional equality: P → lhs = rhs, with agreeing positions -/
  | conditional (agreeCount total : Nat) : DetectedRelation
  deriving Repr, BEq, DecidableEq

/-- A candidate pair: two patterns whose CVecs match under some relation.
    These are candidates for rewrite/relation rules. -/
structure CandidatePair where
  /-- Left-hand side pattern -/
  lhs : Pattern Nat
  /-- Right-hand side pattern -/
  rhs : Pattern Nat
  /-- The shared CVec (for debugging/verification) -/
  cvec : CVec
  /-- The detected relation (default: equality) -/
  relation : DetectedRelation := .eq

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Bucketing by CVec
-- ══════════════════════════════════════════════════════════════════

/-- A bucket: patterns that share the same CVec hash. -/
structure CVecBucket where
  hash : UInt64
  cvec : CVec
  patterns : List (Pattern Nat)

/-- Group patterns by their CVec. Returns a list of buckets. -/
def groupByCVec (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (patterns : List (Pattern Nat)) : List CVecBucket :=
  let tagged := patterns.map fun p =>
    let cv := evaluateCVec evalOp inputs p
    (cvecHash cv, cv, p)
  -- Group by hash (simple quadratic grouping for sketch phase)
  let rec buildBuckets : List (UInt64 × CVec × Pattern Nat) → List CVecBucket → List CVecBucket
    | [], buckets => buckets
    | (h, cv, p) :: rest, buckets =>
      match buckets.find? (fun b => b.hash == h && cvecEqual b.cvec cv) with
      | some _ =>
        let buckets' := buckets.map fun b =>
          if b.hash == h && cvecEqual b.cvec cv
          then { b with patterns := p :: b.patterns }
          else b
        buildBuckets rest buckets'
      | none =>
        buildBuckets rest ({ hash := h, cvec := cv, patterns := [p] } :: buckets)
  buildBuckets tagged []

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Candidate Pair Generation
-- ══════════════════════════════════════════════════════════════════

/-- Generate all distinct pairs from a list. -/
def allPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: rest => rest.map (fun b => (a, b)) ++ allPairs rest

/-- Generate candidate pairs from a workload using CVec matching.
    1. Evaluate all patterns on `inputs`
    2. Group by CVec
    3. Generate all pairs within each bucket -/
def cvecMatch (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (w : Workload Nat) : List CandidatePair :=
  let buckets := groupByCVec evalOp inputs w.patterns
  buckets.flatMap fun bucket =>
    (allPairs bucket.patterns).map fun (lhs, rhs) =>
      { lhs := lhs, rhs := rhs, cvec := bucket.cvec }

/-- Number of candidate pairs generated. -/
def numCandidates (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (w : Workload Nat) : Nat :=
  (cvecMatch evalOp inputs w).length

-- ══════════════════════════════════════════════════════════════════
-- Section 3b: Multi-Mode Matching (v2.1)
-- ══════════════════════════════════════════════════════════════════

/-- Convert a CVecMatchMode to a DetectedRelation. -/
def modeToRelation (mode : CVecMatchMode) : DetectedRelation :=
  match mode with
  | .eq => .eq
  | .le => .le
  | .dvd => .dvd
  | .modN n => .modN n
  | .conditional => .conditional 0 0

/-- Generate candidate pairs using a specific match mode.
    Unlike `cvecMatch` (equality-only via bucketing), this checks
    all pattern pairs for the given relation mode. -/
def cvecMatchWithMode (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (mode : CVecMatchMode)
    (w : Workload Nat) : List CandidatePair :=
  let cvecs := w.patterns.map (evaluateCVec evalOp inputs)
  let indexed := w.patterns.zip cvecs
  let rec checkPairs : List (Pattern Nat × CVec) → List CandidatePair
    | [] => []
    | (p1, cv1) :: rest =>
      let found := rest.filterMap fun (p2, cv2) =>
        if cvecMatchWith mode cv1 cv2 then
          let rel := match mode with
            | .conditional =>
              let (agree, total) := cvecAgreeFraction cv1 cv2
              DetectedRelation.conditional agree total
            | _ => modeToRelation mode
          some { lhs := p1, rhs := p2, cvec := cv1, relation := rel }
        else none
      found ++ checkPairs rest
  checkPairs indexed

/-- Scan all modes for a pair of CVecs and return the most specific match.
    Priority: eq > dvd > modN > le > conditional.
    (dvd before le because a ∣ b → a ≤ b for Nat, so dvd is stronger.)
    Returns `none` if no relation detected. -/
def detectRelation (cv1 cv2 : CVec) (moduli : List Nat := [2, 3, 5, 7]) :
    Option DetectedRelation :=
  if cvecEqual cv1 cv2 then some .eq
  else if cvecDvd cv1 cv2 then some .dvd
  else
    match moduli.find? (fun n => cvecModEq cv1 cv2 n) with
    | some n => some (.modN n)
    | none =>
      if cvecLe cv1 cv2 then some .le
      else
        let (agree, total) := cvecAgreeFraction cv1 cv2
        if cvecConditionalMatch cv1 cv2 then some (.conditional agree total)
        else none

/-- Generate candidate pairs by scanning ALL relation modes.
    For each pattern pair, detect the strongest relation. -/
def cvecMatchMultiMode (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (w : Workload Nat)
    (moduli : List Nat := [2, 3, 5, 7]) : List CandidatePair :=
  let cvecs := w.patterns.map (evaluateCVec evalOp inputs)
  let indexed := w.patterns.zip cvecs
  let rec checkPairs : List (Pattern Nat × CVec) → List CandidatePair
    | [] => []
    | (p1, cv1) :: rest =>
      let found := rest.filterMap fun (p2, cv2) =>
        (detectRelation cv1 cv2 moduli).map fun rel =>
          { lhs := p1, rhs := p2, cvec := cv1, relation := rel }
      found ++ checkPairs rest
  checkPairs indexed

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Properties
-- ══════════════════════════════════════════════════════════════════

/-- Empty workload produces no candidates. -/
theorem cvecMatch_empty (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) :
    cvecMatch evalOp inputs Workload.empty = [] := by
  simp [cvecMatch, Workload.empty, groupByCVec, groupByCVec.buildBuckets]

/-- allPairs of empty list is empty. -/
theorem allPairs_nil {α : Type} : allPairs ([] : List α) = [] := rfl

/-- allPairs of singleton is empty (no distinct pairs). -/
theorem allPairs_singleton {α : Type} (a : α) : allPairs [a] = [] := by
  simp [allPairs]

/-- cvecMatchWithMode on empty workload produces no candidates. -/
theorem cvecMatchWithMode_empty (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (mode : CVecMatchMode) :
    cvecMatchWithMode evalOp inputs mode Workload.empty = [] := by
  unfold cvecMatchWithMode
  simp only [Workload.empty, List.map_nil, List.zip_nil_left]
  rfl

/-- cvecMatchMultiMode on empty workload produces no candidates. -/
theorem cvecMatchMultiMode_empty (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (moduli : List Nat) :
    cvecMatchMultiMode evalOp inputs Workload.empty moduli = [] := by
  unfold cvecMatchMultiMode
  simp only [Workload.empty, List.map_nil, List.zip_nil_left]
  rfl

/-- detectRelation on identical CVecs returns eq. -/
theorem detectRelation_refl (cv : CVec) (moduli : List Nat) :
    detectRelation cv cv moduli = some .eq := by
  simp [detectRelation, cvecEqual_refl]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- No candidates from empty workload (verified by cvecMatch_empty). -/
example : allPairs ([] : List Nat) = [] := rfl

/-- detectRelation: equal CVecs → eq. -/
example : detectRelation #[1,2,3] #[1,2,3] [] = some .eq := by native_decide

/-- detectRelation: ≤ CVecs → le (when dvd doesn't hold). -/
example : detectRelation #[2,3] #[3,4] [] = some .le := by native_decide

/-- detectRelation: divisibility → dvd. -/
example : detectRelation #[2,3] #[4,9] [] = some .dvd := by native_decide

/-- detectRelation: mod 3 → modN 3. -/
example : detectRelation #[1,4] #[4,7] [3] = some (.modN 3) := by native_decide

end Ruler

end LambdaSat
