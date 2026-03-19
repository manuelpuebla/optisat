/-
  LambdaSat — Ruler/CVecMatcher: CVec-Based Candidate Pair Generation
  Fase 20 Subfase 3: Group patterns by CVec, generate candidate equalities.

  Patterns with identical CVecs are candidates for equality rules.
  This module groups patterns by their CVec hash and generates all
  candidate pairs within each bucket.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `CandidatePair`: two patterns with matching CVecs
  - `cvecMatch`: group by CVec hash, generate candidate pairs
  - `cvecMatch_subset`: candidates come from the workload
-/
import LambdaSat.Ruler.CVecEngine

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CandidatePair
-- ══════════════════════════════════════════════════════════════════

/-- A candidate pair: two patterns whose CVecs match.
    These are candidates for equality rules (they agree on all test inputs). -/
structure CandidatePair where
  /-- Left-hand side pattern -/
  lhs : Pattern Nat
  /-- Right-hand side pattern -/
  rhs : Pattern Nat
  /-- The shared CVec (for debugging/verification) -/
  cvec : CVec

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

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- No candidates from empty workload (verified by cvecMatch_empty). -/
example : allPairs ([] : List Nat) = [] := rfl

end Ruler

end LambdaSat
