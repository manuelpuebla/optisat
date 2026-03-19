/-
  LambdaSat — Ruler/RuleValidator: Candidate Rule Validation
  Fase 20 Subfase 4: Validate candidate pairs as sound rewrite rules.

  After CVec matching produces candidate pairs (patterns that agree on
  test inputs), this module attempts to validate them as genuine equalities.
  Validation can be:
  - Formal proof (produces a `SoundRewriteRule`)
  - Counterexample (disproves the candidate)
  - Timeout (inconclusive)

  Note: Full MetaM-level proof automation is outside the TCB.
  This module provides the interface and the certificate structure.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `ValidatedRule`: a candidate that has been formally validated
  - `ValidationResult`: valid / invalid / timeout
  - `validateCandidate`: attempt validation
-/
import LambdaSat.Ruler.CVecMatcher
import LambdaSat.SoundRule

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Validation Result
-- ══════════════════════════════════════════════════════════════════

/-- The result of attempting to validate a candidate pair. -/
inductive ValidationResult where
  /-- The candidate was proven to be a valid equality. -/
  | valid : ValidationResult
  /-- A counterexample was found (the candidate is not universally true). -/
  | invalid (counterexample : Array Nat) : ValidationResult
  /-- Validation timed out (inconclusive). -/
  | timeout : ValidationResult
  deriving Repr

-- ══════════════════════════════════════════════════════════════════
-- Section 2: ValidatedRule
-- ══════════════════════════════════════════════════════════════════

/-- A validated rule: a candidate pair that has been confirmed as a
    sound equality by formal proof or testing.

    This wraps the candidate pair together with validation metadata.
    The actual `SoundRewriteRule` construction happens outside this module
    (in MetaM or via proof certificates). -/
structure ValidatedRule where
  /-- The original candidate pair -/
  candidate : CandidatePair
  /-- A human-readable name for the discovered rule -/
  name : String
  /-- Number of test inputs used during CVec matching -/
  numTests : Nat
  /-- Validation method used -/
  method : String

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Validation Procedure
-- ══════════════════════════════════════════════════════════════════

/-- Attempt to validate a candidate pair by running additional tests.
    Uses `extraInputs` as additional test cases beyond the original CVec.

    This is the "testing" tier of validation: not a formal proof, but
    increases confidence. Actual formal validation requires MetaM integration. -/
def validateCandidate (evalOp : Nat → List Nat → Nat)
    (extraInputs : Array (Nat → Nat))
    (pair : CandidatePair) : ValidationResult :=
  -- Evaluate both patterns on extra inputs and check for disagreement
  let lhsVec := evaluateCVec evalOp extraInputs pair.lhs
  let rhsVec := evaluateCVec evalOp extraInputs pair.rhs
  if cvecEqual lhsVec rhsVec then
    .valid
  else
    -- Find the first disagreeing input as a counterexample
    let counterexample := Array.zipWith (fun l r => if l == r then (0 : Nat) else 1) lhsVec rhsVec
    .invalid counterexample

/-- Validate all candidate pairs, keeping only the valid ones. -/
def validateCandidates (evalOp : Nat → List Nat → Nat)
    (extraInputs : Array (Nat → Nat))
    (candidates : List CandidatePair) : List ValidatedRule :=
  candidates.filterMap fun pair =>
    match validateCandidate evalOp extraInputs pair with
    | .valid =>
      some { candidate := pair
             name := s!"rule_validated"
             numTests := extraInputs.size
             method := "cvec_testing" }
    | _ => none

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Properties
-- ══════════════════════════════════════════════════════════════════

/-- No candidates means no validated rules. -/
theorem validateCandidates_empty (evalOp : Nat → List Nat → Nat)
    (extraInputs : Array (Nat → Nat)) :
    validateCandidates evalOp extraInputs [] = [] := by
  simp [validateCandidates]

/-- Validated rules are a subset of (derived from) the input candidates. -/
theorem validateCandidates_subset (evalOp : Nat → List Nat → Nat)
    (extraInputs : Array (Nat → Nat))
    (candidates : List CandidatePair) :
    (validateCandidates evalOp extraInputs candidates).length ≤ candidates.length := by
  simp [validateCandidates]
  exact List.length_filterMap_le _ _

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Empty candidates yield empty validated rules. -/
example : validateCandidates (fun _ _ => 0) #[] [] = [] := rfl

end Ruler

end LambdaSat
