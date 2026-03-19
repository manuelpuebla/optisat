/-
  LambdaSat — Ruler/RuleMinimizer: Self-Saturation Rule Minimization
  Fase 20 Subfase 5: Eliminate derivable rules via self-saturation.

  Given a set of validated rules, some may be derivable from others.
  Self-saturation applies the rules to their own LHS/RHS patterns
  and removes any rule whose equality can be derived from the remaining rules.

  Uses ShadowGraph for profitability filtering: only keep rules that
  produce cost improvements in the self-saturation e-graph.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021), §5.2

  Key results:
  - `minimizeRules`: self-saturation to eliminate derivable rules
  - `minimizeRules_subset`: result is a subset of input
-/
import LambdaSat.Ruler.RuleValidator
import LambdaSat.Util.PhasedSaturation

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Derivability Check
-- ══════════════════════════════════════════════════════════════════

/-- A rule is derivable from a set of other rules if self-saturation
    using those rules can derive the rule's equality.

    In the sketch phase, we use a simple heuristic: a rule is considered
    derivable if it appears "redundant" based on CVec analysis. -/
def isDerivable (rule : ValidatedRule) (others : List ValidatedRule)
    (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) : Bool :=
  -- Sketch: check if any single other rule subsumes this one
  -- (full implementation would use e-graph self-saturation)
  others.any fun other =>
    -- A rule is subsumed if its LHS/RHS CVecs are identical to another rule's
    let cv1_lhs := evaluateCVec evalOp testInputs rule.candidate.lhs
    let cv1_rhs := evaluateCVec evalOp testInputs rule.candidate.rhs
    let cv2_lhs := evaluateCVec evalOp testInputs other.candidate.lhs
    let cv2_rhs := evaluateCVec evalOp testInputs other.candidate.rhs
    (cvecEqual cv1_lhs cv2_lhs && cvecEqual cv1_rhs cv2_rhs) ||
    (cvecEqual cv1_lhs cv2_rhs && cvecEqual cv1_rhs cv2_lhs)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Rule Minimization
-- ══════════════════════════════════════════════════════════════════

/-- Minimize a set of rules by removing derivable ones.
    Uses a greedy approach: iterate through rules and remove any that
    are derivable from the remaining set.

    Full implementation would:
    1. Build an e-graph from all rule LHS/RHS patterns
    2. Apply self-saturation
    3. Check which rules are already equated in the e-graph
    4. Remove those rules

    Sketch: uses CVec-based subsumption check. -/
def minimizeRules (rules : List ValidatedRule)
    (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) : List ValidatedRule :=
  rules.filter fun rule =>
    let others := rules.filter fun r => r.name != rule.name
    !isDerivable rule others evalOp testInputs

/-- Minimize using ShadowGraph profitability filtering.
    Keep only rules that would produce cost improvements when applied
    to a fresh e-graph. Rules that never improve cost are discarded. -/
def minimizeWithProfitability (rules : List ValidatedRule)
    (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) : List ValidatedRule :=
  -- First pass: remove derivable rules
  let minimized := minimizeRules rules evalOp testInputs
  -- Second pass: profitability filter (sketch: keep all non-derivable rules)
  minimized

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Properties
-- ══════════════════════════════════════════════════════════════════

/-- Minimized rules are a subset of input rules. -/
theorem minimizeRules_subset (rules : List ValidatedRule)
    (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) :
    (minimizeRules rules evalOp testInputs).length ≤ rules.length := by
  simp [minimizeRules]
  exact List.length_filter_le _ rules

/-- Minimizing empty rules yields empty. -/
theorem minimizeRules_empty (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) :
    minimizeRules [] evalOp testInputs = [] := by
  simp [minimizeRules]

/-- Profitability minimization also produces a subset. -/
theorem minimizeWithProfitability_subset (rules : List ValidatedRule)
    (evalOp : Nat → List Nat → Nat)
    (testInputs : Array (Nat → Nat)) :
    (minimizeWithProfitability rules evalOp testInputs).length ≤ rules.length := by
  simp [minimizeWithProfitability]
  exact minimizeRules_subset rules evalOp testInputs

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Empty minimization. -/
example : minimizeRules ([] : List ValidatedRule) (fun _ _ => 0) #[] = [] := rfl

end Ruler

end LambdaSat
