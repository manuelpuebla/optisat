/-
  LambdaSat — Ruler/CVecEngine: Characteristic Vector Evaluation
  Fase 20 Subfase 2: CVec computation for pattern matching.

  A CVec (characteristic vector) is the result of evaluating a pattern
  on m concrete inputs. Two patterns with identical CVecs are candidates
  for equality rules (they agree on all test inputs).

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `CVec`: Array Nat (evaluation on m concrete inputs)
  - `evaluateCVec`: evaluate a pattern on m inputs
  - `cvecEqual`: check if two CVecs are identical
  - `cvecEqual_refl`: reflexivity of CVec equality
-/
import LambdaSat.Ruler.TermEnumerator

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: CVec Type
-- ══════════════════════════════════════════════════════════════════

/-- A characteristic vector: the result of evaluating a pattern on
    m concrete inputs. Each entry is the evaluation result (as a Nat hash). -/
abbrev CVec := Array Nat

/-- Empty characteristic vector. -/
def CVec.empty : CVec := #[]

/-- Length of a characteristic vector (number of test inputs). -/
def CVec.len (cv : CVec) : Nat := cv.size

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pattern Evaluation on Concrete Inputs
-- ══════════════════════════════════════════════════════════════════

/-- Evaluate a pattern on a single concrete input (variable assignment).
    Uses a simple evaluator that maps operations to Nat → Nat functions.
    `evalOp` maps an op + child values to a result value.
    `varAssign` maps variable IDs to concrete Nat values. -/
def evaluatePattern (evalOp : Nat → List Nat → Nat) (varAssign : Nat → Nat) :
    Pattern Nat → Nat
  | .patVar v => varAssign v
  | .node op children =>
    let childVals := children.map (evaluatePattern evalOp varAssign)
    evalOp op childVals

/-- Evaluate a pattern on m concrete inputs, producing a CVec.
    Each element of `inputs` is a variable assignment (Nat → Nat). -/
def evaluateCVec (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (pattern : Pattern Nat) : CVec :=
  inputs.map (fun assign => evaluatePattern evalOp assign pattern)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: CVec Comparison
-- ══════════════════════════════════════════════════════════════════

/-- Check if two CVecs are identical (element-wise). -/
def cvecEqual (cv1 cv2 : CVec) : Bool :=
  cv1.toList == cv2.toList

/-- Hash a CVec for grouping into buckets. -/
def cvecHash (cv : CVec) : UInt64 :=
  cv.foldl (fun acc x => acc ^^^ hash x) 0

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Basic Properties
-- ══════════════════════════════════════════════════════════════════

/-- CVec equality is reflexive. -/
theorem cvecEqual_refl (cv : CVec) : cvecEqual cv cv = true := by
  simp [cvecEqual]

/-- Empty CVecs are always equal. -/
theorem cvecEqual_empty : cvecEqual CVec.empty CVec.empty = true := by
  simp [cvecEqual, CVec.empty]

/-- CVec equality is symmetric. -/
theorem cvecEqual_symm (cv1 cv2 : CVec) :
    cvecEqual cv1 cv2 = cvecEqual cv2 cv1 := by
  simp [cvecEqual]
  exact BEq.comm

/-- Evaluating on 0 inputs produces an empty CVec. -/
theorem evaluateCVec_empty (evalOp : Nat → List Nat → Nat) (p : Pattern Nat) :
    (evaluateCVec evalOp #[] p).size = 0 := by
  simp [evaluateCVec]

/-- CVec length equals number of inputs. -/
theorem evaluateCVec_len (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (p : Pattern Nat) :
    (evaluateCVec evalOp inputs p).size = inputs.size := by
  simp [evaluateCVec]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Evaluating a variable pattern returns the variable's value. -/
example : evaluatePattern (fun _ _ => 0) (fun v => v + 1) (.patVar 3) = 4 := by
  native_decide

/-- Empty CVec has length 0. -/
example : CVec.empty.size = 0 := rfl

end Ruler

end LambdaSat
