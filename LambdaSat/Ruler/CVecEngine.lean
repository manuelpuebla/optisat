/-
  LambdaSat — Ruler/CVecEngine: Characteristic Vector Evaluation
  Fase 20 Subfase 2: CVec computation for pattern matching.
  Fase 14 (v2.1): CVecMatchMode generalization for non-equality relations.

  A CVec (characteristic vector) is the result of evaluating a pattern
  on m concrete inputs. Two patterns with identical CVecs are candidates
  for equality rules (they agree on all test inputs).

  v2.1 extension: `CVecMatchMode` allows matching for ≤, ∣, mod, and
  conditional relations — not just equality.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `CVec`: Array Nat (evaluation on m concrete inputs)
  - `evaluateCVec`: evaluate a pattern on m inputs
  - `CVecMatchMode`: enum of match modes (eq/le/dvd/modN/conditional)
  - `cvecMatchWith`: dispatch to the right comparison by mode
  - `cvecEqual`: check if two CVecs are identical (eq mode)
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
-- Section 3: CVec Comparison Modes
-- ══════════════════════════════════════════════════════════════════

/-- Match mode for CVec comparison. Determines what relation is being
    tested between two patterns based on their characteristic vectors. -/
inductive CVecMatchMode where
  /-- Equality: `∀ i, cv1[i] = cv2[i]` → candidate `lhs = rhs` -/
  | eq : CVecMatchMode
  /-- Less-or-equal: `∀ i, cv1[i] ≤ cv2[i]` → candidate `lhs ≤ rhs` -/
  | le : CVecMatchMode
  /-- Divisibility: `∀ i, cv1[i] ∣ cv2[i]` → candidate `lhs ∣ rhs` -/
  | dvd : CVecMatchMode
  /-- Modular congruence: `∀ i, cv1[i] % n = cv2[i] % n` → candidate `lhs ≡ rhs (mod n)` -/
  | modN (n : Nat) : CVecMatchMode
  /-- Conditional equality: positions where CVecs agree identify where
      `P(input) → lhs = rhs` holds. The precondition P is inferred from
      disagreeing positions. -/
  | conditional : CVecMatchMode
  deriving Repr, BEq

/-- Check if two CVecs are identical (element-wise). -/
def cvecEqual (cv1 cv2 : CVec) : Bool :=
  cv1.toList == cv2.toList

/-- Check if cv1 ≤ cv2 element-wise. -/
def cvecLe (cv1 cv2 : CVec) : Bool :=
  cv1.size == cv2.size &&
  (cv1.zipWith (fun a b => decide (a ≤ b)) cv2).all id

/-- Check if cv1 ∣ cv2 element-wise (each element of cv1 divides the
    corresponding element of cv2). -/
def cvecDvd (cv1 cv2 : CVec) : Bool :=
  cv1.size == cv2.size &&
  (cv1.zipWith (fun a b => b % a == 0) cv2).all id

/-- Check if cv1 ≡ cv2 (mod n) element-wise. -/
def cvecModEq (cv1 cv2 : CVec) (n : Nat) : Bool :=
  n > 0 &&
  cv1.size == cv2.size &&
  (cv1.zipWith (fun a b => a % n == b % n) cv2).all id

/-- Fraction of positions where cv1 and cv2 agree (for conditional mode).
    Returns (agreeing, total). -/
def cvecAgreeFraction (cv1 cv2 : CVec) : Nat × Nat :=
  let total := min cv1.size cv2.size
  let agree := (cv1.zipWith (fun a b => if a == b then (1 : Nat) else 0) cv2).foldl (· + ·) 0
  (agree, total)

/-- Check conditional match: at least `threshold` fraction of positions agree.
    Default threshold: > 50% agreement (not all, which would be eq mode). -/
def cvecConditionalMatch (cv1 cv2 : CVec) (threshold : Nat := 50) : Bool :=
  let (agree, total) := cvecAgreeFraction cv1 cv2
  total > 0 && agree * 100 ≥ threshold * total && agree < total

/-- Match two CVecs using the specified mode. -/
def cvecMatchWith (mode : CVecMatchMode) (cv1 cv2 : CVec) : Bool :=
  match mode with
  | .eq => cvecEqual cv1 cv2
  | .le => cvecLe cv1 cv2
  | .dvd => cvecDvd cv1 cv2
  | .modN n => cvecModEq cv1 cv2 n
  | .conditional => cvecConditionalMatch cv1 cv2

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

/-- cvecMatchWith in eq mode is exactly cvecEqual. -/
theorem cvecMatchWith_eq (cv1 cv2 : CVec) :
    cvecMatchWith .eq cv1 cv2 = cvecEqual cv1 cv2 := rfl

/-- cvecMatchWith in le mode is exactly cvecLe. -/
theorem cvecMatchWith_le (cv1 cv2 : CVec) :
    cvecMatchWith .le cv1 cv2 = cvecLe cv1 cv2 := rfl

/-- cvecMatchWith in dvd mode is exactly cvecDvd. -/
theorem cvecMatchWith_dvd (cv1 cv2 : CVec) :
    cvecMatchWith .dvd cv1 cv2 = cvecDvd cv1 cv2 := rfl

/-- cvecMatchWith in modN mode is exactly cvecModEq. -/
theorem cvecMatchWith_modN (cv1 cv2 : CVec) (n : Nat) :
    cvecMatchWith (.modN n) cv1 cv2 = cvecModEq cv1 cv2 n := rfl

/-- cvecMatchWith in eq mode is reflexive. -/
theorem cvecMatchWith_eq_refl (cv : CVec) :
    cvecMatchWith .eq cv cv = true := by
  simp [cvecMatchWith, cvecEqual]

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

/-- CVec ≤ matching: [1,2,3] ≤ [2,3,4] -/
example : cvecLe #[1,2,3] #[2,3,4] = true := by native_decide

/-- CVec ≤ matching fails: [3,2,1] ≤ [1,2,3] -/
example : cvecLe #[3,2,1] #[1,2,3] = false := by native_decide

/-- CVec mod matching: [1,4,7] ≡ [1,1,1] (mod 3) -/
example : cvecModEq #[1,4,7] #[1,1,1] 3 = true := by native_decide

/-- CVec divisibility: [2,3] ∣ [4,9] -/
example : cvecDvd #[2,3] #[4,9] = true := by native_decide

end Ruler

end LambdaSat
