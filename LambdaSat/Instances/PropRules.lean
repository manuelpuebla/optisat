/-
  LambdaSat — Instances/PropRules: Propositional Logic Rewrite Rules
  Fase 21 Subfase 2: Named rewrite rules for propositional logic.

  Provides sound rewrite rules for standard propositional identities:
  - doubleNeg: ¬¬P ↔ P
  - deMorgan1: ¬(P ∧ Q) ↔ ¬P ∨ ¬Q
  - deMorgan2: ¬(P ∨ Q) ↔ ¬P ∧ ¬Q
  - andComm: P ∧ Q ↔ Q ∧ P
  - orComm: P ∨ Q ↔ Q ∨ P

  Each rule is constructed as a `RewriteRule PropOp` (syntactic) for
  e-matching. The semantic soundness proofs are in the Bool domain.

  Key results:
  - 5+ RewriteRule PropOp definitions
  - Smoke tests verifying rule structure
-/
import LambdaSat.Instances.PropExpr
import LambdaSat.EMatch

set_option autoImplicit false

namespace LambdaSat

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Pattern Helpers
-- ══════════════════════════════════════════════════════════════════

/-- Pattern variable shorthand. -/
private def pvar (n : Nat) : Pattern PropOp := Pattern.patVar n

/-- NOT pattern: ¬(child). Child is a pattern variable at slot 0. -/
private def patNot (child : Pattern PropOp) : Pattern PropOp :=
  Pattern.node (PropOp.notOp 0) [child]

/-- AND pattern: left ∧ right. -/
private def patAnd (left right : Pattern PropOp) : Pattern PropOp :=
  Pattern.node (PropOp.andOp 0 0) [left, right]

/-- OR pattern: left ∨ right. -/
private def patOr (left right : Pattern PropOp) : Pattern PropOp :=
  Pattern.node (PropOp.orOp 0 0) [left, right]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Rewrite Rules
-- ══════════════════════════════════════════════════════════════════

/-- Double negation elimination: ¬¬P → P.
    Pattern: not(not(?0)) → ?0 -/
def doubleNegRule : RewriteRule PropOp where
  name := "doubleNeg"
  lhs := patNot (patNot (pvar 0))
  rhs := pvar 0

/-- De Morgan's law 1 (forward): ¬(P ∧ Q) → ¬P ∨ ¬Q.
    Pattern: not(and(?0, ?1)) → or(not(?0), not(?1)) -/
def deMorgan1Rule : RewriteRule PropOp where
  name := "deMorgan1"
  lhs := patNot (patAnd (pvar 0) (pvar 1))
  rhs := patOr (patNot (pvar 0)) (patNot (pvar 1))

/-- De Morgan's law 2 (forward): ¬(P ∨ Q) → ¬P ∧ ¬Q.
    Pattern: not(or(?0, ?1)) → and(not(?0), not(?1)) -/
def deMorgan2Rule : RewriteRule PropOp where
  name := "deMorgan2"
  lhs := patNot (patOr (pvar 0) (pvar 1))
  rhs := patAnd (patNot (pvar 0)) (patNot (pvar 1))

/-- Commutativity of AND: P ∧ Q → Q ∧ P.
    Pattern: and(?0, ?1) → and(?1, ?0) -/
def andCommRule : RewriteRule PropOp where
  name := "andComm"
  lhs := patAnd (pvar 0) (pvar 1)
  rhs := patAnd (pvar 1) (pvar 0)

/-- Commutativity of OR: P ∨ Q → Q ∨ P.
    Pattern: or(?0, ?1) → or(?1, ?0) -/
def orCommRule : RewriteRule PropOp where
  name := "orComm"
  lhs := patOr (pvar 0) (pvar 1)
  rhs := patOr (pvar 1) (pvar 0)

/-- Idempotence of AND: P ∧ P → P.
    Pattern: and(?0, ?0) → ?0 -/
def andIdempRule : RewriteRule PropOp where
  name := "andIdemp"
  lhs := patAnd (pvar 0) (pvar 0)
  rhs := pvar 0

/-- Idempotence of OR: P ∨ P → P.
    Pattern: or(?0, ?0) → ?0 -/
def orIdempRule : RewriteRule PropOp where
  name := "orIdemp"
  lhs := patOr (pvar 0) (pvar 0)
  rhs := pvar 0

/-- The standard propositional logic rule set. -/
def propRules : List (RewriteRule PropOp) :=
  [doubleNegRule, deMorgan1Rule, deMorgan2Rule,
   andCommRule, orCommRule, andIdempRule, orIdempRule]

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Semantic Soundness (Bool domain)
-- ══════════════════════════════════════════════════════════════════

/-- Double negation is semantically sound in Bool. -/
theorem doubleNeg_sound (b : Bool) : (!!b) = b := by
  cases b <;> rfl

/-- De Morgan 1 is semantically sound in Bool. -/
theorem deMorgan1_sound (a b : Bool) :
    (!(a && b)) = (!a || !b) := by
  cases a <;> cases b <;> rfl

/-- De Morgan 2 is semantically sound in Bool. -/
theorem deMorgan2_sound (a b : Bool) :
    (!(a || b)) = (!a && !b) := by
  cases a <;> cases b <;> rfl

/-- AND commutativity is semantically sound in Bool. -/
theorem andComm_sound (a b : Bool) : (a && b) = (b && a) := by
  cases a <;> cases b <;> rfl

/-- OR commutativity is semantically sound in Bool. -/
theorem orComm_sound (a b : Bool) : (a || b) = (b || a) := by
  cases a <;> cases b <;> rfl

/-- AND idempotence is semantically sound in Bool. -/
theorem andIdemp_sound (a : Bool) : (a && a) = a := by
  cases a <;> rfl

/-- OR idempotence is semantically sound in Bool. -/
theorem orIdemp_sound (a : Bool) : (a || a) = a := by
  cases a <;> rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- The rule set has 7 rules. -/
example : propRules.length = 7 := rfl

/-- Double negation rule LHS is a nested NOT pattern. -/
example : doubleNegRule.lhs = patNot (patNot (pvar 0)) := rfl

/-- Double negation rule RHS is just a variable. -/
example : doubleNegRule.rhs = pvar 0 := rfl

#eval!
  let n := propRules.length
  s!"Propositional logic rules: {n} rules"

end LambdaSat
