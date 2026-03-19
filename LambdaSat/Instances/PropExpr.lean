/-
  LambdaSat — Instances/PropExpr: Propositional Logic Instantiation
  Fase 21 Subfase 1: Concrete instantiation of the e-graph engine
  for propositional logic optimization.

  Provides `PropOp` (propositional operations), `NodeOps PropOp` instance,
  and `NodeSemantics PropOp Bool` instance. This demonstrates that the
  generic e-graph engine can be instantiated for a non-trivial domain.

  Key results:
  - `PropOp` inductive: atom, not, and, or, imp, iff
  - `NodeOps PropOp` instance
  - `NodeSemantics PropOp Bool` instance
  - Smoke tests with #eval
-/
import LambdaSat.Core
import LambdaSat.SemanticSpec

set_option autoImplicit false

namespace LambdaSat

-- ══════════════════════════════════════════════════════════════════
-- Section 1: PropOp — Propositional Logic Operations
-- ══════════════════════════════════════════════════════════════════

/-- Operations for propositional logic.
    Each operation corresponds to a logical connective.
    `atom` represents a named propositional variable. -/
inductive PropOp where
  /-- Atomic proposition (leaf node, identified by index) -/
  | atom (idx : Nat)
  /-- Logical negation: ¬P -/
  | notOp (child : EClassId)
  /-- Logical conjunction: P ∧ Q -/
  | andOp (left right : EClassId)
  /-- Logical disjunction: P ∨ Q -/
  | orOp (left right : EClassId)
  /-- Logical implication: P → Q -/
  | impOp (left right : EClassId)
  /-- Logical bi-implication: P ↔ Q -/
  | iffOp (left right : EClassId)
  deriving Repr, Inhabited, DecidableEq

-- Manual BEq instance matching DecidableEq
instance : BEq PropOp where
  beq a b := decide (a = b)

instance : Hashable PropOp where
  hash
    | .atom i => mixHash 0 (hash i)
    | .notOp a => mixHash 1 (hash a)
    | .andOp a b => mixHash 2 (mixHash (hash a) (hash b))
    | .orOp a b => mixHash 3 (mixHash (hash a) (hash b))
    | .impOp a b => mixHash 4 (mixHash (hash a) (hash b))
    | .iffOp a b => mixHash 5 (mixHash (hash a) (hash b))

-- ══════════════════════════════════════════════════════════════════
-- Section 2: LawfulBEq + LawfulHashable
-- ══════════════════════════════════════════════════════════════════

instance : LawfulBEq PropOp where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

instance : LawfulHashable PropOp where
  hash_eq {a b} h := by
    have := eq_of_beq h
    subst this; rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 3: NodeOps PropOp Instance
-- ══════════════════════════════════════════════════════════════════

private def propChildren : PropOp → List EClassId
  | .atom _ => []
  | .notOp c => [c]
  | .andOp l r => [l, r]
  | .orOp l r => [l, r]
  | .impOp l r => [l, r]
  | .iffOp l r => [l, r]

private def propMapChildren (f : EClassId → EClassId) : PropOp → PropOp
  | .atom i => .atom i
  | .notOp c => .notOp (f c)
  | .andOp l r => .andOp (f l) (f r)
  | .orOp l r => .orOp (f l) (f r)
  | .impOp l r => .impOp (f l) (f r)
  | .iffOp l r => .iffOp (f l) (f r)

private def propReplaceChildren (op : PropOp) (ids : List EClassId) : PropOp :=
  match op, ids with
  | .atom i, _ => .atom i
  | .notOp _, c :: _ => .notOp c
  | .andOp _ _, l :: r :: _ => .andOp l r
  | .orOp _ _, l :: r :: _ => .orOp l r
  | .impOp _ _, l :: r :: _ => .impOp l r
  | .iffOp _ _, l :: r :: _ => .iffOp l r
  | op, _ => op

instance : NodeOps PropOp where
  children := propChildren
  mapChildren := propMapChildren
  replaceChildren := propReplaceChildren

  localCost
    | .atom _ => 1
    | .notOp _ => 1
    | .andOp _ _ => 2
    | .orOp _ _ => 2
    | .impOp _ _ => 3
    | .iffOp _ _ => 4

  mapChildren_children f op := by
    cases op <;> simp [propChildren, propMapChildren]

  mapChildren_id op := by
    cases op <;> simp [propMapChildren]

  replaceChildren_children op ids h := by
    cases op with
    | atom idx => simp [propChildren] at h; simp [propChildren, propReplaceChildren, h]
    | notOp c =>
      simp [propChildren] at h
      match ids, h with
      | [x], _ => simp [propReplaceChildren, propChildren]
    | andOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propChildren]
    | orOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propChildren]
    | impOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propChildren]
    | iffOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propChildren]

  replaceChildren_sameShape op ids h := by
    cases op with
    | atom idx => simp [propChildren] at h; simp [propReplaceChildren, propMapChildren]
    | notOp c =>
      simp [propChildren] at h
      match ids, h with
      | [x], _ => simp [propReplaceChildren, propMapChildren]
    | andOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propMapChildren]
    | orOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propMapChildren]
    | impOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propMapChildren]
    | iffOp l r =>
      simp [propChildren] at h
      match ids, h with
      | [x, y], _ => simp [propReplaceChildren, propMapChildren]

  mapChildren_replaceChildren f op := by
    cases op <;> simp [propChildren, propMapChildren, propReplaceChildren]

-- ══════════════════════════════════════════════════════════════════
-- Section 4: PropVal + NodeSemantics
-- ══════════════════════════════════════════════════════════════════

/-- Semantic domain for propositional logic: Bool. -/
abbrev PropVal := Bool

private def propEvalOp (op : PropOp) (env : Nat → PropVal) (v : EClassId → PropVal) : PropVal :=
  match op with
  | .atom i => env i
  | .notOp c => !v c
  | .andOp l r => v l && v r
  | .orOp l r => v l || v r
  | .impOp l r => !v l || v r
  | .iffOp l r => (v l == v r)

/-- Evaluate a propositional operation given:
    - `env`: maps external input indices to Bool
    - `v`: maps e-class IDs to Bool values -/
instance : NodeSemantics PropOp PropVal where
  evalOp := propEvalOp

  evalOp_ext op _env v v' h := by
    cases op with
    | atom _ => rfl
    | notOp c =>
      simp only [propEvalOp]
      have := h c (by show c ∈ propChildren (PropOp.notOp c); simp [propChildren])
      rw [this]
    | andOp l r =>
      simp only [propEvalOp]
      have hl := h l (by show l ∈ propChildren (PropOp.andOp l r); simp [propChildren])
      have hr := h r (by show r ∈ propChildren (PropOp.andOp l r); simp [propChildren])
      rw [hl, hr]
    | orOp l r =>
      simp only [propEvalOp]
      have hl := h l (by show l ∈ propChildren (PropOp.orOp l r); simp [propChildren])
      have hr := h r (by show r ∈ propChildren (PropOp.orOp l r); simp [propChildren])
      rw [hl, hr]
    | impOp l r =>
      simp only [propEvalOp]
      have hl := h l (by show l ∈ propChildren (PropOp.impOp l r); simp [propChildren])
      have hr := h r (by show r ∈ propChildren (PropOp.impOp l r); simp [propChildren])
      rw [hl, hr]
    | iffOp l r =>
      simp only [propEvalOp]
      have hl := h l (by show l ∈ propChildren (PropOp.iffOp l r); simp [propChildren])
      have hr := h r (by show r ∈ propChildren (PropOp.iffOp l r); simp [propChildren])
      rw [hl, hr]

  evalOp_mapChildren f op _env v := by
    cases op <;> rfl

  evalOp_skeleton op₁ op₂ env v₁ v₂ hskel hvals := by
    cases op₁ <;> cases op₂ <;>
      simp only [NodeOps.mapChildren, propMapChildren] at hskel <;>
      try (exact absurd hskel PropOp.noConfusion)
    case atom.atom =>
      injection hskel with hIdx
      simp only [propEvalOp]; rw [hIdx]
    case notOp.notOp c₁ c₂ =>
      simp only [propEvalOp]
      have h0 := hvals 0 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      simp only [NodeOps.children, propChildren, List.getElem_cons_zero] at h0; rw [h0]
    case andOp.andOp l₁ r₁ l₂ r₂ =>
      simp only [propEvalOp]
      have h0 := hvals 0 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      have h1 := hvals 1 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      simp only [NodeOps.children, propChildren, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      rw [h0, h1]
    case orOp.orOp l₁ r₁ l₂ r₂ =>
      simp only [propEvalOp]
      have h0 := hvals 0 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      have h1 := hvals 1 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      simp only [NodeOps.children, propChildren, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      rw [h0, h1]
    case impOp.impOp l₁ r₁ l₂ r₂ =>
      simp only [propEvalOp]
      have h0 := hvals 0 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      have h1 := hvals 1 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      simp only [NodeOps.children, propChildren, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      rw [h0, h1]
    case iffOp.iffOp l₁ r₁ l₂ r₂ =>
      simp only [propEvalOp]
      have h0 := hvals 0 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      have h1 := hvals 1 (by simp [NodeOps.children, propChildren]) (by simp [NodeOps.children, propChildren])
      simp only [NodeOps.children, propChildren, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1
      rw [h0, h1]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Atom children are empty. -/
example : NodeOps.children (PropOp.atom 0) = [] := rfl

/-- And has two children. -/
example : NodeOps.children (PropOp.andOp 1 2) = [1, 2] := rfl

/-- Not has one child. -/
example : NodeOps.children (PropOp.notOp 3) = [3] := rfl

/-- mapChildren on atom is identity. -/
example : NodeOps.mapChildren (· + 1) (PropOp.atom 5) = PropOp.atom 5 := rfl

/-- mapChildren on and increments children. -/
example : NodeOps.mapChildren (· + 1) (PropOp.andOp 1 2) = PropOp.andOp 2 3 := rfl

/-- Semantic evaluation: atom reads from env. -/
example : NodeSemantics.evalOp (PropOp.atom 0) (fun _ => true) (fun _ => false) = true := rfl

/-- Semantic evaluation: not negates child. -/
example : NodeSemantics.evalOp (PropOp.notOp 0) (fun _ => false) (fun _ => true) = false := rfl

/-- Semantic evaluation: and conjoins children. -/
example : NodeSemantics.evalOp (PropOp.andOp 0 1)
    (fun _ => false) (fun c => c == 0) = false := rfl

#eval!
  let op := PropOp.andOp 0 1
  let children := NodeOps.children op
  let cost := NodeOps.localCost op
  s!"PropOp.andOp: children={children}, cost={cost}"

end LambdaSat
