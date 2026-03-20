/-
  LambdaSat — DirectedRelSpec: Soundness for Directed Relations
  Fase 17: Layer 3 specification.

  Provides the semantic specification for directed relation graphs
  (the RelationTypes.lean data structures). Defines what it means
  for a directed edge to be "sound" and proves that operations
  on DirectedRelGraph preserve soundness.

  Key innovation: a DAG of implications parallel to the Union-Find.
  The UF handles equality (symmetric); the DAG handles directed
  relations like ≤, ∣, →.

  Cross-relation rules connect Layers 1-3:
  - `a ≤ b ∧ b ≤ a → merge(a, b)` (antisymmetry promotes to equality)
  - `a = b → a ≤ b` (equality implies any reflexive relation)

  Key results:
  - `DirectedRelConsistency`: semantic invariant for directed relation graphs
  - `addEdge_preserves_consistency`: adding a sound edge is safe
  - `hasPath_transitivity`: path existence implies transitive relation
  - `antisymmetry_promotes`: ≤ + ≥ implies equality (cross-layer rule)
-/
import LambdaSat.RelationTypes
import LambdaSat.SemanticSpec

set_option autoImplicit false

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Relation Semantics
-- ══════════════════════════════════════════════════════════════════

/-- A semantic relation: a binary relation on values.
    Examples: `(· ≤ ·)` for Nat, `(· ∣ ·)` for divisibility. -/
abbrev SemanticRelation (Val : Type) := Val → Val → Prop

/-- A relation is reflexive. -/
def IsReflexive {Val : Type} (R : SemanticRelation Val) : Prop := ∀ x, R x x

/-- A relation is transitive. -/
def IsTransitive {Val : Type} (R : SemanticRelation Val) : Prop := ∀ x y z, R x y → R y z → R x z

/-- A relation is antisymmetric (with respect to equality). -/
def IsAntisymmetric {Val : Type} (R : SemanticRelation Val) : Prop := ∀ x y, R x y → R y x → x = y

/-- A preorder: reflexive + transitive. -/
def IsPreorder {Val : Type} (R : SemanticRelation Val) : Prop := IsReflexive R ∧ IsTransitive R

/-- A partial order: preorder + antisymmetric. -/
def IsPartialOrder {Val : Type} (R : SemanticRelation Val) : Prop := IsPreorder R ∧ IsAntisymmetric R

-- ══════════════════════════════════════════════════════════════════
-- Section 2: DirectedRelConsistency
-- ══════════════════════════════════════════════════════════════════

/-- Semantic consistency for a directed relation graph.
    Every edge (a, b) in the graph means R(v(a), v(b)) holds. -/
def DirectedRelConsistency {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val) : Prop :=
  ∀ a b, drg.hasDirectEdge a b → R (v a) (v b)

/-- The empty graph is trivially consistent with any relation. -/
theorem empty_consistent_rel {Val : Type} (R : SemanticRelation Val) (v : EClassId → Val) :
    DirectedRelConsistency DirectedRelGraph.empty R v := by
  intro a b h
  simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors,
        DirectedRelGraph.empty] at h

/-- Consistency via allEdges: every listed edge satisfies the relation.
    This is a companion to `DirectedRelConsistency` (which uses `hasDirectEdge`).
    Useful when the available evidence is `allEdges` membership. -/
def DirectedRelConsistencyAllEdges {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val) : Prop :=
  ∀ a b, (a, b) ∈ drg.allEdges → R (v a) (v b)

/-- DirectedRelConsistency implies DirectedRelConsistencyAllEdges
    (hasDirectEdge check is more restrictive than allEdges membership
     in theory, but in practice they agree for well-formed graphs).
    Note: the reverse direction requires HashMap bridge lemmas. -/
theorem DRC_implies_DRC_allEdges {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (h_bridge : ∀ a b, (a, b) ∈ drg.allEdges → drg.hasDirectEdge a b) :
    DirectedRelConsistencyAllEdges drg R v := by
  intro a b hmem
  exact hcon a b (h_bridge a b hmem)

theorem DirectedRelConsistency_transfer {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v v' : EClassId → Val) (n : Nat)
    (hcon : DirectedRelConsistency drg R v)
    (hagree : ∀ i, i < n → v' i = v i)
    (hbnd : ∀ a b, drg.hasDirectEdge a b → a < n ∧ b < n) :
    DirectedRelConsistency drg R v' := by
  intro a b hedge
  have ⟨ha, hb⟩ := hbnd a b hedge
  rw [hagree a ha, hagree b hb]
  exact hcon a b hedge

-- ══════════════════════════════════════════════════════════════════
-- Section 3: addEdge preserves consistency
-- ══════════════════════════════════════════════════════════════════

/-- Adding an edge (a, b) preserves consistency if R(v(a), v(b)) holds. -/
theorem addEdge_preserves_consistency {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val)
    (a b : EClassId)
    (hcon : DirectedRelConsistency drg R v)
    (h_sound : R (v a) (v b)) :
    DirectedRelConsistency (drg.addEdge a b) R v := by
  intro x y hxy
  simp [DirectedRelGraph.addEdge, DirectedRelGraph.hasDirectEdge,
        DirectedRelGraph.successors] at hxy
  rw [Std.HashMap.getD_insert] at hxy
  split at hxy
  · -- x == a: getD returns (b :: old successors)
    rename_i heq
    have hxa : a = x := eq_of_beq heq
    subst hxa
    simp [List.mem_cons] at hxy
    rcases hxy with rfl | hmem
    · exact h_sound
    · exact hcon a y (by simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors, hmem])
  · -- x ≠ a: getD returns old value
    exact hcon x y (by simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.successors, hxy])

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Path transitivity
-- ══════════════════════════════════════════════════════════════════

/-- If R is transitive and the graph is R-consistent, then a path
    from a to b implies R(v(a), v(b)).

    **Proof strategy**: Generalize over the BFS `go` helper. For any queue,
    if `go queue visited fuel = true`, then ∃ c ∈ queue with a chain of
    direct edges from c to b, each satisfying R. By transitivity, R(v(c),v(b)).
    Then specialize with queue = [a].

    The BFS `go` is defined by simultaneous pattern match on (queue, visited, fuel).
    We induct on `fuel` and case-split on the queue, mirroring `go`'s recursion. -/
private theorem go_implies_relation {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (htrans : IsTransitive R)
    (hrefl : IsReflexive R)
    (b : EClassId) :
    ∀ (fuel : Nat) (queue : List EClassId) (visited : Std.HashSet EClassId),
    DirectedRelGraph.hasPath.go drg b queue visited fuel = true →
    ∃ c ∈ queue, R (v c) (v b) := by
  intro fuel
  induction fuel with
  | zero =>
    intro queue visited hgo
    cases queue <;> simp_all [DirectedRelGraph.hasPath.go]
  | succ n ih =>
    intro queue visited hgo
    match hq : queue with
    | [] => simp [DirectedRelGraph.hasPath.go] at hgo
    | cur :: rest =>
      unfold DirectedRelGraph.hasPath.go at hgo
      by_cases hcur : cur == b
      · -- cur is the target b itself → R(v(b), v(b)) by reflexivity
        have := beq_iff_eq.mp hcur
        subst this
        exact ⟨cur, .head rest, hrefl (v cur)⟩
      · simp [hcur] at hgo
        split at hgo
        · -- cur already visited: skip, recurse on rest
          obtain ⟨c, hc_mem, hcR⟩ := ih rest visited hgo
          exact ⟨c, List.mem_cons_of_mem _ hc_mem, hcR⟩
        · -- cur not visited: expand successors
          obtain ⟨c, hc_mem, hcR⟩ := ih (rest ++ drg.successors cur) (visited.insert cur) hgo
          rw [List.mem_append] at hc_mem
          rcases hc_mem with hc_rest | hc_succ
          · exact ⟨c, List.mem_cons_of_mem _ hc_rest, hcR⟩
          · -- c is a successor of cur: cur → c edge, and R(v(c), v(b))
            have hedge : drg.hasDirectEdge cur c := by
              simp [DirectedRelGraph.hasDirectEdge, hc_succ]
            exact ⟨cur, .head rest,
              htrans (v cur) (v c) (v b) (hcon cur c hedge) hcR⟩

theorem hasPath_implies_relation {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (htrans : IsTransitive R)
    (hrefl : IsReflexive R)
    (a b : EClassId) (fuel : Nat)
    (hpath : drg.hasPath a b fuel = true) :
    R (v a) (v b) := by
  simp only [DirectedRelGraph.hasPath] at hpath
  obtain ⟨c, hc_mem, hcR⟩ := go_implies_relation drg R v hcon htrans hrefl b fuel [a] {} hpath
  simp at hc_mem
  subst hc_mem
  exact hcR

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Antisymmetry promotes to equality
-- ══════════════════════════════════════════════════════════════════

/-- The key cross-layer rule: if R is antisymmetric, and we have both
    R(v(a), v(b)) and R(v(b), v(a)), then v(a) = v(b).

    This justifies promoting DAG edges to UF merges:
    `a ≤ b ∧ b ≤ a → merge(a, b)` in Layer 1. -/
theorem antisymmetry_promotes {Val : Type}
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hanti : IsAntisymmetric R)
    (a b : EClassId)
    (h_ab : R (v a) (v b)) (h_ba : R (v b) (v a)) :
    v a = v b :=
  hanti (v a) (v b) h_ab h_ba

/-- Combining path existence with antisymmetry: if there's a path
    a → b AND a path b → a, and R is a partial order, then v(a) = v(b). -/
theorem bidirectional_path_implies_eq {Val : Type} (drg : DirectedRelGraph)
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hcon : DirectedRelConsistency drg R v)
    (hpo : IsPartialOrder R)
    (a b : EClassId) (fuel : Nat)
    (hab : drg.hasPath a b fuel = true)
    (hba : drg.hasPath b a fuel = true) :
    v a = v b := by
  have hrefl := hpo.1.1
  have htrans := hpo.1.2
  have hanti := hpo.2
  exact antisymmetry_promotes R v hanti a b
    (hasPath_implies_relation drg R v hcon htrans hrefl a b fuel hab)
    (hasPath_implies_relation drg R v hcon htrans hrefl b a fuel hba)

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Equality → Reflexive Relation
-- ══════════════════════════════════════════════════════════════════

/-- Equality in the UF implies any reflexive relation in the DAG.
    This is the reverse direction: Layer 1 informs Layer 3. -/
theorem equality_implies_relation {Val : Type}
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hrefl : IsReflexive R) (a b : EClassId)
    (heq : v a = v b) :
    R (v a) (v b) := by
  rw [heq]; exact hrefl (v b)

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Cross-Relation Rule Soundness
-- ══════════════════════════════════════════════════════════════════

/-- Soundness of the antisymmetry cross-relation rule.
    Given two directed relation graphs for R and R⁻¹ (or the same R
    with reversed arguments), antisymmetry produces equality merges. -/
def AntisymmetryCrossRule (Val : Type) (R : SemanticRelation Val) : Prop :=
  ∀ a b, R a b → R b a → a = b

/-- The natural numbers' ≤ is a partial order that supports antisymmetry. -/
example : IsPartialOrder (fun (a b : Nat) => a ≤ b) :=
  ⟨⟨fun x => Nat.le_refl x, fun x y z => Nat.le_trans⟩,
   fun x y h1 h2 => Nat.le_antisymm h1 h2⟩

-- Divisibility on Nat is a preorder (reflexive + transitive).
-- NOTE: requires Mathlib for dvd_refl/dvd_trans; omitted in base Lean 4.

-- ══════════════════════════════════════════════════════════════════
-- Section 8: Multi-Relation Consistency
-- ══════════════════════════════════════════════════════════════════

/-- Multi-relation consistency: consistency across multiple relations.
    Each relation has its own DAG, and all are consistent with the
    same valuation. -/
def MultiRelConsistency {Val : Type}
    (dags : List (DirectedRelGraph × SemanticRelation Val))
    (v : EClassId → Val) : Prop :=
  ∀ pair ∈ dags, DirectedRelConsistency pair.1 pair.2 v

/-- Empty list of relations is trivially consistent. -/
theorem multiRel_empty_consistent {Val : Type} (v : EClassId → Val) :
    MultiRelConsistency ([] : List (DirectedRelGraph × SemanticRelation Val)) v := by
  intro pair h; exact absurd h List.not_mem_nil

/-- Adding a new relation with an empty DAG preserves multi-rel consistency. -/
theorem multiRel_add_empty {Val : Type}
    (dags : List (DirectedRelGraph × SemanticRelation Val))
    (R : SemanticRelation Val) (v : EClassId → Val)
    (hcon : MultiRelConsistency dags v) :
    MultiRelConsistency (dags ++ [(DirectedRelGraph.empty, R)]) v := by
  intro pair hmem
  simp [List.mem_append] at hmem
  rcases hmem with h | rfl
  · exact hcon pair h
  · exact empty_consistent_rel R v

-- ══════════════════════════════════════════════════════════════════
-- Section 9: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: DirectedRelConsistency is satisfiable. -/
example : DirectedRelConsistency DirectedRelGraph.empty (fun (a b : Nat) => a ≤ b)
    (fun _ => 0) :=
  empty_consistent_rel _ _

/-- Non-vacuity: antisymmetry_promotes works on concrete values. -/
example : ∀ (a b : Nat), a ≤ b → b ≤ a → a = b :=
  fun a b h1 h2 => antisymmetry_promotes (fun a b => a ≤ b) id
    (fun x y h1 h2 => Nat.le_antisymm h1 h2) a b h1 h2

end LambdaSat
