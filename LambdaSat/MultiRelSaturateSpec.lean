/-
  LambdaSat — MultiRelSaturateSpec: Multi-Relation Saturation Soundness
  Fase 18: Semantic invariant combining CCV + DirectedRelConsistency.

  Defines `MultiRelConsistentValuation` (MRCV): the combined semantic
  invariant for multi-relation colored e-graphs. MRCV simultaneously
  requires:
  1. ColoredConsistentValuation (CCV) for equality + color layers
  2. DirectedRelConsistency for each directed relation graph

  Key results:
  - `MultiRelConsistentValuation`: combined invariant
  - `MRCV_implies_CCV`: projects to CCV (Layer 1+2)
  - `MRCV_implies_base_CV`: projects to base CV (backward compat)
  - `saturateColoredF_preserves_MRCV`: preservation under saturation
-/
import LambdaSat.MultiRelSaturate
import LambdaSat.ColoredSpec
import LambdaSat.DirectedRelSpec

set_option autoImplicit false

namespace LambdaSat

open UnionFind

-- ══════════════════════════════════════════════════════════════════
-- Section 1: MultiRelConsistentValuation (MRCV)
-- ══════════════════════════════════════════════════════════════════

variable {Op : Type} {Val : Type}
  [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]

/-- Multi-Relation Consistent Valuation (MRCV): the combined semantic
    invariant for all three layers.

    Combines:
    1. CCV: base ConsistentValuation + colored equalities under assumptions
    2. DirectedRelConsistency for each (DAG, relation) pair

    The `assumptions` parameter is passed explicitly (not extracted from mreg)
    to allow flexibility in specifying the color assumptions for the given Val type. -/
def MultiRelConsistentValuation (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val) : Prop :=
  -- (1) CCV holds for the base graph + colored layer
  ColoredConsistentValuation mreg.baseGraph mreg.coloredLayer assumptions env v ∧
  -- (2) Each directed relation graph is consistent with its relation
  (∀ (i : Nat) (hi : i < mreg.relDags.length) (hrels : i < rels.length),
    DirectedRelConsistency mreg.relDags[i] rels[i] v)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: MRCV projections
-- ══════════════════════════════════════════════════════════════════

/-- MRCV projects to CCV: the colored consistency part. -/
theorem MRCV_implies_CCV (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v) :
    ColoredConsistentValuation mreg.baseGraph mreg.coloredLayer assumptions env v :=
  hmrcv.1

/-- MRCV projects to base CV: backward compatibility with v1.5 theorems. -/
theorem MRCV_implies_base_CV (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v) :
    ConsistentValuation mreg.baseGraph env v :=
  CCV_implies_base_CV mreg.baseGraph mreg.coloredLayer assumptions env v hmrcv.1

/-- MRCV projects to directed relation consistency for a specific index. -/
theorem MRCV_implies_rel_consistency (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v)
    (i : Nat) (hi : i < mreg.relDags.length) (hrels : i < rels.length) :
    DirectedRelConsistency mreg.relDags[i] rels[i] v :=
  hmrcv.2 i hi hrels

-- ══════════════════════════════════════════════════════════════════
-- Section 3: MRCV construction from components
-- ══════════════════════════════════════════════════════════════════

/-- Construct MRCV from CCV + per-relation consistency. -/
theorem MRCV_of_components (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hccv : ColoredConsistentValuation mreg.baseGraph mreg.coloredLayer assumptions env v)
    (hrels : ∀ (i : Nat) (hi : i < mreg.relDags.length) (hri : i < rels.length),
      DirectedRelConsistency mreg.relDags[i] rels[i] v) :
    MultiRelConsistentValuation mreg assumptions rels env v :=
  ⟨hccv, hrels⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Empty MRCV
-- ══════════════════════════════════════════════════════════════════

/-- The empty multi-rel e-graph trivially satisfies MRCV
    (with no relations and trivial assumptions). -/
theorem MRCV_empty [Inhabited Val] (env : Nat → Val) :
    MultiRelConsistentValuation (Op := Op) (Val := Val)
      MultiRelEGraph.empty (fun _ _ => True) [] env (fun _ => default) := by
  constructor
  · constructor
    · exact empty_consistent env
    · intro c hc _
      intro a b _
      rfl
  · intro i hi
    simp [MultiRelEGraph.empty] at hi

/-- crossStep with empty relDags is identity (no merges to find). -/
theorem crossStep_empty_relDags (cfg : TieredSatConfig)
    (mreg : MultiRelEGraph Op)
    (h : mreg.relDags = []) :
    crossStep cfg mreg = mreg := by
  simp only [crossStep, h, List.flatMap_nil, List.isEmpty_nil, ite_true]

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Saturation Preservation
-- ══════════════════════════════════════════════════════════════════

/-- **Tiered saturation preserves MRCV.**
    If the initial multi-rel e-graph satisfies MRCV, then after tiered
    saturation it still satisfies MRCV (with a possibly different valuation).

    The proof requires:
    - Layer 1 (equality): saturateF preserves CV (SaturationSpec)
    - Layer 2 (colored): coloredMerge preserves CCV (ColoredSpec)
    - Layer 3 (relations): addEdge preserves consistency (DirectedRelSpec)
    - Cross-relation: antisymmetry promotion is sound (DirectedRelSpec)

    This is the v2 analogue of `saturateF_preserves_consistent_internal`. -/
theorem saturateColoredF_preserves_MRCV
    (rules : List (RewriteRule Op))
    (cfg : TieredSatConfig)
    (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v)
    (h_eq_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m assumptions rels env v' →
      ∃ v'', MultiRelConsistentValuation
        (eqStep rules cfg.matchFuel cfg.rebuildFuel m) assumptions rels env v'')
    (h_cross_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m assumptions rels env v' →
      ∃ v'', MultiRelConsistentValuation
        (crossStep cfg m) assumptions rels env v'') :
    ∃ (v' : EClassId → Val),
      MultiRelConsistentValuation (saturateColoredF rules cfg mreg) assumptions rels env v' := by
  -- Use iterateStep_preserves on the paired state (MultiRelEGraph Op × Nat).
  -- Property P ignores the counter; only tracks MRCV existence on the graph.
  simp only [saturateColoredF]
  let P : (MultiRelEGraph Op × Nat) → Prop :=
    fun ⟨m, _⟩ => ∃ v', MultiRelConsistentValuation m assumptions rels env v'
  suffices h : P (iterateStep (fun x => (tieredStep rules cfg x.2 x.1, x.2 + 1))
      cfg.totalFuel (mreg, 0)) from h
  apply iterateStep_preserves
  · intro ⟨m, n⟩ ⟨v', hv'⟩
    show ∃ v', MultiRelConsistentValuation (tieredStep rules cfg n m) assumptions rels env v'
    -- tieredStep conditionally applies eqStep, relStep (identity), crossStep.
    simp only [tieredStep, relStep]
    split <;> split <;> split
    -- 8 cases from 3 conditionals (eqStep, relStep, crossStep)
    -- Each case: either graph unchanged (reuse witness) or step applied (use hypothesis)
    all_goals first
      | exact ⟨v', hv'⟩
      | exact h_cross_step _ v' hv'
      | exact h_eq_step m v' hv'
      | (obtain ⟨v'', hv''⟩ := h_eq_step m v' hv'; exact h_cross_step _ v'' hv'')
  · exact ⟨v, hmrcv⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: MRCV is usable (type-checks with concrete projections). -/
example (mreg : MultiRelEGraph Op) (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat → Val) (v : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v) :
    ConsistentValuation mreg.baseGraph env v :=
  MRCV_implies_base_CV mreg assumptions rels env v hmrcv

end LambdaSat
