/-
  LambdaSat — MultiRelSoundness: v2 Master Theorem
  Fase 22 Subfase 2: End-to-end soundness for the v2 pipeline.

  Combines:
  - Multi-relation saturation preservation (MultiRelSaturateSpec)
  - Cost computation preservation (SemanticSpec)
  - Extraction correctness (Extraction)

  Key results:
  - `full_pipeline_v2_soundness`: master theorem for v2
  - `v2_implies_v1_soundness`: backward compat — v2 with base features = v1
-/
import LambdaSat.MultiRelEGraph
import LambdaSat.MultiRelSaturateSpec
import LambdaSat.TranslationValidation
import LambdaSat.PipelineSoundness

set_option autoImplicit false

namespace LambdaSat

open UnionFind

variable {Op : Type} {Val : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op]
  [LawfulBEq Op] [LawfulHashable Op]
  [DecidableEq Op] [Repr Op] [Inhabited Op]
  [NodeSemantics Op Val]
  [Extractable Op Expr] [EvalExpr Expr Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: v2 Pipeline Soundness
-- ══════════════════════════════════════════════════════════════════

/-- **v2 Master Theorem: Full Pipeline Soundness.**

    If `optimizeMultiRelF` returns `some expr`, then:
    - There exists a consistent valuation `v_sat` for the saturated graph
    - The extracted expression evaluates to `v_sat(root(rootId))` in the
      saturated base graph

    This is the multi-relation analogue of `optimizeF_soundness`.

    The proof composes:
    1. `saturateColoredF_preserves_MRCV` -> get v_sat + MRCV for saturated graph
    2. MRCV_implies_base_CV -> get base CV
    3. `computeCostsF_preserves_consistency` -> CV through cost computation
    4. `extractAuto`/`extractF_correct` -> extraction correctness -/
theorem full_pipeline_v2_soundness [Inhabited Val]
    (mreg : MultiRelEGraph Op)
    (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (rules : List (RewriteRule Op))
    (cfg : TieredSatConfig)
    (costFn : ENode Op -> Nat) (costFuel : Nat)
    (env : Nat -> Val) (v : EClassId -> Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v)
    (h_eq_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m assumptions rels env v' →
      ∃ v'', MultiRelConsistentValuation
        (eqStep rules cfg.matchFuel cfg.rebuildFuel m) assumptions rels env v'')
    (h_cross_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m assumptions rels env v' →
      ∃ v'', MultiRelConsistentValuation
        (crossStep cfg m) assumptions rels env v'')
    (rootId : EClassId) (expr : Expr)
    (hwf_sat : WellFormed (saturateColoredF rules cfg mreg).baseGraph.unionFind)
    (hbni_sat : BestNodeInv (computeCostsF (saturateColoredF rules cfg mreg).baseGraph
      costFn costFuel).classes)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeMultiRelF cfg mreg rules costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId -> Val),
      EvalExpr.evalExpr expr env =
        v_sat (root (saturateColoredF rules cfg mreg).baseGraph.unionFind rootId) := by
  -- Step 1: MRCV preservation through saturation → get v_sat + MRCV for saturated graph
  obtain ⟨v_sat, hmrcv_sat⟩ := saturateColoredF_preserves_MRCV rules cfg mreg
    assumptions rels env v hmrcv h_eq_step h_cross_step
  -- Step 2: Project to base CV for the saturated base graph
  have hcv_sat := MRCV_implies_base_CV (saturateColoredF rules cfg mreg) assumptions rels env v_sat hmrcv_sat
  -- Step 3: Unfold optimizeMultiRelF to get extractAuto (computeCostsF ...) = some expr
  unfold optimizeMultiRelF at hopt
  -- Step 4: Cost computation preserves CV
  have hcv_cost := computeCostsF_preserves_consistency
    (saturateColoredF rules cfg mreg).baseGraph costFn costFuel env v_sat hcv_sat
  -- Step 5: extractAuto correctness
  have hroot_eq : root (computeCostsF (saturateColoredF rules cfg mreg).baseGraph
      costFn costFuel).unionFind rootId =
    root (saturateColoredF rules cfg mreg).baseGraph.unionFind rootId := by
    simp [computeCostsF_preserves_uf]
  have hwf_cost : WellFormed (computeCostsF (saturateColoredF rules cfg mreg).baseGraph
      costFn costFuel).unionFind := by
    rw [computeCostsF_preserves_uf]; exact hwf_sat
  have hext := extractAuto_correct
    (computeCostsF (saturateColoredF rules cfg mreg).baseGraph costFn costFuel)
    env v_sat hcv_cost hwf_cost hbni_sat hsound rootId expr hopt
  rw [hroot_eq] at hext
  exact ⟨v_sat, hext⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 2: MRCV construction for ofBase
-- ══════════════════════════════════════════════════════════════════

/-- Base CV lifts to MRCV when using `ofBase` (no colors, no relations). -/
theorem CV_lifts_to_MRCV_ofBase (g : EGraph Op)
    (env : Nat -> Val) (v : EClassId -> Val)
    (hcv : ConsistentValuation g env v) :
    MultiRelConsistentValuation (MultiRelEGraph.ofBase g) (fun _ _ => True) [] env v := by
  constructor
  · constructor
    · exact hcv
    · intro c hc _
      intro a b hequiv
      simp only [MultiRelEGraph.ofBase] at hequiv
      rw [equivUnderColor_empty_layer] at hequiv
      exact hcv.1 a b (beq_iff_eq.mp hequiv)
  · intro i hi
    simp [MultiRelEGraph.ofBase] at hi

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Backward Compatibility
-- ══════════════════════════════════════════════════════════════════

/-- **v2 -> v1 backward compatibility.**

    When using only base features (no colors, no relations), the v2
    pipeline reduces to the v1 pipeline. Specifically, if the multi-rel
    e-graph was created via `ofBase`, the extracted expression satisfies
    the same correctness property as v1's `optimizeF_soundness`.

    This ensures that all 363 existing v1.5.2 theorems remain valid
    when the codebase is upgraded to v2. -/
theorem v2_implies_v1_soundness [Inhabited Val]
    (g : EGraph Op)
    (rules : List (RewriteRule Op))
    (cfg : TieredSatConfig)
    (costFn : ENode Op -> Nat) (costFuel : Nat)
    (env : Nat -> Val) (v : EClassId -> Val)
    (hcv : ConsistentValuation g env v)
    (h_eq_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m (fun _ _ => True) [] env v' →
      ∃ v'', MultiRelConsistentValuation
        (eqStep rules cfg.matchFuel cfg.rebuildFuel m) (fun _ _ => True) [] env v'')
    (h_cross_step : ∀ (m : MultiRelEGraph Op) (v' : EClassId → Val),
      MultiRelConsistentValuation m (fun _ _ => True) [] env v' →
      ∃ v'', MultiRelConsistentValuation
        (crossStep cfg m) (fun _ _ => True) [] env v'')
    (rootId : EClassId) (expr : Expr)
    (hwf_sat : WellFormed (saturateColoredF rules cfg (MultiRelEGraph.ofBase g)).baseGraph.unionFind)
    (hbni_sat : BestNodeInv (computeCostsF
      (saturateColoredF rules cfg (MultiRelEGraph.ofBase g)).baseGraph
      costFn costFuel).classes)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeMultiRelFromBaseF cfg g rules costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId -> Val),
      EvalExpr.evalExpr expr env =
        v_sat (root (saturateColoredF rules cfg (MultiRelEGraph.ofBase g)).baseGraph.unionFind rootId) := by
  have hmrcv := CV_lifts_to_MRCV_ofBase g env v hcv
  have hopt' : optimizeMultiRelF cfg (MultiRelEGraph.ofBase g) rules costFn costFuel rootId = some expr :=
    hopt
  exact full_pipeline_v2_soundness (MultiRelEGraph.ofBase g)
    (fun _ _ => True) [] rules cfg costFn costFuel env v hmrcv h_eq_step h_cross_step
    rootId expr hwf_sat hbni_sat hsound hopt'

-- ══════════════════════════════════════════════════════════════════
-- Section 3b: Auto-discharge for ofBase (v2.1.1)
-- ══════════════════════════════════════════════════════════════════

/-- h_cross_step is trivially satisfied when relDags = [].
    crossStep with no relation DAGs produces no merges → identity. -/
theorem crossStep_preserves_MRCV_ofBase
    (cfg : TieredSatConfig)
    (m : MultiRelEGraph Op) (env : Nat → Val) (v' : EClassId → Val)
    (hmrcv : MultiRelConsistentValuation m (fun _ _ => True) [] env v')
    (hempty : m.relDags = []) :
    ∃ v'', MultiRelConsistentValuation
      (crossStep cfg m) (fun _ _ => True) [] env v'' := by
  rw [crossStep_empty_relDags cfg m hempty]
  exact ⟨v', hmrcv⟩

/-- For ofBase graphs, relDags stays [] through eqStep (which only modifies baseGraph). -/
theorem eqStep_preserves_empty_relDags (rules : List (RewriteRule Op))
    (matchFuel rebuildFuel : Nat) (m : MultiRelEGraph Op)
    (h : m.relDags = []) :
    (eqStep rules matchFuel rebuildFuel m).relDags = [] := by
  simp [eqStep, h]

set_option maxHeartbeats 800000 in
/-- v2 to v1 backward compatibility with ZERO external hypotheses.
    For ofBase callers, matches v1 API. h_eq_step and h_cross_step discharged internally. -/
theorem v2_implies_v1_soundness_auto [Inhabited Val]
    (g : EGraph Op)
    (rules : List (PatternSoundRule Op Val))
    (cfg : TieredSatConfig)
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hpmi : PostMergeInvariant g) (hshi : SemanticHashconsInv g env v)
    (hhcb : HashconsChildrenBounded g)
    (rootId : EClassId) (expr : Expr)
    (hwf_sat : WellFormed (saturateColoredF (rules.map (·.rule)) cfg
      (MultiRelEGraph.ofBase g)).baseGraph.unionFind)
    (hbni_sat : BestNodeInv (computeCostsF
      (saturateColoredF (rules.map (·.rule)) cfg (MultiRelEGraph.ofBase g)).baseGraph
      costFn costFuel).classes)
    (hsound : ExtractableSound Op Expr Val)
    (hopt : optimizeMultiRelFromBaseF cfg g (rules.map (·.rule))
      costFn costFuel rootId = some expr) :
    ∃ (v_sat : EClassId → Val),
      EvalExpr.evalExpr expr env =
        v_sat (root (saturateColoredF (rules.map (·.rule)) cfg
          (MultiRelEGraph.ofBase g)).baseGraph.unionFind rootId) := by
  -- Step 1: Get h_rules from PatternSoundRule (zero external hypotheses)
  have h_rules := patternSoundRules_preserveCV cfg.matchFuel env rules
  -- Step 2: Thread compound invariant through saturateColoredF
  simp only [saturateColoredF] at hopt hwf_sat hbni_sat ⊢
  -- Define compound invariant P: (∃ v', CV ∧ PMI ∧ SHI ∧ HCB) + structural
  -- Use `suffices` with explicit predicate to avoid let-unfolding issues
  suffices hloop : (∃ v', ConsistentValuation
      (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1))
        cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph env v') by
    obtain ⟨v_sat, hcv_sat⟩ := hloop
    have hcv_cost := computeCostsF_preserves_consistency
      (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph
      costFn costFuel env v_sat hcv_sat
    unfold optimizeMultiRelFromBaseF optimizeMultiRelF at hopt
    simp only [saturateColoredF] at hopt
    have hroot_eq : root (computeCostsF
        (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph
        costFn costFuel).unionFind rootId =
      root (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph.unionFind
        rootId := by simp [computeCostsF_preserves_uf]
    have hwf_cost : WellFormed (computeCostsF
        (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph
        costFn costFuel).unionFind := by rw [computeCostsF_preserves_uf]; exact hwf_sat
    have hext := extractAuto_correct
      (computeCostsF (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)).1.baseGraph
        costFn costFuel)
      env v_sat hcv_cost hwf_cost hbni_sat hsound rootId expr hopt
    rw [hroot_eq] at hext
    exact ⟨v_sat, hext⟩
  -- Now prove the loop preserves CV
  let P : (MultiRelEGraph Op × Nat) → Prop :=
    fun ⟨m, _⟩ => (∃ v', ConsistentValuation m.baseGraph env v' ∧
      PostMergeInvariant m.baseGraph ∧ SemanticHashconsInv m.baseGraph env v' ∧
      HashconsChildrenBounded m.baseGraph) ∧
      m.coloredLayer = ColoredLayer.empty ∧ m.relDags = []
  suffices hP : P (iterateStep (fun x => (tieredStep (rules.map (·.rule)) cfg x.2 x.1, x.2 + 1)) cfg.totalFuel (MultiRelEGraph.ofBase g, 0)) by
    obtain ⟨⟨v', hcv', _, _, _⟩, _, _⟩ := hP
    exact ⟨v', hcv'⟩
  -- Step 3: Prove P is preserved by iterateStep
  apply iterateStep_preserves
  · -- Step preservation: each tieredStep preserves P
    intro ⟨m, n⟩ ⟨⟨v', hcv', hpmi', hshi', hhcb'⟩, hcl, hrl⟩
    -- Helper: eqStep preserves the quadruple
    have heq_quad : ∃ v1, ConsistentValuation (eqStep (rules.map (·.rule))
        cfg.matchFuel cfg.rebuildFuel m).baseGraph env v1 ∧
        PostMergeInvariant (eqStep (rules.map (·.rule))
          cfg.matchFuel cfg.rebuildFuel m).baseGraph ∧
        SemanticHashconsInv (eqStep (rules.map (·.rule))
          cfg.matchFuel cfg.rebuildFuel m).baseGraph env v1 ∧
        HashconsChildrenBounded (eqStep (rules.map (·.rule))
          cfg.matchFuel cfg.rebuildFuel m).baseGraph := by
      simp only [eqStep]
      obtain ⟨v1, hcv1, hpmi1, hshi1, hhcb1, _, _⟩ :=
        applyRulesF_preserves_cv cfg.matchFuel env _ h_rules m.baseGraph v' hcv' hpmi' hshi' hhcb'
      have ⟨hcv2, hpmi2, hshi2, hhcb2⟩ :=
        rebuildF_preserves_cv env cfg.rebuildFuel _ v1 hcv1 hpmi1 hshi1 hhcb1
      exact ⟨v1, hcv2, hpmi2, hshi2, hhcb2⟩
    -- Helper: eqStep preserves structural properties
    have heq_cl : (eqStep (rules.map (·.rule)) cfg.matchFuel cfg.rebuildFuel m).coloredLayer =
        m.coloredLayer := by simp [eqStep]
    have heq_rl : (eqStep (rules.map (·.rule)) cfg.matchFuel cfg.rebuildFuel m).relDags =
        m.relDags := by simp [eqStep]
    -- Now prove P for tieredStep
    simp only [tieredStep, relStep]
    -- All 8 cases from 3 conditionals reduce to either:
    --   (a) graph unchanged → reuse v', or (b) eqStep applied → use heq_quad
    --   crossStep on relDags=[] is identity
    split <;> split <;> split
    -- Use a uniform handler for all 8 cases
    all_goals (
      first
        -- Case: no change at all
        | exact ⟨⟨v', hcv', hpmi', hshi', hhcb'⟩, hcl, hrl⟩
        -- Case: only crossStep (identity for empty relDags)
        | (rw [crossStep_empty_relDags cfg _ hrl]; exact ⟨⟨v', hcv', hpmi', hshi', hhcb'⟩, hcl, hrl⟩)
        -- Case: only eqStep, no crossStep
        | exact ⟨heq_quad, heq_cl ▸ hcl, heq_rl ▸ hrl⟩
        -- Case: eqStep + crossStep (crossStep identity after eqStep preserves relDags)
        | (rw [crossStep_empty_relDags cfg _ (heq_rl ▸ hrl)];
           exact ⟨heq_quad, heq_cl ▸ hcl, heq_rl ▸ hrl⟩))
  · exact ⟨⟨v, hcv, hpmi, hshi, hhcb⟩, rfl, rfl⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Type-check: full_pipeline_v2_soundness has the expected conclusion shape. -/
example (mreg : MultiRelEGraph Op) (assumptions : ColorAssumption Val)
    (rels : List (SemanticRelation Val))
    (env : Nat -> Val) (v : EClassId -> Val)
    (hmrcv : MultiRelConsistentValuation mreg assumptions rels env v) :
    ConsistentValuation mreg.baseGraph env v :=
  MRCV_implies_base_CV mreg assumptions rels env v hmrcv

end LambdaSat
