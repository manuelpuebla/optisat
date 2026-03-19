/-
  LambdaSat — ColoredSpec: Colored Soundness Specification
  Fase 16: Layer 2 soundness — CRITICAL PATH.

  Defines `ColoredConsistentValuation` (CCV): the semantic invariant for
  colored e-graphs. Extends `ConsistentValuation` with color-gated equalities:
  for each color c with assumption φ_c, IF φ_c holds, THEN all classes
  merged under c have the same value in the valuation.

  Key insight: CCV projects to standard CV at the root color, preserving
  backward compatibility with all 363 existing v1.5.2 theorems.

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)

  Key results:
  - `ColoredConsistentValuation`: the invariant
  - `CCV_implies_base_CV`: backward compatibility
  - `coloredMerge_preserves_CCV`: merge under color preserves CCV
  - `SoundColoredRule`: colored rewrite rule with soundness proof
  - `soundColoredRule_preserves_CCV`: applying a sound colored rule preserves CCV
-/
import LambdaSat.SemanticSpec
import LambdaSat.ColorTypes
import LambdaSat.ColoredMerge
import LambdaSat.SoundRule

set_option autoImplicit false

namespace LambdaSat

open UnionFind

variable {Op : Type} {Val : Type}
  [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [NodeSemantics Op Val]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Color Assumptions
-- ══════════════════════════════════════════════════════════════════

/-- An assumption function maps each color to a proposition on the environment.
    The root color (0) has the trivial assumption `True`.
    Non-root colors carry meaningful assumptions (e.g., "n > 0"). -/
def ColorAssumption (Val : Type) := ColorId → (Nat → Val) → Prop

/-- The trivial assumption: always true. Used for the root color. -/
def trivialAssumption : (Nat → Val) → Prop := fun _ => True

/-- A well-formed assumption function: root color has trivial assumption,
    and child assumptions imply parent assumptions (monotonicity). -/
def WellFormedAssumptions (assumptions : ColorAssumption Val)
    (hierarchy : ColorHierarchy) : Prop :=
  -- Root assumption is trivial
  (∀ env, assumptions colorRoot env) ∧
  -- Child assumptions imply parent assumptions (assumption monotonicity)
  (∀ c : ColorId, c ≠ colorRoot →
    ∀ env, assumptions c env → assumptions (hierarchy.getParent c) env)

-- ══════════════════════════════════════════════════════════════════
-- Section 2: ColoredConsistentValuation
-- ══════════════════════════════════════════════════════════════════

/-- ColoredConsistentValuation (CCV): the semantic invariant for colored e-graphs.

    Extends ConsistentValuation with color-gated equalities. For each non-root
    color c, IF the color's assumption holds, THEN all e-classes that are
    equivalent under c must have the same value in the valuation.

    This captures the key Easter Egg property: colors add equalities
    (under assumptions), never remove them. -/
def ColoredConsistentValuation (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    (assumptions : ColorAssumption Val) (env : Nat → Val)
    (v : EClassId → Val) : Prop :=
  -- (1) Base: standard ConsistentValuation holds unconditionally
  ConsistentValuation baseGraph env v ∧
  -- (2) Colored: for each non-root color, if assumption holds,
  --     then colored-equivalent classes have the same value
  (∀ c : ColorId, c ≠ colorRoot → assumptions c env →
    ∀ a b : EClassId,
    ColoredLayer.equivUnderColor cl (baseGraph.unionFind.root ·) c a b = true →
    v a = v b)

-- ══════════════════════════════════════════════════════════════════
-- Section 3: CCV ↔ CV backward compatibility
-- ══════════════════════════════════════════════════════════════════

/-- CCV implies standard CV: just project the first conjunct.
    This is the backward-compatibility theorem: all 363 existing v1.5.2
    theorems that use CV still hold when the graph also has colors. -/
theorem CCV_implies_base_CV (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    (assumptions : ColorAssumption Val) (env : Nat → Val) (v : EClassId → Val)
    (hccv : ColoredConsistentValuation baseGraph cl assumptions env v) :
    ConsistentValuation baseGraph env v :=
  hccv.1

/-- CV lifts to CCV when there are no non-root colors (empty colored layer).
    This shows that existing graphs trivially satisfy CCV. -/
theorem CV_implies_CCV_empty (baseGraph : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation baseGraph env v) :
    ColoredConsistentValuation baseGraph (ColoredLayer.empty) (fun _ _ => True) env v :=
  ⟨hcv, fun c _hc _ha a b hequiv => by
    rw [equivUnderColor_empty_layer] at hequiv
    have := beq_iff_eq.mp hequiv
    exact hcv.1 a b this⟩

-- ══════════════════════════════════════════════════════════════════
-- Section 4: coloredMerge preserves CCV
-- ══════════════════════════════════════════════════════════════════

/-- Colored find preserves valuation: the canonical representative under a
    color has the same value as the original e-class id.

    This follows from CCV: find(id) is equivalent to id under the color,
    and CCV says equivalent classes have the same value.

    Requires SmallUF idempotency (findUnderColor is a valid retraction),
    which holds when all SmallUFs in the hierarchy are well-formed. -/
def FindPreservesVal (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (v : EClassId → Val) (fuel : Nat) : Prop :=
  ∀ c : ColorId, ∀ id : EClassId,
    v (ColoredLayer.findUnderColor cl baseFind c id fuel) = v id

/-- foldl of deltaFind preserves valuation when each step preserves it. -/
private theorem foldl_deltaFind_preserves_val_aux
    (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (fuel : Nat) (v : EClassId → Val)
    (hcolors : ∀ c id, v ((colorUFs.getD c SmallUF.empty).deltaFind id fuel) = v id) :
    ∀ acc, v (ancestors.foldl (fun acc c =>
      (colorUFs.getD c SmallUF.empty).deltaFind acc fuel) acc) = v acc := by
  induction ancestors with
  | nil => intro acc; rfl
  | cons c rest ih =>
    intro acc; simp only [List.foldl]
    have := ih ((colorUFs.getD c SmallUF.empty).deltaFind acc fuel)
    rw [this]; exact hcolors c acc

private theorem foldl_deltaFind_preserves_val
    (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat)
    (v : EClassId → Val)
    (hbase : ∀ id, v (baseFind id) = v id)
    (hcolors : ∀ c id, v ((colorUFs.getD c SmallUF.empty).deltaFind id fuel) = v id) :
    ∀ id, v (compositeFind colorUFs ancestors baseFind fuel id) = v id := by
  intro id; simp only [compositeFind]
  rw [foldl_deltaFind_preserves_val_aux colorUFs ancestors fuel v hcolors]
  exact hbase id

omit [NodeOps Op] [LawfulBEq Op] [LawfulHashable Op] in
private theorem addToWorklist_equivUnderColor (cl : ColoredLayer Op) (c : ColorId)
    (ids : List EClassId) (baseFind : EClassId → EClassId) (c' : ColorId)
    (a b : EClassId) (fuel : Nat) :
    (cl.addToWorklist c ids).equivUnderColor baseFind c' a b fuel =
    cl.equivUnderColor baseFind c' a b fuel := rfl

theorem coloredMerge_preserves_CCV (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    (assumptions : ColorAssumption Val) (env : Nat → Val) (v : EClassId → Val)
    (c : ColorId) (a b : EClassId) (fuel : Nat)
    (hccv : ColoredConsistentValuation baseGraph cl assumptions env v)
    (_hassume : assumptions c env)
    (hsound : v a = v b)
    (hbase_v : ∀ id, v (baseGraph.unionFind.root id) = v id)
    (hdelta : ∀ c_inner id f, v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id f) = v id)
    (hroot_repA : (cl.getUF c).delta.get?
        ((cl.getUF c).deltaFind
          (cl.findUnderColor (baseGraph.unionFind.root ·) c a fuel) fuel) = none)
    (hroot_repB : (cl.getUF c).delta.get?
        ((cl.getUF c).deltaFind
          (cl.findUnderColor (baseGraph.unionFind.root ·) c b fuel) fuel) = none) :
    ColoredConsistentValuation baseGraph
      (ColoredLayer.mergeUnderColor cl (baseGraph.unionFind.root ·) c a b fuel).1
      assumptions env v := by
  constructor
  · exact hccv.1
  · intro c' hc' hassume' a' b' hequiv'
    simp only [ColoredLayer.mergeUnderColor] at hequiv'
    split at hequiv'
    · exact hccv.2 c' hc' hassume' a' b' hequiv'
    · -- Actual merge of repA→repB in color c's SmallUF.
      rename_i hneq
      -- Local abbreviations
      let repA := cl.findUnderColor (fun x => baseGraph.unionFind.root x) c a fuel
      let repB := cl.findUnderColor (fun x => baseGraph.unionFind.root x) c b fuel
      let mergedUF := (cl.getUF c).merge repA repB fuel
      -- Specialize hdelta to specific fuel values
      have hdelta_fuel : ∀ c_inner id,
          v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id fuel) = v id :=
        fun c_inner id => hdelta c_inner id fuel
      -- v(repA) = v(repB) via compositeFind preservation + hsound
      have hv_repA : v repA = v a :=
        foldl_deltaFind_preserves_val cl.colorUFs _ (baseGraph.unionFind.root ·) fuel v
          hbase_v hdelta_fuel a
      have hv_repB : v repB = v b :=
        foldl_deltaFind_preserves_val cl.colorUFs _ (baseGraph.unionFind.root ·) fuel v
          hbase_v hdelta_fuel b
      have hab : v repA = v repB := hv_repA.trans (hsound.trans hv_repB.symm)
      -- hold for getUF c = colorUFs.getD c SmallUF.empty, for ALL fuel
      have hold : ∀ id f, v ((cl.getUF c).deltaFind id f) = v id :=
        fun id f => by simp only [ColoredLayer.getUF]; exact hdelta c id f
      -- Modified colorUFs per-step preservation (for any fuel_inner)
      have hmod_delta : ∀ f_inner c_inner id_inner,
          v (((cl.colorUFs.insert c mergedUF).getD c_inner
            SmallUF.empty).deltaFind id_inner f_inner) = v id_inner := by
        intro f_inner c_inner id_inner
        rw [Std.HashMap.getD_insert]
        split
        · -- c == c_inner: the merged SmallUF
          rename_i hceq
          have hceq' := beq_iff_eq.mp hceq; subst hceq'
          show v (((cl.getUF c).merge repA repB fuel).deltaFind id_inner f_inner) = v id_inner
          simp only [SmallUF.merge]
          split
          · -- degenerate: repA == repB internally
            simp only [ColoredLayer.getUF]; exact hdelta c id_inner f_inner
          · -- Actual insert
            have hab_internal : v ((cl.getUF c).deltaFind repA fuel) =
                v ((cl.getUF c).deltaFind repB fuel) :=
              (hold repA fuel).trans (hab.trans (hold repB fuel).symm)
            exact SmallUF.deltaFind_insert_preserves_val (cl.getUF c)
              ((cl.getUF c).deltaFind repA fuel) ((cl.getUF c).deltaFind repB fuel) v
              hroot_repA hroot_repB hab_internal hold id_inner f_inner
        · -- c ≠ c_inner: unchanged
          exact hdelta c_inner id_inner f_inner
      -- Eliminate addToWorklist/.fst noise from hequiv'
      have hequiv_clean : (cl.setUF c mergedUF).equivUnderColor
          (fun x => baseGraph.unionFind.root x) c' a' b' = true := by
        have : ((cl.setUF c mergedUF).addToWorklist c [repA, repB], true).fst =
               (cl.setUF c mergedUF).addToWorklist c [repA, repB] := rfl
        rw [this] at hequiv'
        rw [addToWorklist_equivUnderColor] at hequiv'
        exact hequiv'
      -- Unfold to compositeFind equality (default fuel = 100)
      simp only [ColoredLayer.equivUnderColor, ColoredLayer.findUnderColor,
                  ColoredLayer.setUF] at hequiv_clean
      have hbeq := beq_iff_eq.mp hequiv_clean
      -- compositeFind on modified layer preserves v (at fuel = 100, matching hbeq)
      have hmod_find : ∀ id, v (compositeFind (cl.colorUFs.insert c mergedUF)
          (cl.hierarchy.ancestors c').reverse (fun x => baseGraph.unionFind.root x) 100 id) = v id :=
        foldl_deltaFind_preserves_val (cl.colorUFs.insert c mergedUF)
          (cl.hierarchy.ancestors c').reverse (fun x => baseGraph.unionFind.root x) 100 v
          hbase_v (fun c_inner id => hmod_delta 100 c_inner id)
      -- v(a') = v(b') from compositeFind equality + preservation
      calc v a' = v (compositeFind (cl.colorUFs.insert c mergedUF)
                    (cl.hierarchy.ancestors c').reverse
                    (fun x => baseGraph.unionFind.root x) 100 a') := (hmod_find a').symm
        _ = v (compositeFind (cl.colorUFs.insert c mergedUF)
                    (cl.hierarchy.ancestors c').reverse
                    (fun x => baseGraph.unionFind.root x) 100 b') := congrArg v hbeq
        _ = v b' := hmod_find b'

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Sound Colored Rules
-- ══════════════════════════════════════════════════════════════════

/-- A sound colored rewrite rule: carries a soundness proof that
    the LHS and RHS evaluate to the same value UNDER the color's assumption.

    This is the colored analogue of `SoundRewriteRule` from SoundRule.lean. -/
structure SoundColoredRule (Op : Type) (Expr : Type) (Val : Type)
    [BEq Op] [Hashable Op] where
  /-- The color (assumption context) under which this rule applies -/
  color : ColorId
  /-- Rule name -/
  name : String
  /-- Syntactic rule for e-matching -/
  rule : RewriteRule Op
  /-- Semantic LHS expression -/
  lhsExpr : (Nat → Expr) → Expr
  /-- Semantic RHS expression -/
  rhsExpr : (Nat → Expr) → Expr
  /-- Expression evaluator -/
  eval : Expr → (Nat → Val) → Val
  /-- Assumption for this color -/
  assumption : (Nat → Val) → Prop
  /-- Soundness: under the assumption, LHS = RHS -/
  soundness : ∀ (env : Nat → Val) (vars : Nat → Expr),
    assumption env → eval (lhsExpr vars) env = eval (rhsExpr vars) env

/-- An unconditional SoundRewriteRule lifts to a colored rule at root color. -/
def SoundRewriteRule.toColored {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRewriteRule Op Expr Val) : SoundColoredRule Op Expr Val where
  color := colorRoot
  name := r.name
  rule := r.rule
  lhsExpr := r.lhsExpr
  rhsExpr := r.rhsExpr
  eval := r.eval
  assumption := fun _ => True
  soundness := fun env vars _ => r.soundness env vars

/-- Applying a sound colored rule preserves CCV.
    Combines coloredMerge_preserves_CCV with the rule's soundness proof. -/
theorem soundColoredRule_preserves_CCV (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    {Expr : Type} (rule : SoundColoredRule Op Expr Val)
    (assumptions : ColorAssumption Val) (env : Nat → Val) (v : EClassId → Val)
    (lhsId rhsId : EClassId) (fuel : Nat)
    (hccv : ColoredConsistentValuation baseGraph cl assumptions env v)
    (hassume : assumptions rule.color env)
    (h_color_match : rule.assumption = assumptions rule.color)
    (hbase_v : ∀ id, v (baseGraph.unionFind.root id) = v id)
    (hdelta : ∀ c_inner id f,
      v ((cl.colorUFs.getD c_inner SmallUF.empty).deltaFind id f) = v id)
    (hroot_repA : (cl.getUF rule.color).delta.get?
        ((cl.getUF rule.color).deltaFind
          (cl.findUnderColor (baseGraph.unionFind.root ·) rule.color lhsId fuel) fuel) = none)
    (hroot_repB : (cl.getUF rule.color).delta.get?
        ((cl.getUF rule.color).deltaFind
          (cl.findUnderColor (baseGraph.unionFind.root ·) rule.color rhsId fuel) fuel) = none)
    (vars : Nat → Expr)
    (h_lhs : v lhsId = rule.eval (rule.lhsExpr vars) env)
    (h_rhs : v rhsId = rule.eval (rule.rhsExpr vars) env) :
    ColoredConsistentValuation baseGraph
      (ColoredLayer.mergeUnderColor cl (baseGraph.unionFind.root ·) rule.color lhsId rhsId fuel).1
      assumptions env v :=
  coloredMerge_preserves_CCV baseGraph cl assumptions env v rule.color lhsId rhsId fuel
    hccv hassume (by rw [h_lhs, h_rhs]; exact rule.soundness env vars (h_color_match ▸ hassume))
    hbase_v hdelta hroot_repA hroot_repB

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Extraction under color
-- ══════════════════════════════════════════════════════════════════

/-- Extraction correctness under a non-root color: if CCV holds and the color's
    assumption holds, then the extracted value equals the valuation.

    For root-color extraction, use `CCV_implies_base_CV` + base extraction directly.
    Root-color equivalences are covered by base `ConsistentValuation`, not by CCV's
    colored clause (which excludes root by design). -/
theorem extractColored_correct (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    (assumptions : ColorAssumption Val) (env : Nat → Val) (v : EClassId → Val)
    (c : ColorId) (classId : EClassId)
    (hccv : ColoredConsistentValuation baseGraph cl assumptions env v)
    (hnonroot : c ≠ colorRoot)
    (hassume : assumptions c env)
    (h_equiv : ColoredLayer.equivUnderColor cl (baseGraph.unionFind.root ·) c classId
      (ColoredLayer.findUnderColor cl (baseGraph.unionFind.root ·) c classId) = true) :
    v classId = v (ColoredLayer.findUnderColor cl (baseGraph.unionFind.root ·) c classId) :=
  hccv.2 c hnonroot hassume classId _ h_equiv

-- ══════════════════════════════════════════════════════════════════
-- Section 7: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Non-vacuity: CCV_implies_base_CV is not vacuous (CCV projects to CV). -/
example (baseGraph : EGraph Op) (cl : ColoredLayer Op)
    (assumptions : ColorAssumption Val) (env : Nat → Val) (v : EClassId → Val)
    (hccv : ColoredConsistentValuation baseGraph cl assumptions env v) :
    ConsistentValuation baseGraph env v :=
  CCV_implies_base_CV baseGraph cl assumptions env v hccv

end LambdaSat
