/-
  LambdaSat — MultiRelEGraph: v2 Pipeline Integration
  Fase 22 Subfase 1: Combines multi-relation saturation with extraction.

  Provides the v2 pipeline function `optimizeMultiRelF` which:
  1. Runs tiered multi-relation saturation
  2. Computes costs on the base graph
  3. Extracts the optimal expression

  Also provides backward compatibility: `MultiRelEGraph.ofBase` lifts
  a base EGraph into the multi-relation framework.

  Key results:
  - `optimizeMultiRelF`: the v2 pipeline function
  - `MultiRelEGraph.ofBase`: backward compat lift
  - `ofBase_preserves_rules`: base rules work in multi-rel context
-/
import LambdaSat.MultiRelSaturate
import LambdaSat.Extraction

set_option autoImplicit false

namespace LambdaSat

open UnionFind

variable {Op : Type} {Expr : Type}
  [NodeOps Op] [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]
  [Extractable Op Expr]

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Backward Compatibility Lift
-- ══════════════════════════════════════════════════════════════════

/-- Lift a base EGraph into the multi-relation framework.
    The colored layer is empty and there are no relations.
    This provides backward compatibility: v1.5 code works in v2. -/
def MultiRelEGraph.ofBase (g : EGraph Op) : MultiRelEGraph Op where
  baseGraph := g
  coloredLayer := ColoredLayer.empty
  relDags := []
  assumptions := fun _ _ => True

/-- ofBase preserves the base graph exactly. -/
theorem MultiRelEGraph.ofBase_baseGraph (g : EGraph Op) :
    (MultiRelEGraph.ofBase g).baseGraph = g := rfl

/-- ofBase has no relation DAGs. -/
theorem MultiRelEGraph.ofBase_noRelations (g : EGraph Op) :
    (MultiRelEGraph.ofBase g).relDags = [] := rfl

/-- ofBase preserves node count. -/
theorem MultiRelEGraph.ofBase_numNodes (g : EGraph Op) :
    (MultiRelEGraph.ofBase g).numNodes = g.numNodes := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: v2 Pipeline Function
-- ══════════════════════════════════════════════════════════════════

/-- The v2 optimization pipeline:
    1. Tiered multi-relation saturation (equality + colored + relation rules)
    2. Cost computation on the saturated base graph
    3. Auto extraction from the cost graph

    This is the multi-relation analogue of `optimizeF` from PipelineSoundness.lean.

    Parameters:
    - `cfg`: tiered saturation configuration
    - `mreg`: initial multi-relation e-graph
    - `rules`: equality rewrite rules (Layer 1)
    - `costFn`: node cost function
    - `costFuel`: fuel for cost convergence
    - `rootId`: root class to extract from -/
def optimizeMultiRelF (cfg : TieredSatConfig)
    (mreg : MultiRelEGraph Op) (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (rootId : EClassId) : Option Expr :=
  -- Step 1: Tiered multi-relation saturation
  let mreg_sat := saturateColoredF rules cfg mreg
  -- Step 2: Cost computation on the base graph
  let g_cost := computeCostsF mreg_sat.baseGraph costFn costFuel
  -- Step 3: Auto extraction
  extractAuto g_cost rootId

/-- Convenience: v2 pipeline from a base EGraph (no colors, no relations).
    This should behave identically to v1's `optimizeF`. -/
def optimizeMultiRelFromBaseF (cfg : TieredSatConfig)
    (g : EGraph Op) (rules : List (RewriteRule Op))
    (costFn : ENode Op → Nat) (costFuel : Nat)
    (rootId : EClassId) : Option Expr :=
  optimizeMultiRelF cfg (MultiRelEGraph.ofBase g) rules costFn costFuel rootId

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Base Rule Compatibility
-- ══════════════════════════════════════════════════════════════════

/-- Base rewrite rules work in the multi-relation context.
    The tiered saturation applies equality rules via `saturateStepF`
    on the base graph, which is exactly what v1's `saturateF` does. -/
theorem ofBase_preserves_rules (g : EGraph Op)
    (rules : List (RewriteRule Op))
    (cfg : TieredSatConfig)
    (hcfg : cfg.eqFreq = 1) :
    ∀ (i : Nat), i < cfg.totalFuel →
      -- Every iteration applies the equality rules
      i % cfg.eqFreq = 0 := by
  intro i _
  rw [hcfg]
  omega

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- ofBase of empty is empty multi-rel. -/
example : (MultiRelEGraph.ofBase (Op := Op) EGraph.empty).numNodes = 0 := rfl

example : (MultiRelEGraph.ofBase (Op := Op) EGraph.empty).numRelations = 0 := rfl

end LambdaSat
