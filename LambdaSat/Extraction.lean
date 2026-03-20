/-
  LambdaSat — Unified Extraction Interface + Correctness
  Fase 10: Adapted from VerifiedExtraction/Integration.lean
  v1.6.0: Added .dp strategy variant (Fase 14, N14.4)

  Provides a unified `extract` function dispatching to greedy, ILP-certificate,
  or DP-optimal methods, with a single correctness theorem parameterized by strategy.

  Key results:
  - `extract`: unified greedy/ILP/DP dispatch
  - `extract_correct`: strategy-parameterized correctness theorem
-/
import LambdaSat.ExtractSpec
import LambdaSat.ILPSpec

namespace LambdaSat

open UnionFind ILP

/-! ## Extraction Strategy -/

/-- Selection of extraction method with associated parameters.

    v1.6.0: Added `.dp` variant. DP extraction uses the same greedy `extractF`
    mechanism (following bestNode pointers), but is used after `computeCostsF` has
    been informed by a DP-optimal cost computation. The optimality of the costs
    is guaranteed by `dp_optimal_of_validNTD` (DPTableLemmas.lean); the correctness
    of the extraction from those costs follows from `extractF_correct`. -/
inductive ExtractionStrategy (Op : Type) [NodeOps Op] where
  /-- Greedy extraction: follow bestNode pointers with given fuel. -/
  | greedy (fuel : Nat)
  /-- ILP certificate extraction: follow externally-computed ILP solution. -/
  | ilp (solution : ILPSolution) (fuel : Nat)
  /-- DP-optimal extraction: follow bestNode pointers (same as greedy) after
      DP-optimal cost computation. The `dp_optimal_of_validNTD` theorem guarantees
      cost optimality; extraction correctness follows from `extractF_correct`. -/
  | dp (fuel : Nat)

variable {Op : Type} [NodeOps Op] [BEq Op] [Hashable Op]
  {Expr : Type} [Extractable Op Expr]

/-- Unified extraction: dispatches to the appropriate method. -/
def extract (g : EGraph Op) (rootId : EClassId) :
    ExtractionStrategy Op → Option Expr
  | .greedy fuel => extractF g rootId fuel
  | .ilp sol fuel => extractILP g sol rootId fuel
  | .dp fuel => extractF g rootId fuel

/-! ## Strategy-Specific Validity -/

/-- Each strategy requires a different validity witness.
    - Greedy needs `BestNodeInv`: every bestNode is in its class.
    - ILP needs `ValidSolution`: the 4-way certificate check passes.
    - DP needs `BestNodeInv`: same as greedy (DP computes optimal costs,
      extraction follows bestNode pointers). -/
def StrategyValid (g : EGraph Op) (rootId : EClassId) :
    ExtractionStrategy Op → Prop
  | .greedy _ => BestNodeInv g.classes
  | .ilp sol _ => ValidSolution g rootId sol
  | .dp _ => BestNodeInv g.classes

/-! ## Unified Correctness -/

variable [LawfulBEq Op] [LawfulHashable Op]
  {Val : Type} [NodeSemantics Op Val] [EvalExpr Expr Val]

/-- **Master extraction correctness theorem.**

    Regardless of whether greedy, ILP, or DP extraction is used, if:
    - The e-graph has a consistent valuation
    - The UnionFind is well-formed
    - The strategy-specific validity holds
    - The Extractable→NodeSemantics bridge is sound
    - Extraction succeeds

    Then the extracted expression evaluates to the semantic value of the root class.

    v1.6.0: Added `.dp` case. DP extraction reuses `extractF_correct` since it
    follows the same bestNode pointers as greedy extraction. -/
theorem extract_correct
    (g : EGraph Op) (env : Nat → Val) (v : EClassId → Val)
    (hcv : ConsistentValuation g env v)
    (hwf : WellFormed g.unionFind)
    (hsound : ExtractableSound Op Expr Val)
    (rootId : EClassId) (strategy : ExtractionStrategy Op)
    (hvalid : StrategyValid g rootId strategy)
    (expr : Expr)
    (hext : extract g rootId strategy = some expr) :
    EvalExpr.evalExpr expr env = v (root g.unionFind rootId) := by
  cases strategy with
  | greedy fuel =>
    exact extractF_correct g env v hcv hwf hvalid hsound fuel rootId expr hext
  | ilp sol fuel =>
    exact ilp_extraction_soundness g rootId sol env v hcv hwf hvalid hsound fuel expr hext
  | dp fuel =>
    exact extractF_correct g env v hcv hwf hvalid hsound fuel rootId expr hext

end LambdaSat
