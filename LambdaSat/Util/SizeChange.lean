/-
  LambdaSat — SizeChange: Rule Size Classification + Termination Analysis
  Fase 19 Subfase 5: Anti-explosion module.

  Classifies rewrite rules by their size effect (shrinking/neutral/growing)
  and generates saturation configuration based on the analysis.

  The analysis is OUTSIDE the TCB: it affects iteration bounds,
  not correctness. A growing rule set gets conservative fuel;
  a monotone (non-growing) set gets generous fuel.

  Adapted from SuperTensor (EGraph/Termination.lean).
  Mathlib dependency eliminated; generalized to work with any `Pattern Op`.

  Key results:
  - `SizeChange`: shrinking / neutral / growing classification
  - `patternSize`: count nodes in a pattern
  - `analyzeRuleSet`: full termination analysis
  - `isMonotoneSet`: all rules non-growing → safe for generous fuel
  - `empty_rules_monotone`: empty set is trivially monotone
-/
import LambdaSat.EMatch

set_option autoImplicit false

namespace LambdaSat

/-! ## Pattern Size -/

/-- Count the number of nodes in a pattern (variables count as 1). -/
def patternSize {Op : Type} : Pattern Op → Nat
  | .patVar _ => 1
  | .node _ children => 1 + children.foldl (fun acc c => acc + patternSize c) 0

/-- Variables have size 1. -/
theorem patternSize_var {Op : Type} (v : PatVarId) :
    patternSize (Pattern.patVar v : Pattern Op) = 1 := by simp [patternSize]

/-- A leaf application (no children) has size 1. -/
theorem patternSize_leaf {Op : Type} (op : Op) :
    patternSize (Pattern.node op [] : Pattern Op) = 1 := by simp [patternSize]

/-- Pattern size is always ≥ 1. -/
theorem patternSize_pos {Op : Type} (p : Pattern Op) : 0 < patternSize p := by
  cases p with
  | patVar _ => simp [patternSize]
  | node _ _ => simp [patternSize]; omega

/-! ## Size Change Classification -/

/-- Size change classification of a rewrite rule. -/
inductive SizeChange where
  | shrinking : SizeChange   -- rhs strictly smaller than lhs
  | neutral   : SizeChange   -- same size
  | growing   : SizeChange   -- rhs larger than lhs
  deriving Repr, DecidableEq, BEq

/-- Classify a rule by comparing lhs and rhs pattern sizes. -/
def classifyRule (lhsSize rhsSize : Nat) : SizeChange :=
  if rhsSize < lhsSize then .shrinking
  else if rhsSize == lhsSize then .neutral
  else .growing

/-- Compute the size delta: rhs - lhs (as Int). Positive = growing. -/
def sizeDelta (lhsSize rhsSize : Nat) : Int :=
  (rhsSize : Int) - (lhsSize : Int)

/-- Classify a RewriteRule by its pattern sizes. -/
def rewriteRuleSizeChange {Op : Type} [BEq Op] [Hashable Op]
    (rule : RewriteRule Op) : SizeChange :=
  classifyRule (patternSize rule.lhs) (patternSize rule.rhs)

/-- Size delta of a RewriteRule. -/
def rewriteRuleSizeDelta {Op : Type} [BEq Op] [Hashable Op]
    (rule : RewriteRule Op) : Int :=
  sizeDelta (patternSize rule.lhs) (patternSize rule.rhs)

/-! ## Termination Analysis -/

/-- Result of termination analysis on a rule set. -/
structure TerminationAnalysis where
  /-- Total number of rules analyzed -/
  totalRules : Nat
  /-- Rules where rhs is strictly smaller -/
  shrinkingRules : Nat
  /-- Rules where rhs is same size -/
  neutralRules : Nat
  /-- Rules where rhs is strictly larger -/
  growingRules : Nat
  /-- Maximum growth delta across all rules -/
  maxGrowth : Int
  /-- Conservative termination flag: true only if no growing rules -/
  terminates : Bool
  /-- Recommended fuel based on analysis -/
  suggestedFuel : Nat
  deriving Repr

/-- Analyze a rule set for termination. -/
def analyzeRuleSet {Op : Type} [BEq Op] [Hashable Op]
    (rules : List (RewriteRule Op)) : TerminationAnalysis :=
  let classifications := rules.map rewriteRuleSizeChange
  let deltas := rules.map rewriteRuleSizeDelta
  let shrinking := classifications.filter (· == .shrinking) |>.length
  let neutral := classifications.filter (· == .neutral) |>.length
  let growing := classifications.filter (· == .growing) |>.length
  let maxGrowth := deltas.foldl max 0
  { totalRules := rules.length
    shrinkingRules := shrinking
    neutralRules := neutral
    growingRules := growing
    maxGrowth := maxGrowth
    terminates := growing == 0
    suggestedFuel :=
      if growing == 0 then 100
      else 10 + growing * 5
  }

/-! ## Saturation Configuration -/

/-- Configuration for equality saturation with termination awareness. -/
structure TermAwareSatConfig where
  maxIterations : Nat := 30
  maxNodes : Nat := 10000
  maxClassSize : Nat := 100
  deriving Repr, Inhabited

/-- Generate saturation config from termination analysis. -/
def configFromAnalysis (analysis : TerminationAnalysis) : TermAwareSatConfig where
  maxIterations := analysis.suggestedFuel
  maxNodes := if analysis.terminates then 50000 else 10000
  maxClassSize := if analysis.terminates then 500 else 50

/-! ## Monotonicity -/

/-- A rule is monotone if it doesn't increase pattern size. -/
def isMonotone {Op : Type} [BEq Op] [Hashable Op] (rule : RewriteRule Op) : Bool :=
  patternSize rule.rhs ≤ patternSize rule.lhs

/-- A rule set is monotone if every rule is monotone.
    Monotone rule sets guarantee bounded growth during saturation. -/
def isMonotoneSet {Op : Type} [BEq Op] [Hashable Op]
    (rules : List (RewriteRule Op)) : Bool :=
  rules.all isMonotone

/-- An empty rule set is trivially monotone. -/
theorem empty_rules_monotone {Op : Type} [BEq Op] [Hashable Op] :
    isMonotoneSet ([] : List (RewriteRule Op)) = true := rfl

/-! ## Rule Metrics -/

/-- Metrics for a single rule application. -/
structure RuleMetrics where
  /-- Name/identifier for the rule -/
  name : String
  /-- Classification -/
  change : SizeChange
  /-- Size delta -/
  delta : Int
  /-- Number of times applied -/
  applications : Nat := 0
  deriving Repr

/-- Compute metrics for a named rule. -/
def ruleMetrics {Op : Type} [BEq Op] [Hashable Op]
    (rule : RewriteRule Op) : RuleMetrics where
  name := rule.name
  change := rewriteRuleSizeChange rule
  delta := rewriteRuleSizeDelta rule
  applications := 0

/-! ## Smoke tests -/

private inductive SCTestOp where
  | lit : Nat → SCTestOp
  | add : SCTestOp
  | neg : SCTestOp
  deriving BEq, Hashable

-- A shrinking rule: neg(neg(x)) → x (size 3 → 1)
#eval
  let lhs : Pattern SCTestOp := .node .neg [.node .neg [.patVar 0]]
  let rhs : Pattern SCTestOp := .patVar 0
  let sc := classifyRule (patternSize lhs) (patternSize rhs)
  s!"neg(neg(x)) → x: lhs_size={patternSize lhs}, rhs_size={patternSize rhs}, change={repr sc}"

-- A neutral rule: add(x,y) → add(y,x) (size 3 → 3)
#eval
  let lhs : Pattern SCTestOp := .node .add [.patVar 0, .patVar 1]
  let rhs : Pattern SCTestOp := .node .add [.patVar 1, .patVar 0]
  let sc := classifyRule (patternSize lhs) (patternSize rhs)
  s!"add(x,y) → add(y,x): lhs_size={patternSize lhs}, rhs_size={patternSize rhs}, change={repr sc}"

-- A growing rule: x → add(x,0) (size 1 → 3)
#eval
  let lhs : Pattern SCTestOp := .patVar 0
  let rhs : Pattern SCTestOp := .node .add [.patVar 0, .node (.lit 0) []]
  let sc := classifyRule (patternSize lhs) (patternSize rhs)
  s!"x → add(x,0): lhs_size={patternSize lhs}, rhs_size={patternSize rhs}, change={repr sc}"

end LambdaSat
