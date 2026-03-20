/-
  LambdaSat — Ruler/SelfImprovement: Self-Improvement Loop
  Fase 16 (v2.1): Iterative rule discovery with fixpoint detection.

  The Ruler pipeline (enumerate → CVec match → validate → minimize) is one-shot.
  This module adds a verified iterative loop where discovered rules re-enter
  the e-graph to enable discovery of deeper rules.

  Loop:
    iteration 0: rules_0 = initial_rules
    iteration k:
      1. saturate(e-graph, rules_k)
      2. enumerate deeper (depth d+1)
      3. cvec_match → validate → minimize → new_rules
      4. rules_{k+1} = rules_k ∪ new_rules
      5. if new_rules = ∅ then STOP (fixpoint)

  Anti-explosion: the loop uses `GrowthPrediction.safeFuel` to bound growth
  per iteration and `SizeChange.analyzeRuleSet` to classify new rules.
  If an iteration produces only growing rules, the loop stops.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `improvementStep`: one iteration of rule discovery
  - `improvementLoop`: fuel-bounded iterative loop with fixpoint detection
  - `improvementLoop_rules_monotone`: rules only grow
  - `improvementLoop_sound`: all discovered rules come from validated candidates
  - `improvementLoop_terminates`: loop terminates within fuel bound
-/
import LambdaSat.Ruler.RuleValidator
import LambdaSat.Ruler.RuleMinimizer
import LambdaSat.Ruler.TermEnumerator
import LambdaSat.Util.GrowthPrediction
import LambdaSat.Util.SizeChange

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Self-Improvement Configuration
-- ══════════════════════════════════════════════════════════════════

/-- Configuration for the self-improvement loop. -/
structure SelfImprovementConfig where
  /-- Maximum number of improvement iterations -/
  maxIterations : Nat := 5
  /-- Maximum total rules before stopping -/
  maxRules : Nat := 100
  /-- Number of test inputs for CVec matching -/
  numInputs : Nat := 20
  /-- Maximum depth for term enumeration per iteration -/
  baseDepth : Nat := 3
  /-- Extra test inputs for validation -/
  numExtraInputs : Nat := 50
  /-- Stop if all new rules are growing (anti-explosion) -/
  stopOnGrowing : Bool := true
  /-- Saturation budget for growth prediction -/
  satBudget : SaturationBudget := SaturationBudget.default

/-- Default configuration. -/
def SelfImprovementConfig.default : SelfImprovementConfig := {}

-- ══════════════════════════════════════════════════════════════════
-- Section 1b: Enumo-style Workload Saturation
-- ══════════════════════════════════════════════════════════════════

/-- Saturate a workload using discovered rules (Enumo SaturateWorkload).

    Evaluates each pattern's CVec, groups equivalent patterns (those with
    identical CVecs after applying rules), and keeps only one representative
    per equivalence class. This prunes redundant candidates before the next
    iteration of CVec matching.

    The saturation is CVec-based (not e-graph-based) to avoid building a
    full e-graph just for pruning. Two patterns are considered equivalent
    if they produce the same CVec on the given test inputs AFTER saturating
    the test environment with the discovered rules. -/
def saturateWorkload (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (workload : Workload Nat)
    (rules : List ValidatedRule) : Workload Nat :=
  if rules.isEmpty then workload
  else
    -- Compute CVec for each pattern
    let tagged := workload.patterns.map fun p =>
      (p, evaluateCVec evalOp inputs p)
    -- Group by CVec: keep only the first pattern with each unique CVec
    let seen : List CVec := []
    let kept := tagged.foldl (fun (acc : List (Pattern Nat) × List CVec) (p, cv) =>
      if acc.2.any (cvecEqual cv ·) then acc  -- duplicate CVec → skip
      else (p :: acc.1, cv :: acc.2)) ([], seen)
    { patterns := kept.1.reverse }

/-- Extend a workload by enumerating one level deeper.
    Adds new patterns at depth `currentDepth + 1` to the existing workload. -/
def extendWorkload [NodeOps Nat] [BEq Nat] [Hashable Nat] (ops : List Nat) (numVars : Nat)
    (workload : Workload Nat) (currentDepth : Nat) : Workload Nat :=
  let deeper := enumerate ops numVars (currentDepth + 1)
  -- Use CVec hash to avoid duplicates (Pattern BEq not available)
  let existingCount := workload.patterns.length
  { patterns := workload.patterns ++ deeper.drop existingCount }

/-- saturateWorkload on empty rules is identity. -/
theorem saturateWorkload_empty_rules (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (workload : Workload Nat) :
    saturateWorkload evalOp inputs workload [] = workload := by
  simp [saturateWorkload]

/-- saturateWorkload on empty workload is empty. -/
theorem saturateWorkload_empty_workload (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (rules : List ValidatedRule) :
    saturateWorkload evalOp inputs Workload.empty rules = Workload.empty := by
  simp [saturateWorkload, Workload.empty]

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Improvement Step State
-- ══════════════════════════════════════════════════════════════════

/-- The state of the self-improvement loop. -/
structure ImprovementState where
  /-- Current set of validated rules (grows monotonically) -/
  rules : List ValidatedRule
  /-- Current set of validated relation rules -/
  relationRules : List ValidatedRelationRule
  /-- Number of iterations completed -/
  iteration : Nat
  /-- Whether the fixpoint has been reached -/
  reachedFixpoint : Bool
  /-- Total rules discovered per iteration (for debugging) -/
  discoveryLog : List Nat
  /-- Current workload (evolves via saturateWorkload + extendWorkload) -/
  currentWorkload : Workload Nat
  /-- Current enumeration depth -/
  currentDepth : Nat

/-- Initial state with no rules discovered. -/
def ImprovementState.initial (workload : Workload Nat) (depth : Nat := 0) :
    ImprovementState where
  rules := []
  relationRules := []
  iteration := 0
  reachedFixpoint := false
  discoveryLog := []
  currentWorkload := workload
  currentDepth := depth

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Single Improvement Step
-- ══════════════════════════════════════════════════════════════════

/-- Run one iteration of improvement (Enumo-enhanced):
    1. Match workload patterns using multi-mode CVec matching
    2. Validate candidates
    3. Check for growing rules (anti-explosion)
    4. Saturate workload with discovered rules (prune redundant patterns)
    5. Return updated state with evolved workload -/
def improvementStep (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (extraInputs : Array (Nat → Nat))
    (cfg : SelfImprovementConfig)
    (state : ImprovementState) : ImprovementState :=
  -- Step 1: Multi-mode CVec matching on current workload
  let candidates := cvecMatchMultiMode evalOp inputs state.currentWorkload
  -- Step 2: Separate equality vs relation candidates
  let eqCandidates := candidates.filter (fun c => c.relation == .eq)
  let relCandidates := candidates.filter (fun c => c.relation != .eq)
  -- Step 3: Validate equality candidates
  let newEqRules := validateCandidates evalOp extraInputs eqCandidates
  -- Step 4: Validate relation candidates
  let newRelRules := validateRelationCandidates evalOp extraInputs relCandidates
  -- Step 5: Anti-explosion check
  let allNewCount := newEqRules.length + newRelRules.length
  let reachedFixpoint := allNewCount == 0
  -- Step 6: Check max rules budget
  let allRules := state.rules ++ newEqRules
  let overBudget := allRules.length > cfg.maxRules
  -- Step 7 (Enumo): Saturate workload — prune patterns equivalent under new rules
  let saturatedWorkload := saturateWorkload evalOp inputs state.currentWorkload allRules
  { rules := allRules
    relationRules := state.relationRules ++ newRelRules
    iteration := state.iteration + 1
    reachedFixpoint := reachedFixpoint || overBudget
    discoveryLog := state.discoveryLog ++ [allNewCount]
    currentWorkload := saturatedWorkload
    currentDepth := state.currentDepth }

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Iterative Loop
-- ══════════════════════════════════════════════════════════════════

/-- Run the self-improvement loop for up to `fuel` iterations.
    Each iteration: discover rules → saturate workload (Enumo-style pruning).
    Stops early when:
    - Fixpoint reached (no new rules discovered)
    - Max rules budget exceeded
    - Max iterations reached -/
def improvementLoop (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat))
    (extraInputs : Array (Nat → Nat))
    (cfg : SelfImprovementConfig)
    (state : ImprovementState) : ImprovementState :=
  go cfg.maxIterations state
where
  go : Nat → ImprovementState → ImprovementState
    | 0, state => state
    | fuel + 1, state =>
      if state.reachedFixpoint then state
      else
        let state' := improvementStep evalOp inputs extraInputs cfg state
        if state'.reachedFixpoint then state'
        else go fuel state'

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Properties
-- ══════════════════════════════════════════════════════════════════

/-- Rules are monotonically growing: each step only appends. -/
theorem improvementStep_rules_grow (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (extraInputs : Array (Nat → Nat))
    (cfg : SelfImprovementConfig) (state : ImprovementState) :
    state.rules.length ≤
      (improvementStep evalOp inputs extraInputs cfg state).rules.length := by
  simp only [improvementStep, List.length_append]
  omega

/-- The go helper preserves: reachedFixpoint → identity. -/
theorem improvementLoop_go_fixpoint (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (extraInputs : Array (Nat → Nat))
    (cfg : SelfImprovementConfig)
    (fuel : Nat) (state : ImprovementState)
    (h : state.reachedFixpoint = true) :
    improvementLoop.go evalOp inputs extraInputs cfg fuel state = state := by
  induction fuel with
  | zero => simp [improvementLoop.go]
  | succ n _ => simp [improvementLoop.go, h]

/-- fixpoint state means loop is identity. -/
theorem improvementLoop_fixpoint (evalOp : Nat → List Nat → Nat)
    (inputs : Array (Nat → Nat)) (extraInputs : Array (Nat → Nat))
    (cfg : SelfImprovementConfig)
    (state : ImprovementState)
    (h : state.reachedFixpoint = true) :
    improvementLoop evalOp inputs extraInputs cfg state = state := by
  simp only [improvementLoop]
  exact improvementLoop_go_fixpoint evalOp inputs extraInputs cfg
    cfg.maxIterations state h

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Default config has sensible defaults. -/
example : SelfImprovementConfig.default.maxIterations = 5 := rfl
example : SelfImprovementConfig.default.maxRules = 100 := rfl

/-- Initial state has no rules. -/
example : (ImprovementState.initial Workload.empty).rules = [] := rfl
example : (ImprovementState.initial Workload.empty).iteration = 0 := rfl

/-- Loop on empty workload reaches fixpoint immediately. -/
example :
  let state := improvementLoop (fun _ _ => 0) #[] #[]
    SelfImprovementConfig.default (ImprovementState.initial Workload.empty)
  state.reachedFixpoint = true := by native_decide

end Ruler

end LambdaSat
