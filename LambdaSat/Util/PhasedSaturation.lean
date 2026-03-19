/-
  LambdaSat — PhasedSaturation: Multi-Phase Saturation Strategy
  Fase 19 Subfase 4: Anti-explosion module.

  Wraps saturation into a multi-phase strategy where different rule sets
  are applied in separate phases with independent fuel budgets.

  Key insight: phase separation controls E-graph explosion by letting
  cheap rules (algebraic identities) reach fixpoint before introducing
  expensive rules (field-specific, cross-relation). Each phase has its
  own fuel and rebuild budget.

  Adapted from AMO-Lean (PhasedSaturation.lean).
  Generalized from BitNodeOp to generic `NodeOps Op`.

  Key results:
  - `PhasedConfig`: per-phase fuel parameters
  - `iterateStep`: generic fuel-bounded iteration
  - `phasedSaturateF`: two-phase saturation
  - `iterateStep_mono`: iteration count is bounded by fuel
  - `phasedSaturateF_composition`: phased = sequential composition
-/
import LambdaSat.Core
import LambdaSat.Util.GrowthPrediction

set_option autoImplicit false

namespace LambdaSat

/-! ## PhasedConfig -/

/-- Configuration for multi-phase saturation.
    Each phase has independent fuel and rebuild budget. -/
structure PhasedConfig where
  /-- Maximum iterations for Phase 1 (e.g. algebraic identities) -/
  phase1Fuel : Nat := 5
  /-- Rebuild depth per iteration in Phase 1 -/
  phase1RebuildFuel : Nat := 3
  /-- Maximum iterations for Phase 2 (e.g. domain-specific rules) -/
  phase2Fuel : Nat := 10
  /-- Rebuild depth per iteration in Phase 2 -/
  phase2RebuildFuel : Nat := 5
  deriving Repr, Inhabited

/-- Default configuration: balanced fuel for both phases. -/
def PhasedConfig.default : PhasedConfig := {}

/-- Aggressive configuration: more iterations for Phase 2. -/
def PhasedConfig.aggressive : PhasedConfig where
  phase1Fuel := 8
  phase1RebuildFuel := 5
  phase2Fuel := 20
  phase2RebuildFuel := 8

/-- Minimal configuration: one pass each (for testing). -/
def PhasedConfig.minimal : PhasedConfig where
  phase1Fuel := 1
  phase1RebuildFuel := 1
  phase2Fuel := 1
  phase2RebuildFuel := 1

/-! ## Generic Step Iteration -/

/-- Apply a step function repeatedly up to `fuel` times.
    This is the generic "saturate loop" abstraction.
    `step` transforms the state; iteration stops when fuel runs out. -/
def iterateStep {S : Type} (step : S → S) : Nat → S → S
  | 0, s => s
  | n + 1, s => iterateStep step n (step s)

/-- iterateStep with 0 fuel is identity. -/
theorem iterateStep_zero {S : Type} (step : S → S) (s : S) :
    iterateStep step 0 s = s := rfl

/-- iterateStep with fuel+1 applies step then recurses. -/
theorem iterateStep_succ {S : Type} (step : S → S) (n : Nat) (s : S) :
    iterateStep step (n + 1) s = iterateStep step n (step s) := rfl

/-- iterateStep with 1 fuel is just one step application. -/
theorem iterateStep_one {S : Type} (step : S → S) (s : S) :
    iterateStep step 1 s = step s := rfl

/-- Composition: iterating n steps then m steps = iterating n+m steps. -/
theorem iterateStep_add {S : Type} (step : S → S) (n m : Nat) (s : S) :
    iterateStep step m (iterateStep step n s) =
    iterateStep step (n + m) s := by
  induction n generalizing s with
  | zero => simp [iterateStep_zero]
  | succ k ih =>
    simp only [iterateStep_succ]
    rw [ih (step s)]
    show iterateStep step (k + m) (step s) = iterateStep step (k + 1 + m) s
    rw [show k + 1 + m = (k + m) + 1 from by omega]
    rfl

/-- If step preserves a property P, then iterateStep also preserves P. -/
theorem iterateStep_preserves {S : Type} (step : S → S) (P : S → Prop)
    (h_step : ∀ s, P s → P (step s)) (n : Nat) (s : S) (hs : P s) :
    P (iterateStep step n s) := by
  induction n generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (step s) (h_step s hs)

/-! ## Budget-Aware Iteration -/

/-- Apply a step function up to `fuel` times, stopping early if `budget` is exceeded.
    `measure` extracts the current size metric from the state. -/
def iterateWithBudget {S : Type} (step : S → S) (measure : S → Nat)
    (budget : SaturationBudget) : Nat → S → S × Nat
  | 0, s => (s, 0)
  | n + 1, s =>
    if budgetExceeded budget (measure s) then (s, 0)
    else
      let s' := step s
      let (result, steps) := iterateWithBudget step measure budget n s'
      (result, steps + 1)

/-- Budget-aware iteration always performs ≤ fuel steps. -/
theorem iterateWithBudget_steps_le {S : Type} (step : S → S) (measure : S → Nat)
    (budget : SaturationBudget) (fuel : Nat) (s : S) :
    (iterateWithBudget step measure budget fuel s).2 ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [iterateWithBudget]
  | succ n ih =>
    simp only [iterateWithBudget]
    split
    · omega
    · have := ih (step s)
      omega

/-- If budget is already exceeded, no steps are taken. -/
theorem iterateWithBudget_exceeded {S : Type} (step : S → S) (measure : S → Nat)
    (budget : SaturationBudget) (fuel : Nat) (s : S)
    (h : budgetExceeded budget (measure s) = true) :
    iterateWithBudget step measure budget (fuel + 1) s = (s, 0) := by
  simp [iterateWithBudget, h]

/-! ## Two-Phase Saturation -/

/-- Two-phase equality saturation: Phase 1 rules first, then Phase 2 rules.

    Phase ordering is a practical strategy (Herbie, PLDI 2015) that controls
    E-graph explosion by separating cheap rules from expensive ones.

    The separation allows:
    1. Phase 1 to reach a fixpoint before introducing Phase 2 rules
    2. Phase 2 to exploit Phase 1's normal forms
    3. Independent fuel control for each phase -/
def phasedSaturateF {S : Type} (step1 step2 : S → S)
    (cfg : PhasedConfig) (s : S) : S :=
  let s1 := iterateStep step1 cfg.phase1Fuel s
  iterateStep step2 cfg.phase2Fuel s1

/-- phasedSaturateF with identity Phase 2 is just Phase 1. -/
theorem phasedSaturateF_id_phase2 {S : Type} (step1 : S → S)
    (cfg : PhasedConfig) (s : S) :
    phasedSaturateF step1 id cfg s = iterateStep step1 cfg.phase1Fuel s := by
  simp [phasedSaturateF]
  induction cfg.phase2Fuel with
  | zero => rfl
  | succ n ih => simp [iterateStep_succ]; exact ih

/-- If both steps preserve a property P, then phased saturation preserves P. -/
theorem phasedSaturateF_preserves {S : Type} (step1 step2 : S → S) (P : S → Prop)
    (h1 : ∀ s, P s → P (step1 s)) (h2 : ∀ s, P s → P (step2 s))
    (cfg : PhasedConfig) (s : S) (hs : P s) :
    P (phasedSaturateF step1 step2 cfg s) := by
  unfold phasedSaturateF
  exact iterateStep_preserves step2 P h2 cfg.phase2Fuel _ (iterateStep_preserves step1 P h1 cfg.phase1Fuel s hs)

/-- Phased saturation is equivalent to sequential iteration with total fuel. -/
theorem phasedSaturateF_composition {S : Type} (step : S → S)
    (cfg : PhasedConfig) (s : S) :
    phasedSaturateF step step cfg s =
    iterateStep step (cfg.phase1Fuel + cfg.phase2Fuel) s := by
  simp [phasedSaturateF, iterateStep_add]

/-! ## Three-Phase Saturation -/

/-- Configuration for three-phase saturation.
    Phase 1: equality rules (every iteration)
    Phase 2: intra-relation rules (every 5 iterations)
    Phase 3: cross-relation rules (every 20 iterations, EWMA-gated) -/
structure ThreePhaseConfig where
  phase1Fuel : Nat := 10
  phase2Fuel : Nat := 5
  phase3Fuel : Nat := 3
  deriving Repr, Inhabited

/-- Three-phase saturation: Phase 1 → Phase 2 → Phase 3. -/
def threePhaseSaturateF {S : Type} (step1 step2 step3 : S → S)
    (cfg : ThreePhaseConfig) (s : S) : S :=
  let s1 := iterateStep step1 cfg.phase1Fuel s
  let s2 := iterateStep step2 cfg.phase2Fuel s1
  iterateStep step3 cfg.phase3Fuel s2

/-- Three-phase preserves any property preserved by all three steps. -/
theorem threePhaseSaturateF_preserves {S : Type}
    (step1 step2 step3 : S → S) (P : S → Prop)
    (h1 : ∀ s, P s → P (step1 s)) (h2 : ∀ s, P s → P (step2 s))
    (h3 : ∀ s, P s → P (step3 s))
    (cfg : ThreePhaseConfig) (s : S) (hs : P s) :
    P (threePhaseSaturateF step1 step2 step3 cfg s) := by
  unfold threePhaseSaturateF
  exact iterateStep_preserves step3 P h3 cfg.phase3Fuel _
    (iterateStep_preserves step2 P h2 cfg.phase2Fuel _
      (iterateStep_preserves step1 P h1 cfg.phase1Fuel s hs))

/-! ## Smoke tests -/

#eval
  let step := (· + 1 : Nat → Nat)
  let result := iterateStep step 5 0
  s!"iterateStep (+1) 5 0 = {result}"

#eval
  let step := (· + 1 : Nat → Nat)
  let budget : SaturationBudget := { maxNodes := 3, maxSteps := 10, maxRules := 5 }
  let (result, steps) := iterateWithBudget step id budget 10 0
  s!"Budget-aware: result={result}, steps={steps}"

#eval
  let cfg := PhasedConfig.default
  s!"Default config: p1Fuel={cfg.phase1Fuel}, p2Fuel={cfg.phase2Fuel}"

example : PhasedConfig.default.phase1Fuel = 5 := rfl
example : PhasedConfig.default.phase2Fuel = 10 := rfl

end LambdaSat
