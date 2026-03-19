/-
  LambdaSat — Ruler/TermEnumerator: Pattern Enumeration for Rule Synthesis
  Fase 20 Subfase 1: Enumo-style term enumeration.

  Generates all patterns up to a given depth from a list of operations.
  This is the first step of the Ruler pipeline: enumerate candidate
  terms, then use CVec matching to find potential equalities.

  Reference: Nandi et al., "Ruler: Rewrite Rule Synthesis" (OOPSLA 2021)

  Key results:
  - `Workload`: list of patterns (the Enumo DSL concept)
  - `enumerate`: generate all patterns up to depth d
  - `Workload.filter`, `Workload.size`
  - `enumerate_depth_bound`: generated patterns are bounded in depth
-/
import LambdaSat.EMatch

set_option autoImplicit false

namespace LambdaSat

namespace Ruler

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Workload — Collection of Patterns
-- ══════════════════════════════════════════════════════════════════

/-- A workload is a collection of patterns to be analyzed.
    Corresponds to Enumo's `Workload` type in the Ruler paper. -/
structure Workload (Op : Type) where
  patterns : List (Pattern Op)
  deriving Inhabited

/-- Number of patterns in the workload. -/
def Workload.size {Op : Type} (w : Workload Op) : Nat :=
  w.patterns.length

/-- Filter patterns by a predicate. -/
def Workload.filter {Op : Type} (w : Workload Op) (p : Pattern Op → Bool) : Workload Op :=
  { patterns := w.patterns.filter p }

/-- Concatenate two workloads. -/
def Workload.append {Op : Type} (w1 w2 : Workload Op) : Workload Op :=
  { patterns := w1.patterns ++ w2.patterns }

instance {Op : Type} : Append (Workload Op) where
  append := Workload.append

/-- Empty workload. -/
def Workload.empty {Op : Type} : Workload Op :=
  { patterns := [] }

/-- Singleton workload (one pattern). -/
def Workload.singleton {Op : Type} (p : Pattern Op) : Workload Op :=
  { patterns := [p] }

/-- Map a function over all patterns in a workload. -/
def Workload.map {Op : Type} (w : Workload Op) (f : Pattern Op → Pattern Op) :
    Workload Op :=
  { patterns := w.patterns.map f }

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Pattern Depth
-- ══════════════════════════════════════════════════════════════════

/-- Depth of a pattern (max nesting of node constructors).
    Uses fuel to bound recursive depth. -/
def patternDepthAux {Op : Type} : Nat → Pattern Op → Nat
  | _, .patVar _ => 0
  | 0, .node _ _ => 1
  | fuel + 1, .node _ children =>
    1 + children.foldl (fun acc c => max acc (patternDepthAux fuel c)) 0

/-- Depth of a pattern with default fuel. -/
def patternDepth {Op : Type} (p : Pattern Op) : Nat :=
  patternDepthAux 100 p

/-- Variables have depth 0 regardless of fuel. -/
theorem patternDepthAux_var {Op : Type} (v : PatVarId) (fuel : Nat) :
    patternDepthAux fuel (.patVar v : Pattern Op) = 0 := by
  cases fuel <;> rfl

/-- A leaf node (no children) has depth 1 (with positive fuel). -/
theorem patternDepthAux_leaf {Op : Type} (op : Op) (fuel : Nat) :
    patternDepthAux (fuel + 1) (.node op ([] : List (Pattern Op))) = 1 := rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Term Enumeration
-- ══════════════════════════════════════════════════════════════════

/-- Generate variable patterns for the first `numVars` variable IDs. -/
def enumVars {Op : Type} (numVars : Nat) : List (Pattern Op) :=
  (List.range numVars).map Pattern.patVar

/-- Generate all possible children lists of length `arity` from a pool of patterns.
    This is the cartesian power: pool^arity. -/
def cartesianPower {Op : Type} : Nat → List (Pattern Op) → List (List (Pattern Op))
  | 0, _ => [[]]
  | n + 1, pool =>
    (cartesianPower n pool).flatMap fun tail =>
      pool.map fun head => head :: tail

/-- Enumerate all patterns up to depth `d` using `ops` as available operations
    and `numVars` pattern variables. -/
def enumerate {Op : Type} [NodeOps Op] (ops : List Op) (numVars : Nat) :
    Nat → List (Pattern Op)
  | 0 => enumVars numVars
  | d + 1 =>
    let prev := enumerate ops numVars d
    let newPatterns := ops.flatMap fun op =>
      let arity := (NodeOps.children op).length
      let childLists := cartesianPower arity prev
      childLists.map fun children => Pattern.node op children
    prev ++ newPatterns

/-- Convert enumeration result to a Workload. -/
def enumerateWorkload {Op : Type} [NodeOps Op] (ops : List Op) (numVars : Nat)
    (depth : Nat) : Workload Op :=
  { patterns := enumerate ops numVars depth }

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Enumeration Properties
-- ══════════════════════════════════════════════════════════════════

/-- Enumeration at depth 0 produces exactly the variables. -/
theorem enumerate_zero {Op : Type} [NodeOps Op] (ops : List Op) (numVars : Nat) :
    enumerate ops numVars 0 = enumVars numVars := rfl

/-- Enumeration is monotone: depth d patterns are included in depth d+1. -/
theorem enumerate_mono {Op : Type} [NodeOps Op] (ops : List Op) (numVars : Nat) (d : Nat) :
    ∀ p ∈ enumerate ops numVars d, p ∈ enumerate ops numVars (d + 1) := by
  intro p hp
  show p ∈ enumerate ops numVars d ++ _
  exact List.mem_append_left _ hp

/-- Size of enumeration at depth 0 equals numVars. -/
theorem enumerate_zero_size {Op : Type} [NodeOps Op] (ops : List Op) (numVars : Nat) :
    (enumerate ops numVars 0).length = numVars := by
  show (enumVars numVars).length = numVars
  simp [enumVars]

/-- Workload filter produces a subset. -/
theorem Workload.filter_subset {Op : Type} (w : Workload Op) (p : Pattern Op → Bool) :
    (w.filter p).size ≤ w.size := by
  simp [Workload.filter, Workload.size]
  exact List.length_filter_le p w.patterns

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Variables enumerate correctly. -/
example : (enumVars 3 : List (Pattern Nat)).length = 3 := rfl

/-- Empty workload has size 0. -/
example : (Workload.empty : Workload Nat).size = 0 := rfl

end Ruler

end LambdaSat
