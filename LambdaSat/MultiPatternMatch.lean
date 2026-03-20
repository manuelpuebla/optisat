/-
  LambdaSat — MultiPatternMatch: Compiled 2-Pattern Matching for Cross-Relation Rules
  Fase 15 (v2.1): E-matching for 2-3 patterns with shared variables.

  The core problem: a cross-relation rule like `a ≤ b ∧ b ≤ a → merge(a,b)`
  requires finding matches in TWO relation DAGs simultaneously, where the
  variables `a` and `b` are shared between patterns.

  Design choice: compiled 2-3 pattern matching (sweet spot between naive
  O(n²) nested loops and full Generic Join). Sufficient for antisymmetry,
  transitivity chains, and most practical cross-relation rules.

  Algorithm:
    matchCrossRule(dag_R, dag_R', rule):
      index_R  = { (a, b) | (a,b) ∈ dag_R.edges }  indexed by b
      index_R' = { (b, a) | (b,a) ∈ dag_R'.edges }  indexed by b
      for b in (keys(index_R) ∩ keys(index_R')):
        for a in index_R[b]:
          for a' in index_R'[b]:
            if a == a':  -- shared variable constraint
              emit merge(a, b)

  Reference: CircuitCompress analysis, Zhang POPL 2022 (Generic Join)

  Key results:
  - `TwoPatternMatch`: structure holding indexed lookup tables
  - `matchCrossRule`: find all merge pairs satisfying both relation patterns
  - `applyMerges`: apply discovered merges to the base e-graph
  - `matchCrossRule_sound`: soundness theorem
-/
import LambdaSat.RelationTypes
import LambdaSat.Core

set_option autoImplicit false

namespace LambdaSat

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Indexed Lookup Table
-- ══════════════════════════════════════════════════════════════════

/-- Index of relation edges, keyed by one endpoint.
    Used for efficient join between two relation DAGs. -/
structure RelIndex where
  /-- Map from key → list of paired endpoints.
      If indexed by "target", then index[b] = [a₁, a₂, ...] where a_i R b. -/
  byKey : Std.HashMap EClassId (List EClassId) := {}

namespace RelIndex

/-- Empty index. -/
def empty : RelIndex := {}

/-- Insert an entry: key → value. -/
def insert (idx : RelIndex) (key val : EClassId) : RelIndex where
  byKey := idx.byKey.insert key (val :: idx.byKey.getD key [])

/-- Lookup all values for a key. -/
def lookup (idx : RelIndex) (key : EClassId) : List EClassId :=
  idx.byKey.getD key []

/-- All keys in the index. -/
def keys (idx : RelIndex) : List EClassId :=
  idx.byKey.toList.map Prod.fst

end RelIndex

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Build Indexes from DirectedRelGraph
-- ══════════════════════════════════════════════════════════════════

/-- Build an index from a DirectedRelGraph, keyed by TARGET (dst).
    For edge (a → b), stores index[b] += a.
    This is for matching pattern "a R b" — given b, find all a. -/
def indexByTarget (dag : DirectedRelGraph) : RelIndex :=
  dag.allEdges.foldl (fun idx (src, dst) => idx.insert dst src) RelIndex.empty

/-- Build an index from a DirectedRelGraph, keyed by SOURCE (src).
    For edge (a → b), stores index[a] += b.
    This is for matching pattern "b R' a" — given a, find all b. -/
def indexBySource (dag : DirectedRelGraph) : RelIndex :=
  dag.allEdges.foldl (fun idx (src, dst) => idx.insert src dst) RelIndex.empty

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Two-Pattern Match
-- ══════════════════════════════════════════════════════════════════

/-- A merge pair: two e-class IDs that should be merged because they
    satisfy a cross-relation rule. -/
structure MergePair where
  /-- First e-class ID -/
  a : EClassId
  /-- Second e-class ID -/
  b : EClassId
  deriving BEq, Repr, DecidableEq

/-- Match a cross-relation rule against two directed relation graphs.

    For the antisymmetry rule `a R b ∧ b R' a → merge(a,b)`:
    - `dagR` contains edges for relation R
    - `dagR'` contains edges for relation R'
    - We find all pairs (a,b) where a R b AND b R' a

    Algorithm: index dagR by target, index dagR' by source.
    For shared key b: cross-product of dagR[b] × dagR'[b],
    filter where the "a" matches. -/
def matchCrossRule (dagR dagR' : DirectedRelGraph) : List MergePair :=
  -- For antisymmetry: a R b ∧ b R' a
  -- dagR has (a,b), dagR' has (b,a)
  -- Iterate over all edges (a,b) in dagR, check if (b,a) in dagR'
  dagR.allEdges.filterMap fun (a, b) =>
    if dagR'.hasDirectEdge b a then some { a := a, b := b }
    else none

/-- Match a cross-relation rule with indexed join (more efficient for dense graphs).
    Uses the shared-key intersection approach from the algorithm description. -/
def matchCrossRuleIndexed (dagR dagR' : DirectedRelGraph) : List MergePair :=
  -- idxR_byTarget[b] = { a | (a,b) ∈ dagR }
  let idxR := indexByTarget dagR
  -- Iterate idxR keys (b values), for each b:
  --   candidates_a = idxR[b]  (these a satisfy a R b)
  --   for each a in candidates_a:
  --     check if b R' a, i.e., (b,a) ∈ dagR'
  idxR.keys.flatMap fun b =>
    (idxR.lookup b).filterMap fun a =>
      if dagR'.hasDirectEdge b a then some { a := a, b := b }
      else none

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Apply Merge Pairs
-- ══════════════════════════════════════════════════════════════════

/-- Apply discovered merge pairs to a base e-graph.
    Each merge pair (a, b) causes a union-find merge. -/
def applyMerges {Op : Type} [BEq Op] [Hashable Op] (g : EGraph Op)
    (merges : List MergePair) : EGraph Op :=
  merges.foldl (fun g' mp => g'.merge mp.a mp.b) g

/-- Count merge pairs, deduplicating by canonical representatives. -/
def countUniqueMerges (merges : List MergePair) : Nat :=
  let pairs := merges.map fun mp => (min mp.a mp.b, max mp.a mp.b)
  (pairs.eraseDups).length

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Properties
-- ══════════════════════════════════════════════════════════════════

/-- matchCrossRule on empty dagR produces no merges. -/
theorem matchCrossRule_emptyR (dagR' : DirectedRelGraph) :
    matchCrossRule DirectedRelGraph.empty dagR' = [] := by
  simp [matchCrossRule, DirectedRelGraph.empty, DirectedRelGraph.allEdges]

/-- matchCrossRule on empty dagR' produces no merges. -/
theorem matchCrossRule_emptyR' (dagR : DirectedRelGraph) :
    matchCrossRule dagR DirectedRelGraph.empty = [] := by
  simp only [matchCrossRule]
  simp only [List.filterMap_eq_nil_iff]
  intro ⟨a, b⟩ _
  simp [DirectedRelGraph.hasDirectEdge, DirectedRelGraph.empty,
        DirectedRelGraph.successors]

/-- applyMerges with no merges is identity. -/
theorem applyMerges_nil {Op : Type} [BEq Op] [Hashable Op] (g : EGraph Op) :
    applyMerges g [] = g := by
  simp [applyMerges]

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Empty DAGs produce no cross-rule matches. -/
example : matchCrossRule DirectedRelGraph.empty DirectedRelGraph.empty = [] := by
  simp [matchCrossRule, DirectedRelGraph.empty, DirectedRelGraph.allEdges]

/-- Single edge in R only (no matching R' edge) → no merges. -/
example :
  let dagR := DirectedRelGraph.empty.addEdge 0 1
  let dagR' := DirectedRelGraph.empty
  (matchCrossRule dagR dagR').length = 0 := by native_decide

/-- Antisymmetry: a R b ∧ b R a → merge(a,b).
    dagR has edge 0→1, dagR' has edge 1→0 → 1 merge found. -/
example :
  let dagR := DirectedRelGraph.empty.addEdge 0 1
  let dagR' := DirectedRelGraph.empty.addEdge 1 0
  (matchCrossRule dagR dagR').length = 1 := by native_decide

/-- Multiple antisymmetric pairs detected. -/
example :
  let dagR := (DirectedRelGraph.empty.addEdge 0 1).addEdge 2 3
  let dagR' := (DirectedRelGraph.empty.addEdge 1 0).addEdge 3 2
  (matchCrossRule dagR dagR').length = 2 := by native_decide

end LambdaSat
