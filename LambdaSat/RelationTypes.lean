/-
  LambdaSat — Multi-Relation Types
  Fase 14 Subfase 2: Foundation types for Layer 3 (directed relations).

  Extends SoundRewriteRule (equality only) to arbitrary relations.
  Provides directed graphs for non-symmetric relations (≤, ∣, →)
  and cross-relation rules connecting Layers 1-3.

  Key types:
  - `SoundRelationRule`: rewrite rule parametric in relation R
  - `DirectedRelGraph`: adjacency-list DAG for directed relations
  - `CrossRelationRule`: rules connecting different relation layers
  - `ProofCompositionEntry`: composable proof certificates for relation chains

  Reference: CircuitCompress brainstorm §5.3, optisat-v2-insights.md
-/
import LambdaSat.SoundRule
import Std.Data.HashMap
import Std.Data.HashSet

namespace LambdaSat

-- ══════════════════════════════════════════════════════════════════
-- Section 1: SoundRelationRule — Generalized Rewrite Rules
-- ══════════════════════════════════════════════════════════════════

/-- A sound relation rule generalizes `SoundRewriteRule` from equality to an
    arbitrary relation R. When R = Eq, this reduces to `SoundRewriteRule`.

    The soundness proof guarantees that R holds between the evaluations of
    LHS and RHS for all environments and variable assignments. -/
structure SoundRelationRule (Op : Type) (Expr : Type) (Val : Type)
    (R : Val → Val → Prop) [BEq Op] [Hashable Op] where
  name : String
  rule : RewriteRule Op
  lhsExpr : (Nat → Expr) → Expr
  rhsExpr : (Nat → Expr) → Expr
  eval : Expr → (Nat → Val) → Val
  soundness : ∀ (env : Nat → Val) (vars : Nat → Expr),
    R (eval (lhsExpr vars) env) (eval (rhsExpr vars) env)

/-- Convert a `SoundRewriteRule` (equality) to a `SoundRelationRule Eq`. -/
def SoundRewriteRule.toRelationRule {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRewriteRule Op Expr Val) : SoundRelationRule Op Expr Val Eq where
  name := r.name
  rule := r.rule
  lhsExpr := r.lhsExpr
  rhsExpr := r.rhsExpr
  eval := r.eval
  soundness := r.soundness

/-- Convert a `SoundRelationRule Eq` back to a `SoundRewriteRule`. -/
def SoundRelationRule.toEqualityRule {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRelationRule Op Expr Val Eq) : SoundRewriteRule Op Expr Val where
  name := r.name
  rule := r.rule
  lhsExpr := r.lhsExpr
  rhsExpr := r.rhsExpr
  eval := r.eval
  soundness := r.soundness

/-- Round-trip: toRelationRule ∘ toEqualityRule preserves soundness. -/
theorem SoundRelationRule.roundtrip_eq {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRelationRule Op Expr Val Eq) :
    r.toEqualityRule.toRelationRule.soundness = r.soundness := by
  rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Directed Relation Graph
-- ══════════════════════════════════════════════════════════════════

/-- A directed graph storing relation edges between e-class IDs.
    Edge (a, b) means "R(value_at_a, value_at_b)" for the associated relation.
    Used for non-symmetric relations like ≤, ∣, →. -/
structure DirectedRelGraph where
  edges : Std.HashMap EClassId (List EClassId) := {}
  numEdges : Nat := 0

namespace DirectedRelGraph

def empty : DirectedRelGraph := {}

/-- Add a directed edge from `src` to `dst`. -/
def addEdge (g : DirectedRelGraph) (src dst : EClassId) : DirectedRelGraph where
  edges := g.edges.insert src (dst :: g.edges.getD src [])
  numEdges := g.numEdges + 1

/-- Get all targets reachable from `src` in one step. -/
def successors (g : DirectedRelGraph) (src : EClassId) : List EClassId :=
  g.edges.getD src []

/-- Check if a direct edge exists from `src` to `dst`. -/
def hasDirectEdge (g : DirectedRelGraph) (src dst : EClassId) : Bool :=
  (g.successors src).contains dst

/-- Check if `dst` is reachable from `src` via a path. Fuel-bounded BFS. -/
def hasPath (g : DirectedRelGraph) (src dst : EClassId) (fuel : Nat := 100) : Bool :=
  go [src] {} fuel
where
  go : List EClassId → Std.HashSet EClassId → Nat → Bool
    | [], _, _ => false
    | _, _, 0 => false
    | cur :: rest, visited, fuel + 1 =>
      if cur == dst then true
      else if visited.contains cur then go rest visited fuel
      else
        let succs := g.successors cur
        go (rest ++ succs) (visited.insert cur) fuel

/-- Collect all edges as (src, dst) pairs. -/
def allEdges (g : DirectedRelGraph) : List (EClassId × EClassId) :=
  (g.edges.toList.map fun (src, dsts) => dsts.map fun dst => (src, dst)).flatten

/-- Canonicalize all edges using a find function (e.g., UF root).
    Maps each edge (src, dst) → (find src, find dst), deduplicating. -/
def canonicalize (g : DirectedRelGraph) (find : EClassId → EClassId) : DirectedRelGraph :=
  g.allEdges.foldl (fun acc (src, dst) =>
    let src' := find src
    let dst' := find dst
    if acc.hasDirectEdge src' dst' then acc
    else acc.addEdge src' dst') DirectedRelGraph.empty


end DirectedRelGraph

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Cross-Relation Rules
-- ══════════════════════════════════════════════════════════════════

/-- A cross-relation rule promotes directed relation evidence to equality.
    The canonical example is antisymmetry: a ≤ b ∧ b ≤ a → a = b. -/
structure CrossRelationRule (Val : Type) where
  name : String
  rel1 : Val → Val → Prop
  rel2 : Val → Val → Prop
  soundness : ∀ (a b : Val), rel1 a b → rel2 b a → a = b

/-- Antisymmetry cross-rule for a partial order. -/
def CrossRelationRule.antisymmetry (Val : Type) (R : Val → Val → Prop)
    (h : ∀ a b, R a b → R b a → a = b) : CrossRelationRule Val where
  name := "antisymmetry"
  rel1 := R
  rel2 := R
  soundness := h

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Proof Composition
-- ══════════════════════════════════════════════════════════════════

/-- Composition entry: how to combine two relations into a third. -/
structure ProofCompositionEntry (Val : Type) where
  rel1 : Val → Val → Prop
  rel2 : Val → Val → Prop
  resultRel : Val → Val → Prop
  compose : ∀ (a b c : Val), rel1 a b → rel2 b c → resultRel a c

/-- Proof composition table: a registry of known composition rules. -/
structure ProofCompositionTable (Val : Type) where
  entries : List (ProofCompositionEntry Val) := []

namespace ProofCompositionTable

def empty {Val : Type} : ProofCompositionTable Val := {}

def addEntry {Val : Type} (t : ProofCompositionTable Val) (e : ProofCompositionEntry Val) :
    ProofCompositionTable Val where
  entries := e :: t.entries

/-- Standard composition: Eq on left preserves any relation. -/
def eqLeftEntry {Val : Type} (R : Val → Val → Prop) : ProofCompositionEntry Val where
  rel1 := Eq
  rel2 := R
  resultRel := R
  compose := fun _ _ _ hab hbc => hab ▸ hbc

/-- Standard composition: Eq on right preserves any relation. -/
def eqRightEntry {Val : Type} (R : Val → Val → Prop) : ProofCompositionEntry Val where
  rel1 := R
  rel2 := Eq
  resultRel := R
  compose := fun _ _ _ hab hbc => hbc ▸ hab

/-- Transitivity composition for a transitive relation. -/
def transitiveEntry {Val : Type} (R : Val → Val → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) : ProofCompositionEntry Val where
  rel1 := R
  rel2 := R
  resultRel := R
  compose := htrans

end ProofCompositionTable

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Basic Theorems
-- ══════════════════════════════════════════════════════════════════

/-- DirectedRelGraph.empty has no edges. -/
theorem DirectedRelGraph.empty_noEdges :
    DirectedRelGraph.empty.numEdges = 0 := by rfl

/-- Roundtrip SoundRewriteRule → SoundRelationRule Eq → SoundRewriteRule preserves name. -/
theorem SoundRelationRule.roundtrip_name {Op Expr Val : Type} [BEq Op] [Hashable Op]
    (r : SoundRewriteRule Op Expr Val) :
    r.toRelationRule.toEqualityRule.name = r.name := by rfl

-- ══════════════════════════════════════════════════════════════════
-- Section 6: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Empty graph has 0 edges. -/
example : DirectedRelGraph.empty.numEdges = 0 := by rfl

/-- addEdge increments edge count. -/
example : (DirectedRelGraph.empty.addEdge 1 2).numEdges = 1 := by rfl

end LambdaSat
