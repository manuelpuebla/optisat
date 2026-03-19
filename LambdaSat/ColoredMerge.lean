/-
  LambdaSat — ColoredMerge: Merge Under Color + Coarsening Invariant
  Fase 15 Subfase 2: Layer 2 core operation (de-risk sketch).

  Implements `mergeUnderColor`: merge two e-classes within a specific
  color layer. The merge is recorded in the color's SmallUF and the
  pair is added to a worklist for colored rebuild (Fase 15.3).

  Key architectural insight: descendant colors automatically maintain
  coarsening through the compositional find function. No explicit
  propagation is needed — this is proven in `compositeFind_coarsening`.

  The coarsening invariant is:
    `∀ a b c, isAncestor(parent, c) → equiv_parent(a, b) → equiv_c(a, b)`

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)
             Singher, "Easter Egg" (FMCAD 2024)

  Key results:
  - `mergeUnderColor`: merge two e-classes within a color
  - `compositeFind_coarsening`: descendant find preserves parent equivalences
  - `mergeUnderColor_idempotent`: merging already-equivalent classes is a no-op
-/
import LambdaSat.Core
import LambdaSat.ColorTypes
import LambdaSat.ColoredHashcons
import Std.Data.HashMap

set_option autoImplicit false

namespace LambdaSat

/-! ## Colored Layer -/

/-- The colored layer of a colored e-graph.
    Manages per-color SmallUFs and hashcons tables.
    Layer 1 (base EGraph) is separate and untouched. -/
structure ColoredLayer (Op : Type) [BEq Op] [Hashable Op] where
  /-- Per-color delta union-finds. Each maps extra merges on top of parent. -/
  colorUFs : Std.HashMap ColorId SmallUF := {}
  /-- Per-color delta hashcons tables. -/
  colorHashcons : ColoredHashconsMap Op := ColoredHashconsMap.empty
  /-- Color hierarchy (tree of assumptions). -/
  hierarchy : ColorHierarchy := ColorHierarchy.empty
  /-- Per-color worklists for rebuild (class ids that need congruence closure). -/
  worklists : Std.HashMap ColorId (List EClassId) := {}

/-! ## ColoredLayer operations -/

section ColoredLayerOps

variable {Op : Type} [BEq Op] [Hashable Op]

/-- Empty colored layer (no colors, no merges). -/
def ColoredLayer.empty : ColoredLayer Op :=
  { colorUFs := {}, colorHashcons := ColoredHashconsMap.empty,
    hierarchy := ColorHierarchy.empty, worklists := {} }

/-- Get the SmallUF for a color, defaulting to empty. -/
def ColoredLayer.getUF (cl : ColoredLayer Op) (c : ColorId) : SmallUF :=
  cl.colorUFs.getD c SmallUF.empty

/-- Set the SmallUF for a color. -/
def ColoredLayer.setUF (cl : ColoredLayer Op) (c : ColorId) (suf : SmallUF) :
    ColoredLayer Op :=
  { cl with colorUFs := cl.colorUFs.insert c suf }

/-- Get the worklist for a color, defaulting to empty. -/
def ColoredLayer.getWorklist (cl : ColoredLayer Op) (c : ColorId) : List EClassId :=
  cl.worklists.getD c []

/-- Append to the worklist for a color. -/
def ColoredLayer.addToWorklist (cl : ColoredLayer Op) (c : ColorId)
    (ids : List EClassId) : ColoredLayer Op :=
  let current := ColoredLayer.getWorklist cl c
  { cl with worklists := cl.worklists.insert c (current ++ ids) }

/-- Clear the worklist for a color. -/
def ColoredLayer.clearWorklist (cl : ColoredLayer Op) (c : ColorId) :
    ColoredLayer Op :=
  { cl with worklists := cl.worklists.insert c [] }

/-- Add a new color as child of `parent`. -/
def ColoredLayer.addColor (cl : ColoredLayer Op) (parent : ColorId) :
    ColorId × ColoredLayer Op :=
  let (newId, newHier) := cl.hierarchy.addColor parent
  (newId, { cl with hierarchy := newHier })

end ColoredLayerOps

/-! ## Composite Find -/

/-- Compute the representative of `id` under color `c` by composing
    delta finds through the ancestor chain.

    Given ancestors = [root, c1, c2, ..., c] (from root to target color):
    result = deltaFind_c(deltaFind_c2(...(deltaFind_c1(baseFind(id)))...))

    The root color's "delta" is empty, so its find is the identity.
    The `baseFind` resolves through the base (black) union-find. -/
def compositeFind (colorUFs : Std.HashMap ColorId SmallUF) (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) : EClassId :=
  ancestors.foldl (fun acc c =>
    (colorUFs.getD c SmallUF.empty).deltaFind acc fuel
  ) (baseFind id)

section ColoredFindMerge

variable {Op : Type} [BEq Op] [Hashable Op]

/-- Convenience: composite find using the color hierarchy. -/
def ColoredLayer.findUnderColor (cl : ColoredLayer Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (id : EClassId)
    (fuel : Nat := 100) : EClassId :=
  -- ancestors returns [c, ..., root], we need [root, ..., c] for left-to-right composition
  let anc := (cl.hierarchy.ancestors c).reverse
  compositeFind cl.colorUFs anc baseFind fuel id

/-- Check if two e-classes are equivalent under a color. -/
def ColoredLayer.equivUnderColor (cl : ColoredLayer Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (a b : EClassId)
    (fuel : Nat := 100) : Bool :=
  ColoredLayer.findUnderColor cl baseFind c a fuel ==
  ColoredLayer.findUnderColor cl baseFind c b fuel

/-! ## Merge Under Color -/

/-- Merge two e-classes under a specific color.

    1. Finds the representatives of `a` and `b` under color `c`
       (composing through the ancestor chain)
    2. If they're already equivalent, returns unchanged
    3. Otherwise, adds the merge to `c`'s SmallUF
    4. Adds both ids to `c`'s worklist for rebuild

    **No propagation to descendants needed**: descendant colors compose
    their find through `c`'s SmallUF, so they automatically see the merge. -/
def ColoredLayer.mergeUnderColor (cl : ColoredLayer Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (a b : EClassId)
    (fuel : Nat := 100) : ColoredLayer Op × Bool :=
  let repA := ColoredLayer.findUnderColor cl baseFind c a fuel
  let repB := ColoredLayer.findUnderColor cl baseFind c b fuel
  if repA == repB then
    (cl, false)
  else
    let suf := ColoredLayer.getUF cl c
    let suf' := suf.merge repA repB fuel
    let cl' := ColoredLayer.setUF cl c suf'
    let cl'' := ColoredLayer.addToWorklist cl' c [repA, repB]
    (cl'', true)

end ColoredFindMerge

/-! ## Coarsening Invariant -/

/-- The coarsening invariant: if two e-classes are equivalent under
    a parent color, they are also equivalent under any descendant color.

    This is the central safety property of colored e-graphs.
    It ensures that additional assumptions only ADD equalities, never remove them. -/
def CoarseningInvariant (colorUFs : Std.HashMap ColorId SmallUF)
    (hierarchy : ColorHierarchy) (baseFind : EClassId → EClassId) (fuel : Nat) : Prop :=
  ∀ (child parent : ColorId) (a b : EClassId),
    hierarchy.getParent child = parent →
    compositeFind colorUFs (hierarchy.ancestors parent).reverse baseFind fuel a =
    compositeFind colorUFs (hierarchy.ancestors parent).reverse baseFind fuel b →
    compositeFind colorUFs (hierarchy.ancestors child).reverse baseFind fuel a =
    compositeFind colorUFs (hierarchy.ancestors child).reverse baseFind fuel b

/-! ## Key Theorems -/

/-- Core coarsening lemma: if two ids map to the same value after parent-chain find,
    then applying one more deltaFind layer preserves their equality.

    This is the structural reason coarsening is automatic:
    `deltaFind(x) = deltaFind(y)` whenever `x = y` (deltaFind is a function). -/
theorem deltaFind_preserves_eq (suf : SmallUF) (x y : EClassId) (fuel : Nat)
    (h : x = y) : suf.deltaFind x fuel = suf.deltaFind y fuel := by
  rw [h]

/-- compositeFind through a LONGER ancestor chain (parent chain ++ [child])
    preserves equality established by the shorter chain (parent chain).

    This is the key "coarsening for free" result:
    If `compositeFind parentChain baseFind a = compositeFind parentChain baseFind b`
    then `compositeFind (parentChain ++ [child]) baseFind a = ... b`

    Proof: the child's deltaFind receives equal inputs and produces equal outputs. -/
theorem compositeFind_extend_preserves_eq (colorUFs : Std.HashMap ColorId SmallUF)
    (parentChain : List ColorId) (child : ColorId) (baseFind : EClassId → EClassId)
    (fuel : Nat) (a b : EClassId)
    (h : compositeFind colorUFs parentChain baseFind fuel a =
         compositeFind colorUFs parentChain baseFind fuel b) :
    compositeFind colorUFs (parentChain ++ [child]) baseFind fuel a =
    compositeFind colorUFs (parentChain ++ [child]) baseFind fuel b := by
  simp [compositeFind, List.foldl_append] at *
  rw [h]

/-- Coarsening is inherent in the compositional architecture:
    any extension of the ancestor chain preserves equivalences.

    Inductive generalization of `compositeFind_extend_preserves_eq`:
    works for appending any suffix, not just a single color. -/
theorem compositeFind_coarsening (colorUFs : Std.HashMap ColorId SmallUF)
    (parentChain suffix : List ColorId) (baseFind : EClassId → EClassId)
    (fuel : Nat) (a b : EClassId)
    (h : compositeFind colorUFs parentChain baseFind fuel a =
         compositeFind colorUFs parentChain baseFind fuel b) :
    compositeFind colorUFs (parentChain ++ suffix) baseFind fuel a =
    compositeFind colorUFs (parentChain ++ suffix) baseFind fuel b := by
  simp [compositeFind, List.foldl_append] at *
  rw [h]

/-- Merging already-equivalent classes is a no-op. -/
theorem mergeUnderColor_idempotent {Op : Type} [BEq Op] [Hashable Op]
    (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (c : ColorId) (a b : EClassId) (fuel : Nat)
    (h_equiv : ColoredLayer.equivUnderColor cl baseFind c a b fuel = true) :
    (ColoredLayer.mergeUnderColor cl baseFind c a b fuel).2 = false := by
  simp only [ColoredLayer.mergeUnderColor, ColoredLayer.equivUnderColor] at *
  simp [h_equiv]

/-- compositeFind on an empty chain is just baseFind. -/
theorem compositeFind_nil (colorUFs : Std.HashMap ColorId SmallUF)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind colorUFs [] baseFind fuel id = baseFind id := by
  simp [compositeFind]

/-- compositeFind on a singleton chain applies one deltaFind after baseFind. -/
theorem compositeFind_singleton (colorUFs : Std.HashMap ColorId SmallUF)
    (c : ColorId) (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind colorUFs [c] baseFind fuel id =
    (colorUFs.getD c SmallUF.empty).deltaFind (baseFind id) fuel := by
  simp [compositeFind]

/-- compositeFind with empty colorUFs is just baseFind (no colors modify the result). -/
theorem compositeFind_empty_colorUFs (ancestors : List ColorId)
    (baseFind : EClassId → EClassId) (fuel : Nat) (id : EClassId) :
    compositeFind (∅ : Std.HashMap ColorId SmallUF) ancestors baseFind fuel id = baseFind id := by
  simp only [compositeFind]
  induction ancestors with
  | nil => simp [List.foldl]
  | cons c rest ih =>
    simp only [List.foldl]
    have hget : (∅ : Std.HashMap ColorId SmallUF).getD c SmallUF.empty = SmallUF.empty :=
      Std.HashMap.getD_empty
    rw [hget, SmallUF.empty_deltaFind]
    exact ih

/-- equivUnderColor on an empty colored layer reduces to baseFind equality. -/
theorem equivUnderColor_empty_layer {Op : Type} [BEq Op] [Hashable Op]
    (baseFind : EClassId → EClassId)
    (c : ColorId) (a b : EClassId) (fuel : Nat) :
    ColoredLayer.equivUnderColor (ColoredLayer.empty : ColoredLayer Op) baseFind c a b fuel =
    (baseFind a == baseFind b) := by
  simp only [ColoredLayer.equivUnderColor, ColoredLayer.findUnderColor, ColoredLayer.empty]
  congr 1 <;> exact compositeFind_empty_colorUFs _ baseFind fuel _

/-! ## Smoke tests -/

private inductive CMTestOp where
  | lit : Nat → CMTestOp
  | add : EClassId → EClassId → CMTestOp
  deriving BEq, Hashable

-- Test basic merge under color
#eval do
  let cl : ColoredLayer CMTestOp := ColoredLayer.empty
  let (c1, cl1) := ColoredLayer.addColor cl colorRoot
  let baseFind := fun id => id
  let (cl2, changed) := ColoredLayer.mergeUnderColor cl1 baseFind c1 10 20 100
  let eq := ColoredLayer.equivUnderColor cl2 baseFind c1 10 20 100
  return s!"color={c1}, merged={changed}, equiv={eq}"

-- Test that base layer is unaffected
#eval do
  let cl : ColoredLayer CMTestOp := ColoredLayer.empty
  let (c1, cl1) := ColoredLayer.addColor cl colorRoot
  let baseFind := fun id => id
  let (cl2, _) := ColoredLayer.mergeUnderColor cl1 baseFind c1 10 20 100
  let eqRoot := ColoredLayer.equivUnderColor cl2 baseFind colorRoot 10 20 100
  let eqC1 := ColoredLayer.equivUnderColor cl2 baseFind c1 10 20 100
  return s!"root_equiv={eqRoot}, c1_equiv={eqC1}"

-- Test coarsening: merge under parent, check child sees it too
#eval do
  let cl : ColoredLayer CMTestOp := ColoredLayer.empty
  let (c1, cl1) := ColoredLayer.addColor cl colorRoot
  let (c2, cl2) := ColoredLayer.addColor cl1 c1
  let baseFind := fun id => id
  let (cl3, _) := ColoredLayer.mergeUnderColor cl2 baseFind c1 10 20 100
  let eqC2 := ColoredLayer.equivUnderColor cl3 baseFind c2 10 20 100
  return s!"child_c2_sees_parent_merge={eqC2}"

end LambdaSat
