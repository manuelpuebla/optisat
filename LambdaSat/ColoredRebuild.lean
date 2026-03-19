/-
  LambdaSat — ColoredRebuild: Per-Color Congruence Closure
  Fase 15 Subfase 3: Layer 2 core operation.

  After mergeUnderColor, e-nodes may become congruent under a color
  (their canonical forms under the color's compositeFind match).
  ColoredRebuild detects these new congruences and emits additional
  colored merges.

  The algorithm:
  1. For each class id in the color's worklist
  2. Canonicalize all e-nodes using the color's compositeFind
  3. Check canonical forms against the color's delta hashcons
  4. If a match is found, emit a colored merge
  5. Otherwise, insert into the delta hashcons

  This parallels SemanticSpec.lean's processClass/rebuildF but operates
  on the colored layer only.

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)

  Key results:
  - `coloredCanonicalizeNode`: canonicalize an e-node under a color
  - `coloredProcessClass`: process one class for colored congruences
  - `coloredRebuildStep`: one full rebuild pass under a color
  - `coloredCanonicalizeNode_preserves_shape`: skeleton unchanged
-/
import LambdaSat.Core
import LambdaSat.ColorTypes
import LambdaSat.ColoredHashcons
import LambdaSat.ColoredMerge

set_option autoImplicit false

namespace LambdaSat

variable {Op : Type} [BEq Op] [Hashable Op] [NodeOps Op]

/-! ## Colored Canonicalization -/

/-- Canonicalize an e-node under a specific color.
    Replaces each child e-class id with its representative under color c. -/
def coloredCanonicalizeNode (cl : ColoredLayer Op) (baseFind : EClassId → EClassId)
    (c : ColorId) (node : ENode Op) (fuel : Nat) : ENode Op :=
  node.mapChildren (fun child => ColoredLayer.findUnderColor cl baseFind c child fuel)

/-- Canonicalization preserves the operation skeleton (same shape, different children). -/
theorem coloredCanonicalizeNode_preserves_shape (cl : ColoredLayer Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (node : ENode Op) (fuel : Nat) :
    (coloredCanonicalizeNode cl baseFind c node fuel).mapChildren (fun _ => (0 : EClassId)) =
    node.mapChildren (fun _ => (0 : EClassId)) := by
  simp only [coloredCanonicalizeNode, ENode.mapChildren]
  congr 1
  have h1 := NodeOps.mapChildren_replaceChildren
    (fun child => ColoredLayer.findUnderColor cl baseFind c child fuel) node.op
  rw [h1]
  exact NodeOps.replaceChildren_sameShape node.op _ (by simp [List.length_map])

/-! ## Colored Process Class -/

/-- Result of processing one e-class under a color: new merges discovered. -/
structure ColoredProcessResult (Op : Type) [BEq Op] [Hashable Op] where
  /-- Updated colored layer (with new hashcons entries) -/
  layer : ColoredLayer Op
  /-- New merge pairs discovered by congruence -/
  newMerges : List (EClassId × EClassId)

/-- Process a single e-class for colored congruences.
    For each e-node in the class:
    1. Canonicalize under color c
    2. Look up canonical form in colored hashcons
    3. If found: emit merge (existing id, classId)
    4. If not: insert into colored hashcons -/
def coloredProcessClass (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (classId : EClassId)
    (fuel : Nat) : ColoredProcessResult Op :=
  let canonId := ColoredLayer.findUnderColor cl baseFind c classId fuel
  match baseGraph.classes.get? canonId with
  | none => { layer := cl, newMerges := [] }
  | some eclass =>
    let baseLookup := fun (node : ENode Op) => baseGraph.hashcons.get? node
    eclass.nodes.foldl (fun (acc : ColoredProcessResult Op) node =>
      let canonNode := coloredCanonicalizeNode acc.layer baseFind c node fuel
      let chm := acc.layer.colorHashcons
      match ColoredHashconsMap.hierarchicalLookup chm acc.layer.hierarchy baseLookup c canonNode with
      | some existingId =>
        if existingId == canonId then acc
        else { layer := acc.layer
               newMerges := acc.newMerges ++ [(existingId, canonId)] }
      | none =>
        { layer := { acc.layer with
            colorHashcons := ColoredHashconsMap.setHashcons chm c
              ((ColoredHashconsMap.getHashcons chm c).insert canonNode canonId) }
          newMerges := acc.newMerges }
    ) { layer := cl, newMerges := [] }

/-! ## Colored Rebuild Step -/

/-- One full rebuild pass for a color: process all classes in the worklist,
    collect new merges, apply them, add newly merged classes back to worklist. -/
def coloredRebuildStep (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (fuel : Nat) :
    ColoredLayer Op :=
  let worklist := ColoredLayer.getWorklist cl c
  let cl' := ColoredLayer.clearWorklist cl c
  -- Process each class in the worklist
  let (cl'', allMerges) := worklist.foldl (fun (acc : ColoredLayer Op × List (EClassId × EClassId)) classId =>
    let result := coloredProcessClass acc.1 baseGraph baseFind c classId fuel
    (result.layer, acc.2 ++ result.newMerges)
  ) (cl', [])
  -- Apply all discovered merges
  let cl''' := allMerges.foldl (fun acc (a, b) =>
    (ColoredLayer.mergeUnderColor acc baseFind c a b fuel).1
  ) cl''
  cl'''

/-- Fuel-bounded colored rebuild: iterate rebuild steps up to `fuel` times.
    Terminates when worklist is empty or fuel runs out. -/
def coloredRebuildF (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (fuel rebuildFuel : Nat) :
    ColoredLayer Op :=
  match rebuildFuel with
  | 0 => cl
  | n + 1 =>
    let worklist := ColoredLayer.getWorklist cl c
    if worklist.isEmpty then cl
    else
      let cl' := coloredRebuildStep cl baseGraph baseFind c fuel
      coloredRebuildF cl' baseGraph baseFind c fuel n

/-! ## Properties -/

/-- Rebuilding an empty worklist is a no-op. -/
theorem coloredRebuildF_empty_worklist (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (fuel rebuildFuel : Nat)
    (h : (ColoredLayer.getWorklist cl c).isEmpty = true) :
    coloredRebuildF cl baseGraph baseFind c fuel (rebuildFuel + 1) = cl := by
  simp [coloredRebuildF, h]

/-- Processing a class that doesn't exist in the base graph is a no-op. -/
theorem coloredProcessClass_missing (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (baseFind : EClassId → EClassId) (c : ColorId) (classId : EClassId) (fuel : Nat)
    (h : baseGraph.classes.get? (ColoredLayer.findUnderColor cl baseFind c classId fuel) = none) :
    (coloredProcessClass cl baseGraph baseFind c classId fuel).newMerges = [] := by
  simp only [coloredProcessClass]
  rw [h]

/-! ## Smoke tests -/

private inductive CRTestOp where
  | lit : Nat → CRTestOp
  | add : EClassId → EClassId → CRTestOp
  deriving BEq, Hashable

instance : NodeOps CRTestOp where
  children | .lit _ => [] | .add a b => [a, b]
  mapChildren f | .lit n => .lit n | .add a b => .add (f a) (f b)
  replaceChildren op ids := match op, ids with
    | .lit n, _ => .lit n
    | .add _ _, [a, b] => .add a b
    | op, _ => op
  localCost | .lit _ => 1 | .add _ _ => 2
  mapChildren_children := by intro f op; cases op <;> simp_all
  mapChildren_id := by intro op; cases op <;> rfl
  replaceChildren_children := by
    intro op ids h
    cases op with
    | lit n => simp_all (config := { decide := true })
    | add a b =>
      simp only [] at h
      match ids, h with
      | [x, y], _ => rfl
  replaceChildren_sameShape := by
    intro op ids h
    cases op with
    | lit n => simp_all (config := { decide := true })
    | add a b =>
      simp only [] at h
      match ids, h with
      | [x, y], _ => rfl
  mapChildren_replaceChildren := by
    intro f op; cases op <;> simp_all

#eval
  let cl : ColoredLayer CRTestOp := ColoredLayer.empty
  let (c1, cl1) := ColoredLayer.addColor cl colorRoot
  let worklist := ColoredLayer.getWorklist cl1 c1
  s!"Empty worklist test: worklist length = {worklist.length}"

end LambdaSat
