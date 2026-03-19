/-
  LambdaSat — Colored Hashcons: Differential Per-Color Hashconsing
  Fase 15 Subfase 1: Layer 2 core operation.

  Each color maintains a DELTA hashcons table that stores only entries
  that differ from the parent color. Lookup falls back through the color
  hierarchy until an entry is found (or reaches the base hashcons).

  This is the colored analogue of the base `EGraph.hashcons` field.

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)
             Singher, "Easter Egg" (FMCAD 2024)

  Key results:
  - `lookup_insert_same`: inserted entry is immediately visible
  - `lookup_parent_fallback`: missing entries fall back to parent
  - `lookup_insert_ne`: insert doesn't affect unrelated lookups
-/
import LambdaSat.Core
import LambdaSat.ColorTypes
import Std.Data.HashMap

set_option autoImplicit false

namespace LambdaSat

/-! ## ColoredHashcons -/

/-- Delta hashcons for a single color layer.
    Stores only entries that DIFFER from the parent color's hashcons.
    Lookup: check delta first, fall back to parent lookup. -/
structure ColoredHashcons (Op : Type) [BEq Op] [Hashable Op] where
  /-- Delta entries: canonical ENode -> EClassId for THIS color only. -/
  delta : Std.HashMap (ENode Op) EClassId := {}

namespace ColoredHashcons

variable {Op : Type} [BEq Op] [Hashable Op]

/-- Empty delta hashcons (inherits everything from parent). -/
def empty : ColoredHashcons Op := { delta := {} }

/-- Number of delta entries (differences from parent). -/
def size (ch : ColoredHashcons Op) : Nat := ch.delta.size

/-- Look up an e-node in the delta hashcons only (no fallback). -/
def deltaLookup (ch : ColoredHashcons Op) (node : ENode Op) : Option EClassId :=
  ch.delta.get? node

/-- Look up an e-node: check delta first, fall back to parent lookup.
    `parentLookup` is the lookup function for the parent color (or base hashcons). -/
def lookup (ch : ColoredHashcons Op) (parentLookup : ENode Op → Option EClassId)
    (node : ENode Op) : Option EClassId :=
  match ch.delta.get? node with
  | some id => some id
  | none => parentLookup node

/-- Insert an entry into the delta hashcons. -/
def insert (ch : ColoredHashcons Op) (node : ENode Op) (id : EClassId) : ColoredHashcons Op :=
  { delta := ch.delta.insert node id }

/-- Remove an entry from the delta hashcons (reverts to parent behavior). -/
def erase (ch : ColoredHashcons Op) (node : ENode Op) : ColoredHashcons Op :=
  { delta := ch.delta.erase node }

end ColoredHashcons

/-! ## ColoredHashcons theorems -/

section Theorems

variable {Op : Type} [BEq Op] [Hashable Op] [LawfulBEq Op] [LawfulHashable Op]

/-- After inserting (node, id), delta lookup of node returns id. -/
theorem ColoredHashcons.deltaLookup_insert_same (ch : ColoredHashcons Op)
    (node : ENode Op) (id : EClassId) :
    (ch.insert node id).deltaLookup node = some id := by
  simp [deltaLookup, insert, Std.HashMap.get?_eq_getElem?]

/-- Insert for a different node does not affect delta lookup. -/
theorem ColoredHashcons.deltaLookup_insert_ne (ch : ColoredHashcons Op)
    (node other : ENode Op) (id : EClassId) (hne : node ≠ other) :
    (ch.insert other id).deltaLookup node = ch.deltaLookup node := by
  simp only [deltaLookup, insert, Std.HashMap.get?_eq_getElem?,
             Std.HashMap.getElem?_insert]
  simp [beq_eq_false_iff_ne.mpr (Ne.symm hne)]

/-- After inserting (node, id), full lookup of node returns id
    regardless of parent. -/
theorem ColoredHashcons.lookup_insert_same (ch : ColoredHashcons Op)
    (parentLookup : ENode Op → Option EClassId)
    (node : ENode Op) (id : EClassId) :
    (ch.insert node id).lookup parentLookup node = some id := by
  simp [lookup, insert, Std.HashMap.get?_eq_getElem?]

/-- If a node is NOT in the delta, lookup falls back to parent. -/
theorem ColoredHashcons.lookup_parent_fallback (ch : ColoredHashcons Op)
    (parentLookup : ENode Op → Option EClassId)
    (node : ENode Op) (h : ch.deltaLookup node = none) :
    ch.lookup parentLookup node = parentLookup node := by
  simp only [lookup, deltaLookup] at h ⊢
  rw [h]

/-- Insert for a different node does not affect full lookup. -/
theorem ColoredHashcons.lookup_insert_ne (ch : ColoredHashcons Op)
    (parentLookup : ENode Op → Option EClassId)
    (node other : ENode Op) (id : EClassId) (hne : node ≠ other) :
    (ch.insert other id).lookup parentLookup node = ch.lookup parentLookup node := by
  simp only [lookup, insert, Std.HashMap.get?_eq_getElem?,
             Std.HashMap.getElem?_insert]
  have : (other == node) = false := beq_eq_false_iff_ne.mpr (Ne.symm hne)
  simp [this]

/-- The empty delta has no entries. -/
theorem ColoredHashcons.deltaLookup_empty (node : ENode Op) :
    (ColoredHashcons.empty : ColoredHashcons Op).deltaLookup node = none := by
  simp [deltaLookup, empty, Std.HashMap.get?_eq_getElem?]

/-- On empty delta, lookup always falls back to parent. -/
theorem ColoredHashcons.lookup_empty (parentLookup : ENode Op → Option EClassId)
    (node : ENode Op) :
    (ColoredHashcons.empty : ColoredHashcons Op).lookup parentLookup node =
    parentLookup node := by
  simp [lookup, empty, Std.HashMap.get?_eq_getElem?]

end Theorems

/-! ## Multi-color hashcons management -/

/-- Collection of per-color hashcons tables.
    Maps each non-root color to its delta hashcons. -/
structure ColoredHashconsMap (Op : Type) [BEq Op] [Hashable Op] where
  tables : Std.HashMap ColorId (ColoredHashcons Op) := {}

namespace ColoredHashconsMap

variable {Op : Type} [BEq Op] [Hashable Op]

def empty : ColoredHashconsMap Op := { tables := {} }

/-- Get the delta hashcons for a color, defaulting to empty. -/
def getHashcons (m : ColoredHashconsMap Op) (c : ColorId) : ColoredHashcons Op :=
  match m.tables.get? c with
  | some ch => ch
  | none => ColoredHashcons.empty

/-- Set the delta hashcons for a color. -/
def setHashcons (m : ColoredHashconsMap Op) (c : ColorId) (ch : ColoredHashcons Op) :
    ColoredHashconsMap Op :=
  { tables := m.tables.insert c ch }

/-- Insert an entry into a specific color's hashcons. -/
def insertAt (m : ColoredHashconsMap Op) (c : ColorId) (node : ENode Op) (id : EClassId) :
    ColoredHashconsMap Op :=
  setHashcons m c ((getHashcons m c).insert node id)

/-- Resolve a hashcons lookup through the color hierarchy.
    Walks from color `c` up to the root, checking delta entries at each level.
    Falls back to `baseLookup` at the root. -/
def hierarchicalLookup (m : ColoredHashconsMap Op) (hierarchy : ColorHierarchy)
    (baseLookup : ENode Op → Option EClassId) (c : ColorId) (node : ENode Op) : Option EClassId :=
  go c hierarchy.numColors
where
  go (current : ColorId) : Nat → Option EClassId
    | 0 => baseLookup node
    | fuel + 1 =>
      match (getHashcons m current).deltaLookup node with
      | some id => some id
      | none =>
        if current == colorRoot then baseLookup node
        else go (hierarchy.getParent current) fuel

end ColoredHashconsMap

/-! ## Smoke tests -/

-- Test with a concrete Op type
private inductive TestOp where
  | lit : Nat → TestOp
  | add : EClassId → EClassId → TestOp
  deriving BEq, Hashable

#eval do
  let ch : ColoredHashcons TestOp := ColoredHashcons.empty
  let node := ENode.mk (TestOp.lit 42)
  let ch2 := ch.insert node 7
  let r1 := ch2.deltaLookup node
  let r2 := ch.deltaLookup node
  return s!"After insert: deltaLookup = {r1}, before: {r2}"

#eval do
  let ch : ColoredHashcons TestOp := ColoredHashcons.empty
  let node := ENode.mk (TestOp.lit 42)
  let parent := fun _ => some 99  -- parent always returns 99
  let r1 := ch.lookup parent node  -- should fallback to parent
  let ch2 := ch.insert node 7
  let r2 := ch2.lookup parent node  -- should return 7 (delta overrides)
  return s!"Empty fallback: {r1}, after insert: {r2}"

end LambdaSat
