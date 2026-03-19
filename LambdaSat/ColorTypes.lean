/-
  LambdaSat — Colored E-Graph Types
  Fase 14 Subfase 1: Foundation types for Layer 2 (Easter Egg colored equalities).

  Colored e-graphs maintain multiple congruence relations in a single structure.
  Each "color" represents an assumption under which additional equalities hold.
  Colors form a hierarchy: every color is a coarsening of its parent
  (≅ ⊆ ≅_c for every color c).

  Key types:
  - `ColorId`: identifier for a color layer
  - `ColorHierarchy`: tree of colors with parent pointers
  - `SmallUF`: delta union-find storing only additional merges on top of parent layer

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)
             Singher, "Easter Egg" (FMCAD 2024)
-/
import LambdaSat.UnionFind
import Std.Data.HashMap

namespace LambdaSat

-- ══════════════════════════════════════════════════════════════════
-- Section 1: Color Identifiers
-- ══════════════════════════════════════════════════════════════════

/-- Identifier for a color layer. 0 = root (black/base) layer. -/
abbrev ColorId := Nat

/-- The root color represents the base (unconditional) congruence. -/
def colorRoot : ColorId := 0

-- ══════════════════════════════════════════════════════════════════
-- Section 2: Color Hierarchy
-- ══════════════════════════════════════════════════════════════════

/-- Tree of colors. Each non-root color has exactly one parent.
    The hierarchy defines coarsening: ≅_{parent(c)} ⊆ ≅_c for all c.

    Invariant: the parent graph is acyclic and every path leads to root. -/
structure ColorHierarchy where
  /-- Map from child color → parent color. Root (0) has no entry. -/
  parentOf : Std.HashMap ColorId ColorId := {}
  /-- Number of active colors (including root). -/
  numColors : Nat := 1

namespace ColorHierarchy

def empty : ColorHierarchy := {}

/-- Add a new color as child of `par`. Returns (newColorId, updatedHierarchy). -/
def addColor (h : ColorHierarchy) (par : ColorId) : ColorId × ColorHierarchy :=
  let newId := h.numColors
  (newId, { parentOf := h.parentOf.insert newId par
            numColors := h.numColors + 1 })

/-- Get the parent of a color. Root returns itself. -/
def getParent (h : ColorHierarchy) (c : ColorId) : ColorId :=
  if c == colorRoot then colorRoot
  else h.parentOf.getD c colorRoot

/-- Check if `ancestor` is an ancestor of `c` (inclusive). Fuel-bounded. -/
def isAncestor (h : ColorHierarchy) (c ancestor : ColorId) : Bool :=
  go c h.numColors
where
  go (current : ColorId) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      if current == ancestor then true
      else if current == colorRoot then false
      else go (h.getParent current) fuel

/-- Collect all ancestors of `c` (from c to root, inclusive). Fuel-bounded. -/
def ancestors (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  go c h.numColors []
where
  go (current : ColorId) : Nat → List ColorId → List ColorId
    | 0, acc => acc.reverse
    | fuel + 1, acc =>
      let acc' := current :: acc
      if current == colorRoot then acc'.reverse
      else go (h.getParent current) fuel acc'

/-- Collect all direct children of `c`. -/
def getChildren (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  h.parentOf.toList.filterMap fun (child, par) =>
    if par == c then some child else none

/-- Collect all descendants of `c` (breadth-first, including c). Fuel-bounded. -/
def descendants (h : ColorHierarchy) (c : ColorId) : List ColorId :=
  go [c] [] h.numColors
where
  go : List ColorId → List ColorId → Nat → List ColorId
    | [], acc, _ => acc.reverse
    | _, acc, 0 => acc.reverse
    | cur :: rest, acc, fuel + 1 =>
      let kids := h.getChildren cur
      go (rest ++ kids) (cur :: acc) fuel

end ColorHierarchy

-- ══════════════════════════════════════════════════════════════════
-- Section 3: Small (Delta) Union-Find
-- ══════════════════════════════════════════════════════════════════

/-- Delta union-find: stores only ADDITIONAL merges on top of a parent layer.
    Used to represent colored equivalences efficiently.

    The full equivalence for a color c is:
      `find_c(e) = deltaFind(c, parentLayerFind(e))`
    where parentLayerFind resolves through ancestor colors down to the base UF. -/
structure SmallUF where
  /-- Additional parent pointers (delta over parent layer). -/
  delta : Std.HashMap EClassId EClassId := {}

namespace SmallUF

def empty : SmallUF := {}

def size (suf : SmallUF) : Nat := suf.delta.size

/-- Find the representative in this delta layer.
    Follows delta parent pointers until reaching a fixed point.
    `fuel` ensures totality. -/
def deltaFind (suf : SmallUF) (id : EClassId) : Nat → EClassId
  | 0 => id
  | fuel + 1 =>
    match suf.delta.get? id with
    | none => id
    | some par =>
      if par == id then id
      else deltaFind suf par fuel

/-- Find representative through the full color hierarchy.
    1. First resolve `id` through the parent layer (via `parentFind`)
    2. Then resolve through this color's delta merges -/
def find (suf : SmallUF) (parentFind : EClassId → EClassId) (id : EClassId)
    (fuel : Nat := 100) : EClassId :=
  deltaFind suf (parentFind id) fuel

/-- Merge two e-class ids in this delta layer.
    Maps `a`'s representative to `b`'s representative. -/
def merge (suf : SmallUF) (a b : EClassId) (fuel : Nat := 100) : SmallUF :=
  let repA := deltaFind suf a fuel
  let repB := deltaFind suf b fuel
  if repA == repB then suf
  else { delta := suf.delta.insert repA repB }

/-- Check equivalence in this delta layer (given parent layer find). -/
def equiv (suf : SmallUF) (parentFind : EClassId → EClassId) (a b : EClassId)
    (fuel : Nat := 100) : Bool :=
  find suf parentFind a fuel == find suf parentFind b fuel

end SmallUF

-- ══════════════════════════════════════════════════════════════════
-- Section 4: Well-Formedness and Basic Theorems
-- ══════════════════════════════════════════════════════════════════

/-- A SmallUF is well-formed if deltaFind always terminates within `size` steps. -/
def SmallUF.WellFormed (suf : SmallUF) : Prop :=
  ∀ id, SmallUF.deltaFind suf id suf.size = SmallUF.deltaFind suf id (suf.size + 1)

/-- The empty SmallUF is trivially well-formed. -/
theorem SmallUF.empty_wellFormed : SmallUF.empty.WellFormed := by
  intro id
  simp [SmallUF.WellFormed, SmallUF.empty, SmallUF.deltaFind, SmallUF.size]

/-- deltaFind with 0 fuel returns the input unchanged. -/
theorem SmallUF.deltaFind_zero (suf : SmallUF) (id : EClassId) :
    SmallUF.deltaFind suf id 0 = id := by
  rfl

/-- If id has no delta entry, deltaFind returns id immediately. -/
theorem SmallUF.deltaFind_root (suf : SmallUF) (id : EClassId) (fuel : Nat)
    (h : suf.delta.get? id = none) :
    SmallUF.deltaFind suf id (fuel + 1) = id := by
  simp only [SmallUF.deltaFind, h]

/-- getParent of root is root. -/
theorem ColorHierarchy.getParent_root (h : ColorHierarchy) :
    h.getParent colorRoot = colorRoot := by
  simp [ColorHierarchy.getParent, colorRoot]

/-- deltaFind on empty SmallUF always returns the input. -/
theorem SmallUF.empty_deltaFind (id : EClassId) : ∀ fuel, SmallUF.empty.deltaFind id fuel = id
  | 0 => rfl
  | _ + 1 => by simp [SmallUF.deltaFind, SmallUF.empty]

/-- After inserting repA→repB where repA had no entry (root), deltaFind
    preserves any valuation v where v(repA)=v(repB) and v was preserved
    by the original deltaFind. -/
theorem SmallUF.deltaFind_insert_preserves_val {Val : Type}
    (suf : SmallUF) (repA repB : EClassId) (v : EClassId → Val)
    (hroot : suf.delta.get? repA = none)
    (hrootB : suf.delta.get? repB = none)
    (hab : v repA = v repB)
    (hold : ∀ id fuel, v (suf.deltaFind id fuel) = v id) :
    ∀ id fuel, v ({ delta := suf.delta.insert repA repB : SmallUF }.deltaFind id fuel) = v id
  | _, 0 => rfl
  | id, fuel + 1 => by
    unfold SmallUF.deltaFind
    -- The lookup is on the inserted HashMap
    show v (match ({ delta := suf.delta.insert repA repB : SmallUF }).delta.get? id with
      | none => id | some par => if par == id then id
        else SmallUF.deltaFind { delta := suf.delta.insert repA repB } par fuel) = v id
    by_cases hid : repA = id
    · -- id = repA: the insert gives us repB
      subst hid
      simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true,
                  ↓reduceIte]
      by_cases hbeq : repB == repA
      · -- repB = repA (degenerate)
        simp [hbeq]
      · -- repB ≠ repA: follow to repB, which is a root in the new UF
        simp [hbeq]
        -- deltaFind on new UF at repB: repB ≠ repA so lookup = old lookup = none (root)
        have hrootB' : ({ delta := suf.delta.insert repA repB : SmallUF }).delta.get? repB = none := by
          simp only [show ({ delta := suf.delta.insert repA repB : SmallUF }).delta =
            suf.delta.insert repA repB from rfl,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
            beq_eq_false_iff_ne.mpr (fun h => hbeq (beq_iff_eq.mpr h.symm))]
          simp only [Bool.false_eq_true, ↓reduceIte, ← Std.HashMap.get?_eq_getElem?, hrootB]
        have := deltaFind_insert_preserves_val suf repA repB v hroot hrootB hab hold repB fuel
        exact this.trans hab.symm
    · -- id ≠ repA: insert doesn't affect this lookup
      have hinsert_ne : (suf.delta.insert repA repB).get? id = suf.delta.get? id := by
        simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        simp [beq_eq_false_iff_ne.mpr hid]
      show v (match (suf.delta.insert repA repB).get? id with
        | none => id | some par => if par == id then id
          else SmallUF.deltaFind { delta := suf.delta.insert repA repB } par fuel) = v id
      rw [hinsert_ne]
      -- Now match on old delta WITH binding
      match hget : suf.delta.get? id with
      | none => rfl
      | some par =>
        simp only []
        split
        · rfl
        · rename_i hpar_ne_id
          have hrec := deltaFind_insert_preserves_val suf repA repB v hroot hrootB hab hold par fuel
          -- Need: v par = v id
          -- From hold: suf.deltaFind id (fuel+1) = suf.deltaFind par fuel
          --   (because get? id = some par and par ≠ id)
          have h2 := hold id (fuel + 1)
          have h1 := hold par fuel
          have hstep : v (suf.deltaFind id (fuel + 1)) = v (suf.deltaFind par fuel) := by
            congr 1; show (match suf.delta.get? id with
              | none => id
              | some par => if par == id then id else suf.deltaFind par fuel) = _
            rw [hget]; simp [hpar_ne_id]
          exact hrec.trans (h1.symm.trans (hstep.symm ▸ h2))

-- ══════════════════════════════════════════════════════════════════
-- Section 5: Smoke tests
-- ══════════════════════════════════════════════════════════════════

/-- Empty hierarchy has 1 color (root). -/
example : ColorHierarchy.empty.numColors = 1 := by rfl

/-- SmallUF.empty has size 0. -/
example : SmallUF.empty.size = 0 := by native_decide

/-- deltaFind on empty SmallUF returns the input. -/
example : SmallUF.deltaFind SmallUF.empty 42 10 = 42 := by native_decide

end LambdaSat
