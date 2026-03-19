/-
  LambdaSat — ColoredPruning: Remove Redundant Colored E-Nodes
  Fase 15 Subfase 5: Layer 2 optimization.

  Removes e-nodes from a color's delta hashcons that are subsumed by
  ancestor-color equivalences. If an ancestor color already merges the
  children of an e-node, the node's entry in the descendant's delta
  hashcons is redundant (the parent fallback will find it).

  This is a SPACE optimization, not a correctness requirement.
  All theorems hold with or without pruning.

  Reference: Singher & Itzhaky, "Colored E-Graph" (CAV 2023)

  Key results:
  - `isSubsumedByAncestor`: check if a hashcons entry is redundant
  - `pruneColor`: remove redundant entries from a single color
  - `pruneAllColors`: prune all non-root colors
  - `pruneColor_preserves_lookup`: pruning doesn't change lookup results
-/
import LambdaSat.Core
import LambdaSat.ColorTypes
import LambdaSat.ColoredHashcons
import LambdaSat.ColoredMerge

set_option autoImplicit false

namespace LambdaSat

variable {Op : Type} [BEq Op] [Hashable Op] [NodeOps Op]

/-! ## Subsumption Check -/

/-- Check if an e-node's hashcons entry in color `c` is subsumed by
    an ancestor color. An entry `(node, classId)` is subsumed if
    the parent's hierarchical lookup would return the same classId
    for the same node.

    When subsumed, the delta entry is redundant and can be removed. -/
def isSubsumedByAncestor (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (c : ColorId) (node : ENode Op) (classId : EClassId) : Bool :=
  let parentC := cl.hierarchy.getParent c
  if parentC == c then false  -- root: nothing to subsume against
  else
    let baseLookup := fun (n : ENode Op) => baseGraph.hashcons.get? n
    match ColoredHashconsMap.hierarchicalLookup cl.colorHashcons cl.hierarchy
            baseLookup parentC node with
    | some parentId => parentId == classId
    | none => false

/-! ## Per-Color Pruning -/

/-- Remove all redundant entries from a single color's delta hashcons.
    An entry is removed if the parent's lookup would return the same result. -/
def pruneColor (cl : ColoredLayer Op) (baseGraph : EGraph Op) (c : ColorId) :
    ColoredLayer Op :=
  if c == colorRoot then cl  -- don't prune root
  else
    let ch := ColoredHashconsMap.getHashcons cl.colorHashcons c
    let toRemove := ch.delta.toList.filter fun (node, classId) =>
      isSubsumedByAncestor cl baseGraph c node classId
    let ch' := toRemove.foldl (fun acc (node, _) => acc.erase node) ch
    { cl with colorHashcons :=
        ColoredHashconsMap.setHashcons cl.colorHashcons c ch' }

/-- Prune all non-root colors. -/
def pruneAllColors (cl : ColoredLayer Op) (baseGraph : EGraph Op) :
    ColoredLayer Op :=
  let colorIds := cl.hierarchy.parentOf.toList.map Prod.fst
  colorIds.foldl (fun acc c => pruneColor acc baseGraph c) cl

/-! ## Pruning Statistics -/

/-- Count the number of delta entries across all colors. -/
def totalDeltaEntries (cl : ColoredLayer Op) : Nat :=
  cl.colorHashcons.tables.toList.foldl (fun acc (_, ch) => acc + ch.size) 0

/-- Count entries that would be pruned for a specific color. -/
def countSubsumed (cl : ColoredLayer Op) (baseGraph : EGraph Op) (c : ColorId) : Nat :=
  if c == colorRoot then 0
  else
    let ch := ColoredHashconsMap.getHashcons cl.colorHashcons c
    ch.delta.toList.filter (fun (node, classId) =>
      isSubsumedByAncestor cl baseGraph c node classId) |>.length

/-! ## Properties -/

/-- Pruning the root color is a no-op. -/
theorem pruneColor_root (cl : ColoredLayer Op) (baseGraph : EGraph Op) :
    pruneColor cl baseGraph colorRoot = cl := by
  simp [pruneColor, colorRoot]

/-- Pruning preserves the color hierarchy (only hashcons are modified). -/
theorem pruneColor_preserves_hierarchy (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (c : ColorId) :
    (pruneColor cl baseGraph c).hierarchy = cl.hierarchy := by
  simp [pruneColor]
  split <;> rfl

/-- Pruning preserves the SmallUFs (only hashcons are modified). -/
theorem pruneColor_preserves_ufs (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (c : ColorId) :
    (pruneColor cl baseGraph c).colorUFs = cl.colorUFs := by
  simp [pruneColor]
  split <;> rfl

/-- Summing sizes via foldl distributes: foldl f init l = init + foldl f 0 l. -/
private theorem foldl_add_size_init {α : Type} {β : Type}
    (f_size : β → Nat) (init : Nat) (l : List (α × β)) :
    l.foldl (fun acc x => acc + f_size x.2) init =
    init + l.foldl (fun acc x => acc + f_size x.2) 0 := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih (init + f_size hd.2), ih (0 + f_size hd.2)]
    omega

/-- foldl (+size) over a cons = head.size + foldl (+size) over tail. -/
private theorem foldl_add_size_cons {α : Type} {β : Type}
    (f_size : β → Nat) (hd : α × β) (tl : List (α × β)) :
    (hd :: tl).foldl (fun acc x => acc + f_size x.2) 0 =
    f_size hd.2 + tl.foldl (fun acc x => acc + f_size x.2) 0 := by
  simp only [List.foldl]
  rw [foldl_add_size_init f_size (0 + f_size hd.2) tl]
  omega

/-- foldl (+size) over a sublist (filter) is ≤ foldl over the original list. -/
private theorem foldl_filter_le {α : Type} {β : Type}
    (f_size : β → Nat) (p : α × β → Bool) (l : List (α × β)) :
    (l.filter p).foldl (fun acc x => acc + f_size x.2) 0 ≤
    l.foldl (fun acc x => acc + f_size x.2) 0 := by
  induction l with
  | nil => simp [List.foldl, List.filter]
  | cons hd tl ih =>
    simp only [List.filter]
    split
    · rw [foldl_add_size_cons, foldl_add_size_cons]; omega
    · rw [foldl_add_size_cons]; omega

/-- If `(k, v) ∈ l`, then `fold_sum l ≥ f_size v + fold_sum (filter (k ≠ ·.1) l)`.
    No distinct-keys hypothesis needed — just list membership. -/
private theorem foldl_mem_ge_filter {α : Type} [BEq α] [LawfulBEq α] {β : Type}
    (f_size : β → Nat) (k : α) (v : β) (l : List (α × β))
    (hmem : (k, v) ∈ l) :
    l.foldl (fun acc x => acc + f_size x.2) 0 ≥
    f_size v + (l.filter (fun x => decide (¬(k == x.1) = true))).foldl
      (fun acc x => acc + f_size x.2) 0 := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [foldl_add_size_cons]
    simp only [List.filter]
    split
    · rename_i hneq; rw [foldl_add_size_cons]
      rcases List.mem_cons.mp hmem with h | h
      · have := (Prod.ext_iff.mp h).1; subst this; simp at hneq
      · have := ih h; omega
    · have hfl := foldl_filter_le f_size (fun x => decide (¬(k == x.1) = true)) tl
      rcases List.mem_cons.mp hmem with h | h
      · have := (Prod.ext_iff.mp h).2; subst this; omega
      · have := ih h; omega

/-- For distinct-keyed list l with l ⊆ l' (as pairs),
    fold_sum(l) ≤ fold_sum(l'). -/
private theorem foldl_subset_distinct_le {α : Type} [BEq α] [LawfulBEq α] {β : Type}
    (f_size : β → Nat) (l l' : List (α × β))
    (hsub : ∀ p, p ∈ l → p ∈ l')
    (hdistinct : List.Pairwise (fun a b => (a == b) = false) (l.map Prod.fst)) :
    l.foldl (fun acc x => acc + f_size x.2) 0 ≤
    l'.foldl (fun acc x => acc + f_size x.2) 0 := by
  induction l generalizing l' with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    rw [foldl_add_size_cons]
    simp only [List.map, List.pairwise_cons] at hdistinct
    obtain ⟨hall, htl_distinct⟩ := hdistinct
    have hhd_in_l' := hsub hd (List.mem_cons.mpr (Or.inl rfl))
    have hge := foldl_mem_ge_filter f_size hd.1 hd.2 l' hhd_in_l'
    have htl_sub : ∀ p, p ∈ tl →
        p ∈ l'.filter (fun x => decide (¬(hd.1 == x.1) = true)) := by
      intro ⟨a, b⟩ hmem_tl
      rw [List.mem_filter]
      refine ⟨hsub _ (List.mem_cons.mpr (Or.inr hmem_tl)), ?_⟩
      simp only [decide_eq_true_eq]
      intro heq
      have : a ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(a, b), hmem_tl, rfl⟩
      have := hall a this; rw [heq] at *; simp at *
    have ih_res := ih _ htl_sub htl_distinct
    omega

/-- For distinct-keyed lists, fold decomposes by key:
    fold_sum l = f_size(v) + fold_sum(filter (!=k) l) when (k,v) ∈ l. -/
private theorem foldl_distinct_decompose {α : Type} [BEq α] [LawfulBEq α] {β : Type}
    (f_size : β → Nat) (k : α) (v : β) (l : List (α × β))
    (hmem : (k, v) ∈ l)
    (hdistinct : List.Pairwise (fun a b => (a == b) = false) (l.map Prod.fst)) :
    l.foldl (fun acc x => acc + f_size x.2) 0 =
    f_size v + (l.filter (fun x => decide (¬(k == x.1) = true))).foldl
      (fun acc x => acc + f_size x.2) 0 := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [foldl_add_size_cons]
    simp only [List.filter, List.map, List.pairwise_cons] at hdistinct ⊢
    obtain ⟨hall, htl_distinct⟩ := hdistinct
    split
    · -- k ≠ hd.fst
      rename_i hneq
      rw [foldl_add_size_cons]
      rcases List.mem_cons.mp hmem with h | h
      · have := (Prod.ext_iff.mp h).1; subst this; simp at hneq
      · rw [ih h htl_distinct]; omega
    · -- k == hd.fst
      rename_i hkeq_raw
      have hkeq : (k == hd.fst) = true := by
        simp only [Bool.not_eq_true, decide_eq_false_iff_not, Bool.not_eq_false] at hkeq_raw
        exact hkeq_raw
      have hk_eq : k = hd.fst := beq_iff_eq.mp hkeq
      rcases List.mem_cons.mp hmem with h | h
      · -- (k, v) = hd
        have hv_eq : v = hd.snd := (Prod.ext_iff.mp h).2; subst hv_eq
        suffices hfilt : tl.filter (fun x => decide (¬(k == x.1) = true)) = tl by rw [hfilt]
        rw [List.filter_eq_self]
        intro ⟨a, b⟩ hx
        simp only [decide_eq_true_eq]
        intro heq
        have hka : k = a := beq_iff_eq.mp heq
        have ha_mem : a ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(a, b), hx, rfl⟩
        have := hall a ha_mem; subst hk_eq; subst hka; simp at this
      · -- (k, v) ∈ tl but k == hd.fst: contradicts distinct keys
        have hk_mem : k ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k, v), h, rfl⟩
        have := hall k hk_mem; subst hk_eq; simp at this

/-- Pairwise is preserved by filter. -/
private theorem pairwise_filter_map_fst {α : Type} [BEq α] {β : Type}
    (p : α × β → Bool) (l : List (α × β))
    (hdistinct : List.Pairwise (fun a b => (a == b) = false) (l.map Prod.fst)) :
    List.Pairwise (fun a b => (a == b) = false) ((l.filter p).map Prod.fst) := by
  induction l with
  | nil => simp [List.filter]
  | cons hd tl ih =>
    simp only [List.filter]
    split
    · simp only [List.map, List.pairwise_cons] at hdistinct ⊢
      obtain ⟨hall, htl⟩ := hdistinct
      refine ⟨fun a ha => ?_, ih htl⟩
      have ha_in_filter := List.mem_map.mp ha
      obtain ⟨⟨a', b'⟩, hmf, rfl⟩ := ha_in_filter
      have hmf' : (a', b') ∈ tl := (List.mem_filter.mp hmf).1
      exact hall a' (List.mem_map.mpr ⟨(a', b'), hmf', rfl⟩)
    · simp only [List.map, List.pairwise_cons] at hdistinct
      exact ih hdistinct.2

/-- Erasing entries from a ColoredHashcons can only decrease its size. -/
private theorem foldl_erase_size_le [LawfulBEq Op] [LawfulHashable Op]
    (entries : List (ENode Op × EClassId)) (ch : ColoredHashcons Op) :
    (entries.foldl (fun acc (node, _) => acc.erase node) ch).size ≤ ch.size := by
  induction entries generalizing ch with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    calc (tl.foldl (fun acc (node, _) => acc.erase node) (ch.erase hd.1)).size
        ≤ (ch.erase hd.1).size := ih (ch.erase hd.1)
      _ ≤ ch.size := by
          simp only [ColoredHashcons.size, ColoredHashcons.erase]
          rw [Std.HashMap.size_erase]
          split <;> omega

/-- HashMap distinct keys in the form used by our list-level lemmas. -/
private theorem hashmap_distinct_keys_toList {α : Type} {β : Type}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) :
    List.Pairwise (fun a b => (a == b) = false) (m.toList.map Prod.fst) := by
  have h := Std.HashMap.distinct_keys (m := m)
  rw [show m.keys = m.toList.map Prod.fst from by simp [Std.HashMap.keys]] at h
  exact h.imp (fun hab => by simp [hab])

/-- After HashMap.insert, every non-key entry in the new toList was already in the old toList. -/
private theorem mem_toList_insert_of_ne {α : Type} {β : Type}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (v : β) (k' : α) (v' : β)
    (hne : (k == k') = false) (hmem : (k', v') ∈ (m.insert k v).toList) :
    (k', v') ∈ m.toList := by
  rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hmem ⊢
  rw [Std.HashMap.getElem?_insert] at hmem
  simp [hne] at hmem
  exact hmem

/-- Inserting a key with a smaller-or-equal-valued entry cannot increase the foldl sum,
    provided the key was already present and we replace with a smaller value.
    More precisely: foldl_sum (m.insert k v) ≤ foldl_sum m
    when v.size ≤ (getHashcons k).size, where getHashcons defaults to empty. -/
private theorem foldl_sum_insert_le {α : Type} {β : Type}
    [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    (m : Std.HashMap α β) (k : α) (v : β) (f_size : β → Nat)
    (hle : f_size v ≤ (match m[k]? with | some x => f_size x | none => 0)) :
    (m.insert k v).toList.foldl (fun acc x => acc + f_size x.2) 0 ≤
    m.toList.foldl (fun acc x => acc + f_size x.2) 0 := by
  -- (k, v) ∈ (m.insert k v).toList
  have hmem_kv : (k, v) ∈ (m.insert k v).toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some,
        Std.HashMap.getElem?_insert_self]
  -- Decompose: sum(insert) = f_size(v) + sum(filter(≠k) insert)
  have hdist_insert := hashmap_distinct_keys_toList (m.insert k v)
  have hdecomp_insert := foldl_distinct_decompose f_size k v
    (m.insert k v).toList hmem_kv hdist_insert
  -- filter(≠k) of insert.toList ⊆ filter(≠k) of m.toList
  have hfilter_sub : ∀ p, p ∈ (m.insert k v).toList.filter
      (fun x => decide (¬(k == x.1) = true)) →
      p ∈ m.toList.filter (fun x => decide (¬(k == x.1) = true)) := by
    intro ⟨k', v'⟩ hmf
    rw [List.mem_filter] at hmf ⊢
    obtain ⟨hmem, hne_dec⟩ := hmf
    simp only [decide_eq_true_eq, Bool.not_eq_true] at hne_dec
    exact ⟨mem_toList_insert_of_ne m k v k' v' hne_dec hmem, by simp [hne_dec]⟩
  -- filter(≠k) has distinct keys
  have hdist_filter := pairwise_filter_map_fst
    (fun x => decide (¬(k == x.1) = true)) (m.insert k v).toList hdist_insert
  -- sum(filter(≠k) insert) ≤ sum(filter(≠k) m)
  have hdist_filter_m := pairwise_filter_map_fst
    (fun x => decide (¬(k == x.1) = true)) m.toList (hashmap_distinct_keys_toList m)
  have hfilt_le := foldl_subset_distinct_le f_size
    ((m.insert k v).toList.filter (fun x => decide (¬(k == x.1) = true)))
    (m.toList.filter (fun x => decide (¬(k == x.1) = true)))
    hfilter_sub hdist_filter
  -- Case split on whether k ∈ m
  by_cases hk : k ∈ m
  · -- k ∈ m: decompose original sum too
    have hget := Std.HashMap.getElem?_eq_some_getElem (m := m) hk
    have hmem_k_orig : (k, m[k]'hk) ∈ m.toList := by
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]; exact hget
    have hdist_m := hashmap_distinct_keys_toList m
    have hdecomp_m := foldl_distinct_decompose f_size k (m[k]'hk)
      m.toList hmem_k_orig hdist_m
    -- Simplify the match in hle: match some m[k] with ... = f_size m[k]
    rw [hget] at hle; simp only at hle
    rw [hdecomp_insert, hdecomp_m]; omega
  · -- k ∉ m: f_size v ≤ 0, so f_size v = 0
    have hget_none := Std.HashMap.getElem?_eq_none hk
    rw [hget_none] at hle; simp only at hle
    -- f_size v = 0
    have hv_zero : f_size v = 0 := Nat.le_zero.mp hle
    have hfilt_m_le := foldl_filter_le f_size
      (fun x => decide (¬(k == x.1) = true)) m.toList
    rw [hdecomp_insert, hv_zero]; omega

theorem pruneColor_entries_le [LawfulBEq Op] [LawfulHashable Op]
    (cl : ColoredLayer Op) (baseGraph : EGraph Op)
    (c : ColorId) :
    totalDeltaEntries (pruneColor cl baseGraph c) ≤ totalDeltaEntries cl := by
  simp only [pruneColor]
  split
  · -- Root case: no-op
    exact Nat.le_refl _
  · -- Non-root case: pruning can only decrease delta entries
    rename_i hNotRoot
    simp only [totalDeltaEntries, ColoredHashconsMap.setHashcons]
    apply foldl_sum_insert_le cl.colorHashcons.tables c _ ColoredHashcons.size
    -- Need: ch'.size ≤ match tables[c]? with | some x => x.size | none => 0
    -- Connect getHashcons to tables[c]?
    -- getHashcons m c = match m.tables.get? c with | some ch => ch | none => empty
    simp only [ColoredHashconsMap.getHashcons, Std.HashMap.get?_eq_getElem?]
    split
    · -- tables[c]? = some ch_orig: ch = ch_orig, so ch'.size ≤ ch.size = ch_orig.size
      rename_i ch_orig heq
      rw [heq]; simp only
      exact foldl_erase_size_le _ _
    · -- tables[c]? = none: ch = empty, ch' ≤ empty.size = 0
      rename_i heq
      rw [heq]; simp only
      exact foldl_erase_size_le _ _

/-! ## Smoke tests -/

private inductive CPTestOp where
  | lit : Nat → CPTestOp
  | add : EClassId → EClassId → CPTestOp
  deriving BEq, Hashable

instance : NodeOps CPTestOp where
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
  let cl : ColoredLayer CPTestOp := ColoredLayer.empty
  let entries := totalDeltaEntries cl
  s!"Empty colored layer: totalDeltaEntries = {entries}"

#eval
  let cl : ColoredLayer CPTestOp := ColoredLayer.empty
  let pruned := pruneAllColors cl (EGraph.empty : EGraph CPTestOp)
  let entries := totalDeltaEntries pruned
  s!"After pruning empty: totalDeltaEntries = {entries}"

end LambdaSat
