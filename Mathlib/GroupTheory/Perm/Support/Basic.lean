/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.End

import Mathlib.Data.Set.Insert

/-!
# Support of a permutation: basic definitions

This file contains material about the points moved by a permutation that does not need any
finiteness assumptions.

## Main definitions

In the following, `f : Equiv.Perm α`.

* `Equiv.Perm.support` is the set `{x | f x ≠ x}`, the set of all elements that are not fixed
by the permutation.

See `Mathlib/GroupTheory/Perm/Support/Finset.lean` for `Equiv.Perm.supportFinset`, the `Finset`
of points moved by a permutation of a `Fintype`.
-/

public section

namespace Equiv.Perm

variable {α : Type*}

/-- The `Set` of nonfixed points of a permutation. -/
def support (f : Perm α) : Set α := {x | f x ≠ x}

section Support

variable {f g : Perm α}

@[grind =, simp] theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := Set.mem_ofPred

theorem support_def : f.support = {x | f x ≠ x} := by grind

instance [DecidableEq α] : DecidablePred (· ∈ f.support) := fun _ =>
  decidable_of_decidable_of_iff mem_support.symm

theorem notMem_support {x : α} : x ∉ f.support ↔ f x = x := mem_support.not_left

@[simp] theorem support_eq_empty_iff : f.support = ∅ ↔ f = 1 := by
  simp [Set.ext_iff, Equiv.ext_iff]

@[simp] theorem support_one : (1 : Perm α).support = ∅ := by simp

@[simp]
theorem support_refl : support (Equiv.refl α) = ∅ := by simp [pull_end]

@[simp]
theorem support_inv (f : Perm α) : f⁻¹.support = f.support := by
  grind [f.inv_eq_iff_eq]

@[simp] theorem support_symm : support f.symm = f.support := by grind

@[deprecated (since := "2026-11-17")] alias set_support_symm_eq := support_symm

theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by simp

@[deprecated (since := "2026-11-17")] alias set_support_apply_mem := apply_mem_support

theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by simp

theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by simp

theorem support_eq_pair_iff {x y} : f.support = {x, y} ↔ x ≠ y ∧ f x = y ∧ f y = x ∧
    (∀ {z}, z ≠ x → z ≠ y → f z = z) := Set.ext_iff.trans <|
    ⟨(by have := · ∘' f; grind [f.injective]), by grind⟩

theorem support_ne_singleton {x} : f.support ≠ {x} := Set.pair_eq_singleton x ▸ by
  simp only [ne_eq, support_eq_pair_iff, and_self_left,
    false_and, not_true_eq_false, not_false_eq_true]

/-- If `g` and `c` commute, then `g` stabilizes the support of `c`. -/
theorem mem_support_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.support ↔ x ∈ c.support := by
  simp only [mem_support, ne_eq, hgc.symm.apply_apply, g.apply_eq_iff_eq]

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀ x ∈ g.support, f x = g x) : f = g := by
  grind

theorem support_swap_eq_pair_iff [DecidableEq α] {x y : α} :
    (swap x y).support = {x, y} ↔ x ≠ y := support_eq_pair_iff.trans <| and_iff_left_of_imp <|
  fun _ => ⟨swap_apply_left x y, swap_apply_right x y, swap_apply_of_ne_of_ne⟩

@[simp]
theorem support_swap_of_ne [DecidableEq α] {x y : α} (h : x ≠ y) : (swap x y).support = {x, y} :=
  support_swap_eq_pair_iff.mpr h

theorem support_swap [DecidableEq α] {x y : α} : (swap x y).support =
    if x = y then ∅ else {x, y} := if h : x = y then
    Eq.trans (h ▸ swap_self x ▸ support_refl) ((ite_eq_left h).symm) else
    Eq.trans (support_swap_of_ne h) (ite_eq_right h).symm

theorem support_pow_subset (n : ℕ) : (f ^ n).support ⊆ f.support := by
  grind [pow_apply_eq_self_of_apply_eq_self]

theorem support_zpow_subset (n : ℤ) : (f ^ n).support ⊆ f.support := by
  grind [zpow_apply_eq_self_of_apply_eq_self]

@[deprecated (since := "2026-11-17")] alias set_support_zpow_subset := support_zpow_subset

theorem support_mul_subset (f g : Perm α) : (f * g).support ⊆ f.support ∪ g.support := by
  grind [mul_apply]

@[deprecated (since := "2026-11-17")] alias set_support_mul_subset := support_mul_subset

@[simp]
theorem support_conj : (f * g * f⁻¹).support = f '' g.support := by
  grind [mul_apply, Set.mem_image_perm, f.eq_inv_iff_eq]

theorem support_permCongr : (f.permCongr g).support = f '' g.support := by simp

theorem _root_.MulAut.support_conj_apply : (MulAut.conj f g).support = f '' g.support := by simp

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.support) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.mem_cons, true_or]
    grind

theorem isInvariant_of_support_subset {c : Perm α} {s : Set α} (hcs : c.support ⊆ s)
    (x : α) : c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.support
  · simp only [hcs hx', hcs (apply_mem_support.mpr hx')]
  · rw [notMem_support.mp hx']

lemma ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Set α} [DecidablePred (· ∈ s)]
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.support ⊆ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_support, ← h a, ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_support_subset hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha, eq_comm, ← notMem_support]
      exact Set.notMem_subset hc ha

theorem support_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).support = Subtype.val '' u.support := by
  ext x
  simp only [mem_support, ne_eq, Set.mem_image,
    Subtype.exists, exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

theorem mem_support_ofSubtype {p : α → Prop} [DecidablePred p] (x : α)
    (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).support ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.support := by
  simp [support_ofSubtype]

theorem pow_eq_on_of_mem_support (h : ∀ x ∈ f.support ∩ g.support, f x = g x)
    (k : ℕ) : ∀ x ∈ f.support ∩ g.support, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [Set.mem_inter_iff, apply_mem_support, ← h _ hx, apply_mem_support, ← Set.mem_inter_iff]

theorem support_prod_subset (l : List (Perm α)) : l.prod.support ⊆
    (l.map support).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (support_mul_subset hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

theorem support_swap_mul_swap [DecidableEq α] {x y z : α} (h : List.Nodup [x, y, z]) :
    support (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert support_mul_subset (swap x y) (swap y z) using 1
    rw [support_swap_of_ne h.left.left, support_swap_of_ne h.right.left]
    grind
  · intro
    simp only [Set.mem_insert_iff]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

end Support

end Equiv.Perm
