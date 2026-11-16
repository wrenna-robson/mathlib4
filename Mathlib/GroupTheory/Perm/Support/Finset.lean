/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Fintype.Card

import Mathlib.Algebra.Group.Commute.Basic

/-!
# support of a permutation

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `Disjoint` iff their `support` are disjoint.
* `Equiv.Perm.IsSwap`: `f = swap x y` for `x ≠ y`.
* `Equiv.Perm.supportFinset`: the elements `x : α` that are not fixed by `f`.

Assume `α` is a Fintype:
* `Equiv.Perm.fixed_point_card_lt_of_ne_one f` says that `f` has
  strictly less than `Fintype.card α - 1` fixed points, unless `f = 1`.
  (Equivalently, `f.supportFinset` has at least 2 elements.)
-/

@[expose] public section


open Equiv Finset Function

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x

variable {f g h : Perm α}

@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by simp only [Disjoint, or_comm, imp_self]

instance Disjoint.stdSymm : Std.Symm (α := Perm α) Disjoint where
  symm _ _ := Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩

theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equiv.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim (fun hg => by simp [mul_apply, hf, hg]) fun hg => by
          simp [mul_apply, hf, g.injective hg])
      fun hg =>
      (h (f x)).elim (fun hf => by simp [mul_apply, f.injective hf, hg]) fun hf => by
        simp [mul_apply, hf, hg]

@[simp]
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl

@[simp]
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl

theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl

@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  rcases h x with hx | hx <;> simp [hx]

theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x

theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm

@[simp]
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine ⟨fun h => ?_, Disjoint.inv_left⟩
  convert! h.inv_left

@[simp]
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]

theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x ↦ by
  cases H1 x <;> cases H2 x <;> simp [*]

theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

@[simp]
theorem disjoint_conj (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) ↔ Disjoint f g :=
  (h⁻¹).forall_congr fun {_} ↦ by simp only [mul_apply, eq_inv_iff_eq]

theorem Disjoint.conj (H : Disjoint f g) (h : Perm α) : Disjoint (h * f * h⁻¹) (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, Disjoint f g) :
    Disjoint f l.prod := by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem disjoint_noncommProd_right {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (hg : ∀ i ∈ s, g.Disjoint (k i)) :
    Disjoint g (s.noncommProd k (hs)) :=
  noncommProd_induction s k hs g.Disjoint (fun _ _ ↦ Disjoint.mul_right) (disjoint_one_right g) hg

open scoped List in
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) :
    l₁.prod = l₂.prod :=
  hp.prod_eq' <| hl.imp Disjoint.commute

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Disjoint) : l.Nodup := by
  grind [List.Pairwise.imp_of_mem, disjoint_refl_iff]

theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by rw [pow_succ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self hfx n]

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | Int.negSucc n => by rw [zpow_negSucc, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self hffx n).elim
      (fun h => Or.inr (by rw [pow_succ', mul_apply, h]))
      fun h => Or.inl (by rw [pow_succ', mul_apply, h, hffx])

theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) :
    ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | Int.negSucc n => by
    rw [zpow_negSucc, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succ', eq_comm,
      inv_eq_iff_eq, ← mul_apply, ← pow_succ, @eq_comm _ x, or_comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _

theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} :
    (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine ⟨fun h => ?_, fun h => by rw [mul_apply, h.2, h.1]⟩
  rcases hστ a with hσ | hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
  · exact ⟨congr(σ $hτ).symm.trans h, hτ⟩

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [Perm.ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and]

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) :
    Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m)
    (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) :
    Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

end Disjoint

section IsSwap

variable [DecidableEq α]

/-- `f.IsSwap` indicates that the permutation `f` is a transposition of two elements. -/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y

@[simp]
theorem ofSubtype_swap_eq {p : α → Prop} [DecidablePred p] (x y : Subtype p) :
    ofSubtype (Equiv.swap x y) = Equiv.swap ↑x ↑y := by
  grind [ofSubtype_apply_of_mem, ofSubtype_apply_of_not_mem]

theorem IsSwap.of_subtype_isSwap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)}
    (h : f.IsSwap) : (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [Ne, Subtype.ext_iff] at hxy
    exact hxy.1, by
    rw [hxy.2, ofSubtype_swap_eq]⟩

theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) :
    f y ≠ y ∧ y ≠ x := by
  simp only [swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

end IsSwap

section supportFinset

section Set

variable (p q : Perm α)

lemma set_support_symm_eq : {x | p.symm x ≠ x} = {x | p x ≠ x} := by
  ext; simp [eq_symm_apply, eq_comm]

theorem set_support_apply_mem {p : Perm α} {a : α} :
    p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by simp

theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx

theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  simp only [coe_mul]
  grind

end Set

@[simp]
theorem apply_pow_apply_eq_iff (f : Perm α) (n : ℕ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_pow f, mul_apply, apply_eq_iff_eq]

@[simp]
theorem apply_zpow_apply_eq_iff (f : Perm α) (n : ℤ) {x : α} :
    f ((f ^ n) x) = (f ^ n) x ↔ f x = x := by
  rw [← mul_apply, Commute.self_zpow f, mul_apply, apply_eq_iff_eq]

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `Finset` of nonfixed points of a permutation. -/
def supportFinset (f : Perm α) : Finset α := {x | f x ≠ x}

@[deprecated (since := "2026-11-16")] alias support := supportFinset

@[simp]
theorem mem_supportFinset {x : α} : x ∈ f.supportFinset ↔ f x ≠ x := by
  rw [supportFinset, mem_filter, and_iff_right (mem_univ x)]

@[deprecated (since := "2026-11-16")] alias mem_support := mem_supportFinset

theorem notMem_supportFinset {x : α} : x ∉ f.supportFinset ↔ f x = x := by simp

@[deprecated (since := "2026-11-16")] alias notMem_support := notMem_supportFinset

theorem coe_supportFinset_eq_set_support (f : Perm α) : (f.supportFinset : Set α) =
    { x | f x ≠ x } := by
  ext
  simp

@[deprecated (since := "2026-11-16")] alias coe_support_eq_set_support :=
    coe_supportFinset_eq_set_support

@[simp]
theorem supportFinset_eq_empty_iff {σ : Perm α} : σ.supportFinset = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_supportFinset, Finset.notMem_empty, iff_false, not_not,
    Equiv.Perm.ext_iff, one_apply]

@[deprecated (since := "2026-11-16")] alias support_eq_empty_iff := supportFinset_eq_empty_iff

@[simp]
theorem supportFinset_one : (1 : Perm α).supportFinset = ∅ := by rw [supportFinset_eq_empty_iff]

@[deprecated (since := "2026-11-16")] alias support_one := supportFinset_one

@[simp]
theorem supportFinset_refl : supportFinset (Equiv.refl α) = ∅ :=
  supportFinset_one

@[deprecated (since := "2026-11-16")] alias support_refl := supportFinset_refl

theorem supportFinset_congr (h : f.supportFinset ⊆ g.supportFinset)
    (h' : ∀ x ∈ g.supportFinset, f x = g x) : f = g := by
  grind [notMem_supportFinset]

@[deprecated (since := "2026-11-16")] alias support_congr := supportFinset_congr

/-- If g and c commute, then g stabilizes the support of c -/
theorem mem_supportFinset_iff_of_commute {g c : Perm α} (hgc : Commute g c) (x : α) :
    g x ∈ c.supportFinset ↔ x ∈ c.supportFinset := by
  simp only [mem_supportFinset, not_iff_not, ← mul_apply]
  rw [← hgc, mul_apply, Equiv.apply_eq_iff_eq]

@[deprecated (since := "2026-11-16")] alias mem_support_iff_of_commute :=
    mem_supportFinset_iff_of_commute

theorem supportFinset_mul_le (f g : Perm α) :
    (f * g).supportFinset ≤ f.supportFinset ∪ g.supportFinset := fun x => by
  rw [mem_union, mem_supportFinset, mem_supportFinset, mem_supportFinset, mul_apply, ← not_and_or,
      not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]

@[deprecated (since := "2026-11-16")] alias support_mul_le := supportFinset_mul_le

theorem exists_mem_supportFinset_of_mem_supportFinset_prod {l : List (Perm α)} {x : α}
    (hx : x ∈ l.prod.supportFinset) : ∃ f : Perm α, f ∈ l ∧ x ∈ f.supportFinset := by
  contrapose! hx
  simp_rw [mem_supportFinset, not_not] at hx ⊢
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.prod_cons, mul_apply, ih, hx]
    · simp only [List.mem_cons, true_or]
    grind

@[deprecated (since := "2026-11-16")] alias exists_mem_support_of_mem_support_prod :=
    exists_mem_supportFinset_of_mem_supportFinset_prod

theorem supportFinset_pow_le (σ : Perm α) (n : ℕ) :
    (σ ^ n).supportFinset ≤ σ.supportFinset := fun _ h1 =>
  mem_supportFinset.mpr fun h2 => mem_supportFinset.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[deprecated (since := "2026-11-16")] alias support_pow_le := supportFinset_pow_le

@[simp]
theorem supportFinset_inv (σ : Perm α) : supportFinset σ⁻¹ = σ.supportFinset := by
  simp_rw [Finset.ext_iff, mem_supportFinset, not_iff_not, inv_eq_iff_eq.trans eq_comm,
      imp_true_iff]

@[deprecated (since := "2026-11-16")] alias support_inv := supportFinset_inv

theorem apply_mem_supportFinset {x : α} : f x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  rw [mem_supportFinset, mem_supportFinset, Ne, Ne, apply_eq_iff_eq]

@[deprecated (since := "2026-11-16")] alias apply_mem_support := apply_mem_supportFinset

/-- The support of a permutation is invariant -/
theorem isInvariant_of_supportFinset_le {c : Perm α} {s : Finset α} (hcs : c.supportFinset ≤ s)
    (x : α) :
    c x ∈ s ↔ x ∈ s := by
  by_cases hx' : x ∈ c.supportFinset
  · simp only [hcs hx', hcs (apply_mem_supportFinset.mpr hx')]
  · rw [notMem_supportFinset.mp hx']

@[deprecated (since := "2026-11-16")] alias isInvariant_of_support_le :=
    isInvariant_of_supportFinset_le

/-- A permutation c is the extension of a restriction of g to s
  iff its support is contained in s and its restriction is that of g -/
lemma ofSubtype_eq_iff {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) :
    ofSubtype (g.subtypePerm hg) = c ↔
      c.supportFinset ≤ s ∧
      ∀ (hc' : ∀ x, c x ∈ s ↔ x ∈ s), c.subtypePerm hc' = g.subtypePerm hg := by
  simp only [Equiv.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  constructor
  · intro h
    constructor
    · intro a ha
      by_contra ha'
      rw [mem_supportFinset, ← h a, ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha'] at ha
      exact ha rfl
    · intro _ a ha
      rw [← h a, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
  · rintro ⟨hc, h⟩ a
    specialize h (isInvariant_of_supportFinset_le hc)
    by_cases ha : a ∈ s
    · rw [h a ha, ofSubtype_apply_of_mem (p := (· ∈ s)) _ ha, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (p := (· ∈ s)) _ ha, eq_comm, ← notMem_supportFinset]
      exact Finset.notMem_mono hc ha

theorem supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (u : Perm (Subtype p)) :
    (ofSubtype u).supportFinset = u.supportFinset.map (Function.Embedding.subtype p) := by
  ext x
  simp only [mem_supportFinset, ne_eq, Finset.mem_map, Function.Embedding.coe_subtype,
      Subtype.exists,
    exists_and_right, exists_eq_right, not_iff_comm, not_exists, not_not]
  by_cases hx : p x
  · simp only [forall_prop_of_true hx, ofSubtype_apply_of_mem u hx, ← Subtype.coe_inj]
  · simp only [forall_prop_of_false hx, ofSubtype_apply_of_not_mem u hx]

@[deprecated (since := "2026-11-16")] alias support_ofSubtype := supportFinset_ofSubtype

theorem mem_supportFinset_ofSubtype {p : α → Prop} [DecidablePred p] (x : α)
    (u : Perm (Subtype p)) :
    x ∈ (ofSubtype u).supportFinset ↔ ∃ (hx : p x), ⟨x, hx⟩ ∈ u.supportFinset := by
  simp [supportFinset_ofSubtype]

@[deprecated (since := "2026-11-16")] alias mem_support_ofSubtype := mem_supportFinset_ofSubtype

theorem mem_supportFinset_of_mem_noncommProd_supportFinset {α β : Type*} [DecidableEq β] [Fintype β]
    {s : Finset α} {f : α → Perm β}
    {comm : (s : Set α).Pairwise (Commute on f)} {x : β}
        (hx : x ∈ (s.noncommProd f comm).supportFinset) :
    ∃ a ∈ s, x ∈ (f a).supportFinset := by
  contrapose! hx
  classical
  revert hx comm s
  apply Finset.induction
  · simp
  · intro a s ha ih comm hs
    rw [Finset.noncommProd_insert_of_notMem s a f comm ha]
    apply mt (Finset.mem_of_subset (supportFinset_mul_le _ _))
    rw [Finset.notMem_union]
    exact ⟨hs a (s.mem_insert_self a), ih (fun a ha ↦ hs a (Finset.mem_insert_of_mem ha))⟩

@[deprecated (since := "2026-11-16")] alias mem_support_of_mem_noncommProd_support :=
    mem_supportFinset_of_mem_noncommProd_supportFinset

theorem pow_apply_mem_supportFinset {n : ℕ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  simp only [mem_supportFinset, ne_eq, apply_pow_apply_eq_iff]

@[deprecated (since := "2026-11-16")] alias pow_apply_mem_support := pow_apply_mem_supportFinset

theorem zpow_apply_mem_supportFinset {n : ℤ} {x : α} :
    (f ^ n) x ∈ f.supportFinset ↔ x ∈ f.supportFinset := by
  simp only [mem_supportFinset, ne_eq, apply_zpow_apply_eq_iff]

@[deprecated (since := "2026-11-16")] alias zpow_apply_mem_support := zpow_apply_mem_supportFinset

theorem pow_eq_on_of_mem_supportFinset (h : ∀ x ∈ f.supportFinset ∩ g.supportFinset, f x = g x)
    (k : ℕ) :
    ∀ x ∈ f.supportFinset ∩ g.supportFinset, (f ^ k) x = (g ^ k) x := by
  induction k with
  | zero => simp
  | succ k hk =>
    intro x hx
    rw [pow_succ, mul_apply, pow_succ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_supportFinset, ← h _ hx, apply_mem_supportFinset, ← mem_inter]

@[deprecated (since := "2026-11-16")] alias pow_eq_on_of_mem_support :=
    pow_eq_on_of_mem_supportFinset

theorem disjoint_iff_disjoint_supportFinset : Disjoint f g ↔
    _root_.Disjoint f.supportFinset g.supportFinset := by
  simp [disjoint_iff_eq_or_eq, disjoint_iff, disjoint_iff, Finset.ext_iff,
    imp_iff_not_or]

@[deprecated (since := "2026-11-16")] alias disjoint_iff_disjoint_support :=
    disjoint_iff_disjoint_supportFinset

theorem Disjoint.disjoint_supportFinset
    (h : Disjoint f g) : _root_.Disjoint f.supportFinset g.supportFinset :=
  disjoint_iff_disjoint_supportFinset.1 h

@[deprecated (since := "2026-11-16")] alias Disjoint.disjoint_support :=
    Disjoint.disjoint_supportFinset

theorem Disjoint.supportFinset_mul (h : Disjoint f g) :
    (f * g).supportFinset = f.supportFinset ∪ g.supportFinset := by
  refine le_antisymm (supportFinset_mul_le _ _) fun a => ?_
  rw [mem_union, mem_supportFinset, mem_supportFinset, mem_supportFinset, mul_apply, ← not_and_or,
      not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨congr(f $hg).symm.trans h, hg⟩

@[deprecated (since := "2026-11-16")] alias Disjoint.support_mul := Disjoint.supportFinset_mul

theorem supportFinset_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.prod.supportFinset = (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [this.supportFinset_mul, hl h.right]

@[deprecated (since := "2026-11-16")] alias support_prod_of_pairwise_disjoint :=
    supportFinset_prod_of_pairwise_disjoint

theorem supportFinset_noncommProd {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Disjoint (k i) (k j)) :
    (s.noncommProd k (hs.imp (fun _ _ ↦ Perm.Disjoint.commute))).supportFinset =
      s.biUnion fun i ↦ (k i).supportFinset := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hrec =>
    have hs' : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j) :=
      hs.mono (by simp only [Finset.coe_insert, Set.subset_insert])
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hi, Finset.biUnion_insert]
    rw [Equiv.Perm.Disjoint.supportFinset_mul, hrec hs']
    apply disjoint_noncommProd_right
    intro j hj
    apply hs _ _ (ne_of_mem_of_not_mem hj hi).symm <;>
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, hj, or_true, true_or]

@[deprecated (since := "2026-11-16")] alias support_noncommProd := supportFinset_noncommProd

theorem supportFinset_prod_le (l : List (Perm α)) : l.prod.supportFinset ≤
    (l.map supportFinset).foldr (· ∪ ·) ⊥ := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine (supportFinset_mul_le hd tl.prod).trans ?_
    exact sup_le_sup le_rfl hl

@[deprecated (since := "2026-11-16")] alias support_prod_le := supportFinset_prod_le

theorem supportFinset_zpow_le (σ : Perm α) (n : ℤ) :
    (σ ^ n).supportFinset ≤ σ.supportFinset := fun _ h1 =>
  mem_supportFinset.mpr fun h2 => mem_supportFinset.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

@[deprecated (since := "2026-11-16")] alias support_zpow_le := supportFinset_zpow_le

@[simp]
theorem supportFinset_swap {x y : α} (h : x ≠ y) : supportFinset (swap x y) = {x, y} := by
  grind [supportFinset]

@[deprecated (since := "2026-11-16")] alias support_swap := supportFinset_swap

theorem supportFinset_swap_iff (x y : α) : supportFinset (swap x y) = {x, y} ↔ x ≠ y := by
  refine ⟨fun h => ?_, fun h => supportFinset_swap h⟩
  rintro rfl
  simp [Finset.ext_iff] at h

@[deprecated (since := "2026-11-16")] alias support_swap_iff := supportFinset_swap_iff

theorem supportFinset_swap_mul_swap {x y z : α} (h : List.Nodup [x, y, z]) :
    supportFinset (swap x y * swap y z) = {x, y, z} := by
  simp only [List.not_mem_nil, and_true, List.mem_cons, not_false_iff, List.nodup_cons,
    and_self_iff, List.nodup_nil] at h
  push Not at h
  apply le_antisymm
  · convert supportFinset_mul_le (swap x y) (swap y z) using 1
    rw [supportFinset_swap h.left.left, supportFinset_swap h.right.left]
    simp [-Finset.union_singleton]
  · intro
    simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [swap_apply_of_ne_of_ne, h.left.left, h.left.left.symm, h.left.right.symm,
        h.left.right.left.symm, h.right.left.symm]

@[deprecated (since := "2026-11-16")] alias support_swap_mul_swap := supportFinset_swap_mul_swap

theorem supportFinset_swap_mul_ge_supportFinset_sdiff (f : Perm α) (x y : α) :
    f.supportFinset \ {x, y} ≤ (swap x y * f).supportFinset := by
  intro
  simp only [and_imp, Perm.coe_mul, Function.comp_apply, Ne, mem_supportFinset, mem_insert,
      mem_sdiff,
    mem_singleton]
  push Not
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

@[deprecated (since := "2026-11-16")] alias support_swap_mul_ge_support_sdiff :=
    supportFinset_swap_mul_ge_supportFinset_sdiff

@[deprecated (since := "2026-06-03")]
alias support_swap_mul_ge_support_diff := supportFinset_swap_mul_ge_supportFinset_sdiff

theorem supportFinset_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) :
    (swap x (f x) * f).supportFinset = f.supportFinset \ {x} := by
  by_cases hx : f x = x
  · simp [hx, sdiff_singleton_eq_erase, notMem_supportFinset.mpr hx, erase_eq_of_notMem, pull_end]
  ext z
  by_cases hzx : z = x
  · simp [hzx]
  by_cases hzf : z = f x
  · simp [hzf, hx, h, swap_apply_of_ne_of_ne]
  by_cases hzfx : f z = x
  · simp [Ne.symm hzx, hzx, Ne.symm hzf, hzfx]
  · simp [hzx, hzfx, f.injective.ne hzx, swap_apply_of_ne_of_ne]

@[deprecated (since := "2026-11-16")] alias support_swap_mul_eq := supportFinset_swap_mul_eq

theorem mem_supportFinset_swap_mul_imp_mem_supportFinset_ne {x y : α}
    (hy : y ∈ supportFinset (swap x (f x) * f)) :
    y ∈ supportFinset f ∧ y ≠ x := by
  simp only [mem_supportFinset, swap_apply_def, mul_apply, f.injective.eq_iff] at *
  grind

@[deprecated (since := "2026-11-16")] alias mem_support_swap_mul_imp_mem_support_ne :=
    mem_supportFinset_swap_mul_imp_mem_supportFinset_ne

omit [Fintype α] in
theorem disjoint_swap_swap {x y z t : α} (h : [x, y, z, t].Nodup) :
    Disjoint (swap x y) (swap z t) := by
  intro; grind

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α}
    (hx : x ∈ f.supportFinset) : x ∉ g.supportFinset :=
  disjoint_left.mp h.disjoint_supportFinset hx

theorem eq_on_supportFinset_mem_disjoint {l : List (Perm α)} (h : f ∈ l)
    (hl : l.Pairwise Disjoint) :
    ∀ x ∈ f.supportFinset, f x = l.prod x := by
  induction l with
  | nil => simp at h
  | cons hd tl IH =>
    intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply,
        notMem_supportFinset.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← notMem_supportFinset]
      refine (hl.left _ h).symm.mem_imp ?_
      simpa using hx

@[deprecated (since := "2026-11-16")] alias eq_on_support_mem_disjoint :=
    eq_on_supportFinset_mem_disjoint

theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.supportFinset ≤ f.supportFinset)
    (hg : y.supportFinset ≤ g.supportFinset) : Disjoint x y := by
  rw [disjoint_iff_disjoint_supportFinset] at h ⊢
  exact h.mono hf hg

theorem supportFinset_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.supportFinset ≤ l.prod.supportFinset := by
  intro x hx
  rwa [mem_supportFinset, ← eq_on_supportFinset_mem_disjoint h hl _ hx, ← mem_supportFinset]

@[deprecated (since := "2026-11-16")] alias support_le_prod_of_mem := supportFinset_le_prod_of_mem

section ExtendDomain

variable {β : Type*} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem supportFinset_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    supportFinset (g.extendDomain f) = g.supportFinset.map f.asEmbedding := by
  ext b
  simp only [mem_map, Ne,
    mem_supportFinset]
  by_cases pb : p b
  · rw [extendDomain_apply_subtype _ _ pb]
    grind [asEmbedding_apply]
  · rw [extendDomain_apply_not_subtype _ _ pb]
    simp only [not_exists, false_iff, not_and, not_true]
    rintro a _ rfl
    exact pb (Subtype.prop _)

@[deprecated (since := "2026-11-16")] alias support_extend_domain := supportFinset_extend_domain

theorem card_supportFinset_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    #(g.extendDomain f).supportFinset = #g.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_extend_domain :=
    card_supportFinset_extend_domain

end ExtendDomain

section Card

theorem card_supportFinset_eq_zero {f : Perm α} : #f.supportFinset = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, supportFinset_eq_empty_iff]

@[deprecated (since := "2026-11-16")] alias card_support_eq_zero := card_supportFinset_eq_zero

theorem one_lt_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < #f.supportFinset := by
  simp_rw [one_lt_card_iff, mem_supportFinset, ← not_or]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_self_iff, or_self_iff] at h

@[deprecated (since := "2026-11-16")] alias one_lt_card_support_of_ne_one :=
    one_lt_card_supportFinset_of_ne_one

theorem card_supportFinset_ne_one (f : Perm α) : #f.supportFinset ≠ 1 := by
  by_cases h : f = 1
  · exact ne_of_eq_of_ne (card_supportFinset_eq_zero.mpr h) zero_ne_one
  · exact ne_of_gt (one_lt_card_supportFinset_of_ne_one h)

@[deprecated (since := "2026-11-16")] alias card_support_ne_one := card_supportFinset_ne_one

@[simp]
theorem card_supportFinset_le_one {f : Perm α} : #f.supportFinset ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eq, Nat.lt_succ_iff, Nat.le_zero, card_supportFinset_eq_zero,
      or_iff_not_imp_right,
    imp_iff_right f.card_supportFinset_ne_one]

@[deprecated (since := "2026-11-16")] alias card_support_le_one := card_supportFinset_le_one

theorem two_le_card_supportFinset_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ #f.supportFinset :=
  one_lt_card_supportFinset_of_ne_one h

@[deprecated (since := "2026-11-16")] alias two_le_card_support_of_ne_one :=
    two_le_card_supportFinset_of_ne_one

theorem card_supportFinset_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) :
    #(swap x (f x) * f).supportFinset < #f.supportFinset :=
  Finset.card_lt_card
    ⟨fun _ hz => (mem_supportFinset_swap_mul_imp_mem_supportFinset_ne hz).left, fun h =>
      absurd (h (mem_supportFinset.2 hx)) (mt mem_supportFinset.1 (by simp))⟩

@[deprecated (since := "2026-11-16")] alias card_support_swap_mul := card_supportFinset_swap_mul

theorem card_supportFinset_swap {x y : α} (hxy : x ≠ y) : #(swap x y).supportFinset = 2 :=
  show #(swap x y).supportFinset = #⟨x ::ₘ y ::ₘ 0, by simp [hxy]⟩ from
    congr(card $(by simp [supportFinset_swap hxy, *, Finset.ext_iff]))

@[deprecated (since := "2026-11-16")] alias card_support_swap := card_supportFinset_swap

@[simp]
theorem card_supportFinset_eq_two {f : Perm α} : #f.supportFinset = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine ⟨x, y, hmem, ?_⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b =>
        by rw [← mem_supportFinset, ← hins, mem_insert, mem_singleton]
    by_cases ha : f a = a
    · have ha' := not_or.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
      · rw [Or.resolve_right ha' ha, swap_apply_right]
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_supportFinset_swap hxy

@[deprecated (since := "2026-11-16")] alias card_support_eq_two := card_supportFinset_eq_two

theorem Disjoint.card_supportFinset_mul (h : Disjoint f g) :
    #(f * g).supportFinset = #f.supportFinset + #g.supportFinset := by
  rw [← Finset.card_union_of_disjoint]
  · congr
    ext
    simp [h.supportFinset_mul]
  · simpa using h.disjoint_supportFinset

@[deprecated (since := "2026-11-16")] alias Disjoint.card_support_mul :=
    Disjoint.card_supportFinset_mul

theorem card_supportFinset_prod_list_of_pairwise_disjoint {l : List (Perm α)}
    (h : l.Pairwise Disjoint) :
    #l.prod.supportFinset = (l.map (card ∘ supportFinset)).sum := by
  induction l with
  | nil => exact card_supportFinset_eq_zero.mpr rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_supportFinset_mul

@[deprecated (since := "2026-11-16")] alias card_support_prod_list_of_pairwise_disjoint :=
    card_supportFinset_prod_list_of_pairwise_disjoint

end Card

end supportFinset

@[simp]
theorem supportFinset_subtypePerm [DecidableEq α] {s : Finset α} (f : Perm α) (h) :
    (f.subtypePerm h : Perm s).supportFinset = ({x | f x ≠ x} : Finset s) := by
  ext; simp [Subtype.ext_iff]

@[deprecated (since := "2026-11-16")] alias support_subtypePerm := supportFinset_subtypePerm

end Equiv.Perm

section FixedPoints

namespace Equiv.Perm
/-!
### Fixed points
-/

variable {α : Type*}

theorem fixed_point_card_lt_of_ne_one [DecidableEq α] [Fintype α] {σ : Perm α} (h : σ ≠ 1) :
    #{x | σ x = x} < Fintype.card α - 1 := by
  rw [Nat.lt_sub_iff_add_lt, ← Nat.lt_sub_iff_add_lt', ← Finset.card_compl, Finset.compl_filter]
  exact one_lt_card_supportFinset_of_ne_one h

end Equiv.Perm

end FixedPoints

section Conjugation

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Perm α}

@[simp]
theorem supportFinset_conj : (σ * τ * σ⁻¹).supportFinset = τ.supportFinset.map σ.toEmbedding := by
  ext
  simp only [mem_map_equiv, Perm.coe_mul, Function.comp_apply, Ne, Perm.mem_supportFinset,
    Equiv.eq_symm_apply, inv_def]

@[deprecated (since := "2026-11-16")] alias support_conj := supportFinset_conj

theorem card_supportFinset_conj : #(σ * τ * σ⁻¹).supportFinset = #τ.supportFinset := by simp

@[deprecated (since := "2026-11-16")] alias card_support_conj := card_supportFinset_conj

end Equiv.Perm

end Conjugation
