/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.GroupTheory.Perm.Support.Basic

/-!
# Disjoint permutations

## Main definitions

In the following, `f g : Equiv.Perm α`.

* `Equiv.Perm.Disjoint`: two permutations `f` and `g` are `Disjoint` if every element is fixed
  either by `f`, or by `g`: equivalently, their supports are disjoint.
-/

public section

namespace Equiv.Perm

variable {α : Type*}

section Disjoint

/-- Two permutations `f` and `g` are `Disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
@[irreducible] protected def Disjoint (f g : Perm α) := Disjoint f.support g.support

variable {f g h : Perm α}

unseal Perm.Disjoint in
theorem disjoint_iff_disjoint_support : f.Disjoint g ↔ Disjoint f.support g.support := Iff.rfl

theorem _root_.Disjoint.disjoint_perm (h : Disjoint f.support g.support) : f.Disjoint g :=
  disjoint_iff_disjoint_support.mpr h

theorem Disjoint.disjoint_support (h : f.Disjoint g) : Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.mp h

theorem Disjoint.mono {x y : Perm α} (hf : x.support ≤ f.support) (hg : y.support ≤ g.support)
    (h : f.Disjoint g) : x.Disjoint y := (h.disjoint_support.mono hf hg).disjoint_perm

theorem disjoint_iff_forall_eq_or_eq : f.Disjoint g ↔ ∀ x : α, f x = x ∨ g x = x := by
  simp only [disjoint_iff_disjoint_support, Set.disjoint_iff_inter_eq_empty, Set.ext_iff,
    Set.mem_inter_iff, mem_support, Set.mem_empty_iff_false, iff_false, not_and_or, not_not]

@[deprecated (since := "2026-11-17")] alias disjoint_iff_eq_or_eq := disjoint_iff_forall_eq_or_eq

@[symm] theorem Disjoint.symm (h : f.Disjoint g) : g.Disjoint f :=
  h.disjoint_support.symm.disjoint_perm

instance Disjoint.stdSymm : Std.Symm (α := Perm α) Perm.Disjoint where
  symm _ _ := Disjoint.symm

@[deprecated (since := "2026-06-10")] alias Disjoint.symmetric := Disjoint.stdSymm

theorem disjoint_comm : f.Disjoint g ↔ g.Disjoint f := ⟨Disjoint.symm, Disjoint.symm⟩

theorem Disjoint.mem_left_imp (h : f.Disjoint g) {x : α}
    (hx : x ∈ f.support) : x ∉ g.support :=
  Set.disjoint_left.mp h.disjoint_support hx

@[deprecated (since := "2026-11-17")] alias Disjoint.mem_imp := Disjoint.mem_left_imp

theorem Disjoint.mem_right_imp (h : f.Disjoint g) {x : α}
    (hx : x ∈ g.support) : x ∉ f.support :=
  Set.disjoint_right.mp h.disjoint_support hx

theorem Disjoint.eq_or_eq (hfg : f.Disjoint g) (x) : f x = x ∨ g x = x :=
  disjoint_iff_forall_eq_or_eq.mp hfg x

theorem Disjoint.of_apply_left_ne (hfg : f.Disjoint g) {x} (h : f x ≠ x) : g x = x :=
  notMem_support.mp (hfg.mem_left_imp (mem_support.mpr h))

theorem Disjoint.of_apply_right_ne (hfg : f.Disjoint g) {x} (h : g x ≠ x) : f x = x :=
  notMem_support.mp (hfg.mem_right_imp (mem_support.mpr h))

theorem Disjoint.commute (h : f.Disjoint g) : Commute f g := Equiv.ext fun x => by
  rcases h.eq_or_eq x with hf | hg
  · rcases h.eq_or_eq (g x) with hf' | hg' <;> simp_all [mul_apply]
  · rcases h.eq_or_eq (f x) with hf' | hg' <;> simp_all [mul_apply]

@[simp]
theorem disjoint_one_left (f : Perm α) : (1 : Perm α).Disjoint f := by
  simp [disjoint_iff_disjoint_support]

@[simp]
theorem disjoint_one_right (f : Perm α) : f.Disjoint 1 := by
  simp [disjoint_iff_disjoint_support]

@[simp]
theorem disjoint_refl_iff : f.Disjoint f ↔ f = 1 := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.eq_one : f.Disjoint f → f = 1 := by simp

theorem Disjoint.inv_left : f.Disjoint g → f⁻¹.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.inv_right (h : f.Disjoint g) : f.Disjoint g⁻¹ :=
  h.symm.inv_left.symm

@[simp] theorem disjoint_inv_left_iff : f⁻¹.Disjoint g ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

@[simp] theorem disjoint_inv_right_iff : f.Disjoint g⁻¹ ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support]

theorem Disjoint.mul_left (H1 : f.Disjoint h) (H2 : g.Disjoint h) : (f * g).Disjoint h :=
  ((H1.disjoint_support.union_left H2.disjoint_support).mono_left
    (support_mul_subset f g)).disjoint_perm

theorem Disjoint.mul_right (H1 : f.Disjoint g) (H2 : f.Disjoint h) : f.Disjoint (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

theorem Disjoint.support_mul (h : f.Disjoint g) :
    (f * g).support = f.support ∪ g.support := by
  refine le_antisymm (support_mul_subset _ _) fun a => ?_
  rw [Set.mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_or,
    not_imp_not]
  exact
    (h.eq_or_eq a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨congr(f $hg).symm.trans h, hg⟩

@[simp]
theorem disjoint_conj (h : Perm α) : (h * f * h⁻¹).Disjoint (h * g * h⁻¹) ↔ f.Disjoint g := by
  simp [disjoint_iff_disjoint_support, Set.disjoint_image_iff h.injective]

theorem Disjoint.conj (H : f.Disjoint g) (h : Perm α) : (h * f * h⁻¹).Disjoint (h * g * h⁻¹) :=
  (disjoint_conj h).2 H

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀ g ∈ l, f.Disjoint g) :
    f.Disjoint l.prod := by
  induction l with
  | nil => exact disjoint_one_right _
  | cons g l ih =>
    rw [List.prod_cons]
    exact (h _ List.mem_cons_self).mul_right (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem disjoint_noncommProd_right {ι : Type*} {k : ι → Perm α} {s : Finset ι}
    (hs : Set.Pairwise s fun i j ↦ Commute (k i) (k j))
    (hg : ∀ i ∈ s, g.Disjoint (k i)) :
    g.Disjoint (s.noncommProd k (hs)) :=
  s.noncommProd_induction k hs g.Disjoint (fun _ _ ↦ Disjoint.mul_right) (disjoint_one_right g) hg

open scoped List in
theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Perm.Disjoint)
    (hp : l₁ ~ l₂) : l₁.prod = l₂.prod :=
  hp.prod_eq' <| hl.imp Disjoint.commute

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l)
    (h2 : l.Pairwise Perm.Disjoint) : l.Nodup :=
  h2.imp_of_mem fun _ hb hab ↦ mt (fun h => (h ▸ hab).eq_one ▸ hb) h1

theorem Disjoint.apply_apply_eq_iff (hfg : f.Disjoint g) {a : α} :
    f (g a) = a ↔ f a = a ∧ g a = a :=
  ⟨by rcases hfg.eq_or_eq a <;> grind [f.injective], by grind⟩

theorem Disjoint.mul_apply_eq_iff (hfg : f.Disjoint g) {a : α} :
    (f * g) a = a ↔ f a = a ∧ g a = a := hfg.apply_apply_eq_iff

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : σ.Disjoint τ) :
    σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [Perm.ext_iff, one_apply, mul_apply, hστ.apply_apply_eq_iff, forall_and]

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : σ.Disjoint τ) (m n : ℤ) :
    (σ ^ m).Disjoint (τ ^ n) := hστ.mono (support_zpow_subset m) (support_zpow_subset n)

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : σ.Disjoint τ) (m n : ℕ) :
    (σ ^ m).Disjoint (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

theorem disjoint_swap_swap [DecidableEq α] {x y z t : α} (h : [x, y, z, t].Nodup) :
    (swap x y).Disjoint (swap z t) := by grind [disjoint_iff_forall_eq_or_eq]

end Disjoint

end Equiv.Perm
