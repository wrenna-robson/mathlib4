/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common

/-!
# Lists in product and sigma types

This file proves basic properties of `List.product` and `List.sigma`, which are list constructions
living in `Prod` and `Sigma` types respectively. Their definitions can be found in
[`Data.List.Defs`](./defs). Beware, this is not about `List.prod`, the multiplicative product.
-/

public section


variable {α β : Type*}

namespace List

/-! ### product -/


@[simp]
theorem nil_product (l : List β) : (@nil α) ×ˢ l = [] :=
  rfl

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂) :=
  rfl

@[simp]
theorem product_nil : ∀ l : List α, l ×ˢ (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil l]

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) ∈ l₁ ×ˢ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, and_left_comm]

theorem length_product (l₁ : List α) (l₂ : List β) :
    length (l₁ ×ˢ l₂) = length l₁ * length l₂ := by
  induction l₁ with
  | nil => exact (Nat.zero_mul _).symm
  | cons x l₁ IH =>
    simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

/-! ### sigma -/


variable {σ : α → Type*}

@[simp, grind =]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).sigma l = [] :=
  rfl

@[simp, grind =]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂ :=
  rfl

@[simp, grind =]
theorem sigma_nil (l : List α) : (l.sigma fun a => @nil (σ a)) = [] := by
  induction l <;> grind

@[simp, grind =]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {ab : (a : α) × σ a} :
    ab ∈ l₁.sigma l₂ ↔ ab.1 ∈ l₁ ∧ ab.2 ∈ l₂ ab.1 := by grind [List.sigma]

@[simp, grind =]
theorem length_sigma {σ : α → Type*} (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map (length <| l₂ ·)).sum := by induction l₁ <;> grind

/-! ### Miscellaneous lemmas -/

@[simp 1100]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  simp

end List
