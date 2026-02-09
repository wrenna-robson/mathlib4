/-
Copyright (c) 2026 Wrenan Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenan Robson
-/
module
public import Mathlib.Data.List.Defs
public import Mathlib.Data.FinEnum

/-!


-/

@[expose] public section

namespace List

variable {α : Type*} {l : List α}

instance {v : α} : NeZero (v :: l).length := ⟨Nat.succ_ne_zero _⟩

attribute [coe] get

/-- There is a coercion from `l : Type` to `α`. -/
instance instCoeOutFinLength : CoeOut l α := ⟨l.get⟩

@[simp] theorem coe_mem {x : l} : ↑x ∈ l := List.get_mem _ _

@[simp, grind =]
theorem coe_mk {i : Nat} {hi : i < l.length} : ↑(Fin.mk i hi) = l[i] := rfl

@[simp]
protected theorem forall_coe (p : l → Prop) :
    (∀ x : l, p x) ↔ ∀ (i : Nat) (hi : i < l.length), p ⟨i, hi⟩ := Fin.forall_iff

@[simp]
protected theorem exists_coe (p : l → Prop) :
    (∃ x : l, p x) ↔ ∃ (i : Nat) (hi : i < l.length), p ⟨i, hi⟩ := Fin.exists_iff

instance : FinEnum l where
  card := l.length
  equiv := Equiv.refl _

theorem card_eq : Fintype.card l = l.length := (FinEnum.card_eq_fintypeCard).symm

instance : IsEmpty ([] : List α) := Fin.isEmpty

instance {v : α} : Unique [v] := Fin.instUnique

instance {v : α} : Inhabited (v :: l) := ⟨0⟩

@[simp, grind =]
theorem coe_default {v : α} : (default : v :: l) = v := rfl

@[simp, grind =]
theorem coe_zero {v : α} : (0 : v :: l) = v := rfl

/-- If `l = l'` then there's an equivalence between the appropriate types. -/
@[simps]
def cast {l' : List α} (h : l = l') : l ≃ l' where
  toFun x := ⟨x.1, Nat.lt_of_lt_of_eq x.2 <| h ▸ rfl⟩
  invFun x := ⟨x.1, Nat.lt_of_lt_of_eq x.2 <| h ▸ rfl⟩

/-- `x :: l` is equivalent to `Option l`. -/
def consEquiv (v : α) : v :: l ≃ Option l where
  toFun x := x.cases none some
  invFun x := x.recOn 0 Fin.succ
  left_inv x := x.cases rfl (fun _ => rfl)
  right_inv x := x.recOn rfl (fun _ => rfl)

@[simp, grind =]
lemma consEquiv_zero {v : α} : l.consEquiv v 0 = none := rfl

@[simp, grind =]
lemma consEquiv_succ {v : α} {x : l} : l.consEquiv v x.succ = some x := rfl

@[simp, grind =]
lemma consEquiv_symm_none {v : α} : (l.consEquiv v).symm none = 0 := rfl

@[simp, grind =]
lemma consEquiv_symm_some {v : α} {x : l} : (l.consEquiv v).symm (some x) = x.succ := rfl

def mapEquiv {α β} {l : List α} (f : α → β) : l ≃ l.map f where
  toFun x := ⟨x.1, Nat.lt_of_lt_of_eq x.2 (l.length_map _).symm⟩
  invFun x := ⟨x.1, Nat.lt_of_lt_of_eq x.2 (l.length_map _)⟩

theorem mapEquiv_apply {α β} {l : List α} {x : l} (f : α → β) :
    l.mapEquiv f x = f x := getElem_map _

theorem apply_mapEquiv_symm_apply {α β} {l : List α} (f : α → β) {x : l.map f} :
    f ((l.mapEquiv f).symm x) = x := (getElem_map _).symm

end List
