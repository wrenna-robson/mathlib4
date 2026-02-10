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

universe u

variable {α : Type u}

instance : IsEmpty (Fin ([] : List α).length) := Fin.isEmpty

instance {v : α} : Unique (Fin [v].length) := Fin.instUnique

def ToType (l : List α) := {xi : α × Fin l.length // xi.1 = l[xi.2]}

instance instCoeType {α : Type u} : CoeSort (List α) (Type u) := ⟨ToType⟩

notation:max "↥" l:40  => ToType l

namespace ToType

variable {l l' : List α}

def val (x : l) : α := x.1.1
def idx (x : l) : Fin l.length := x.1.2

@[simp, grind =] theorem val_eq {x : l} : x.val = l[x.idx] := x.2
@[simp, grind =] theorem getElem_idx {x : l} : l[x.idx] =x.val := x.2.symm

theorem get_comp_idx : l.get ∘ idx = val := funext fun _ => getElem_idx

def mk (i : Fin l.length) : l := ⟨⟨l[i], i⟩, rfl⟩

@[simp, grind =] theorem idx_mk {i : Fin l.length} : (mk i).idx = i := rfl
@[simp, grind =] theorem val_mk {i : Fin l.length} : (mk i).val = l[i.1] := rfl

@[simp, grind =] theorem mk_idx {x : l} : mk x.idx = x :=
  Subtype.ext <| Prod.ext getElem_idx rfl

@[cases_eliminator, elab_as_elim]
def recOn {motive : l → Sort*} (mk : ∀ i : Fin l.length, motive (mk i)) (x : l) : motive x :=
  x.mk_idx ▸ mk x.idx

@[simp, grind =]
theorem recOn_mk {motive : l → Sort*} {mk : ∀ i : Fin l.length, motive (mk i)} (i : Fin l.length) :
    recOn mk (ToType.mk i) = mk i := rfl

@[ext] theorem ext {x y : l} : x.idx = y.idx → x = y := x.recOn <| y.recOn <| by simp

@[simps!]
def idxEquiv : l ≃ Fin l.length where
  toFun := idx
  invFun := mk
  left_inv := by grind
  right_inv := by grind

/-- There is a coercion from `l : Type` to `α`. -/
instance instCoeOutFinLength : CoeOut l α := ⟨val⟩

@[simp] theorem mem_val {x : l} : x.val ∈ l := mem_of_getElem getElem_idx

@[simp]
protected theorem forall_mk (p : l → Prop) :
    (∀ x : l, p x) ↔ ∀ (i : Fin l.length), p (mk i) :=
  ⟨by grind, fun h x => x.mk_idx ▸ h x.idx⟩

@[simp]
protected theorem exists_mk (p : l → Prop) :
    (∃ x : l, p x) ↔ ∃ (i : Fin l.length), p (mk i) :=
  ⟨fun ⟨x, h⟩ => ⟨x.idx, x.mk_idx ▸ h⟩, by grind⟩

instance : DecidableEq l := idxEquiv.decidableEq

instance : FinEnum l := {card := l.length, equiv := idxEquiv}

theorem card_eq : Fintype.card l = l.length := (FinEnum.card_eq_fintypeCard).symm

instance : IsEmpty ([] : List α) := idxEquiv.isEmpty

instance {v : α} : Unique [v] := idxEquiv.unique

instance {v : α} : Inhabited (v :: l) := ⟨mk 0⟩

@[simp, grind =]
theorem coe_default {v : α} : (default : v :: l) = v := rfl

/-- If `l = l'` then there's an equivalence between the appropriate types. -/
def cast (h : l = l') : l ≃ l' :=
  idxEquiv.trans <| (finCongr <| h ▸ rfl).trans idxEquiv.symm

theorem val_idx_cast (h : l = l') (x : l) : (cast h x).idx.val = x.idx.val := rfl

theorem val_cast (h : l = l') (x : l) : (cast h x).val = l'[x.idx]'(h ▸ by simp) := by
  simp [cast, idxEquiv]

def mapEquiv {α β} {l : List α} (f : α → β) : l ≃ l.map f :=
  idxEquiv.trans <| (finCongr (length_map _).symm).trans idxEquiv.symm

@[simp, grind =]
theorem val_idx_mapEquiv_apply {α β} {l : List α} {x : l} (f : α → β) :
    (mapEquiv f x).idx.val = x.idx.val := rfl

@[simp]
theorem val_mapEquiv_apply {α β} {l : List α} {x : l} (f : α → β) :
    (mapEquiv f x).val = f x.val := by grind

theorem apply_mapEquiv_symm_apply {α β} {l : List α} (f : α → β) {x : l.map f} :
    f ((l.mapEquiv f).symm x) = x := (getElem_map _).symm

def equivSigmaCount [BEq α] [LawfulBEq α] {l : List α} : l ≃ (x : α) × Fin (l.count x) where
  toFun := l.idxToSigmaCount
  invFun := l.sigmaCountToIdx
  left_inv := l.leftInverse_sigmaCountToIdx_idxToSigmaCount
  right_inv := l.rightInverse_sigmaCountToIdx_idxToSigmaCount

instance [BEq α] [LawfulBEq α] {l : List α} : FinEnum ((x : α) × Fin (l.count x)) :=
  FinEnum.ofEquiv _ equivSigmaCount.symm

def Subperm.embedding [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ <+~ l₂) : l₁ ↪ l₂ where
  toFun := h.idxInj
  inj' := h.idxInj_injective

theorem Subperm.coe_embedding [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ <+~ l₂) (x : l₁) :
  (h.embedding x : α) = (x : α) := by simp [Subperm.embedding]

def Perm.equiv [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁ ≃ l₂ where
  toFun := h.idxBij
  invFun := h.symm.idxBij
  left_inv := h.idxBij_symm_leftInverse_idxBij
  right_inv := h.idxBij_symm_rightInverse_idxBij

theorem Perm.coe_equiv [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) (x : l₁) :
  (h.equiv x : α) = (x : α) := by simp [Subperm.embedding]


def permOfEquiv {l₁ l₂ : List α} (e : l₁ ≃ l₂)

end ToType


end List
