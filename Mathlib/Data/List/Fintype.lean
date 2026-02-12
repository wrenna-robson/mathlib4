/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module
public import Mathlib.Data.List.Defs
public import Mathlib.Data.Fintype.Card

/-!


-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v}

namespace List

@[simps!]
def getAttach (l : List α) : Fin l.length → { x // x ∈ l } := Subtype.coind l.get l.get_mem

variable {l : List α}

@[simp, grind =]
theorem val_comp_getAttach : Subtype.val ∘ l.getAttach = l.get := rfl

theorem map_getAttach_finRange : map l.getAttach (finRange l.length) =
    l.attach := by apply ext_getElem <;> simp [Subtype.ext_iff]

abbrev Idx (l : List α) := Fin l.length

theorem Subperm.map (f : α → β) {l₁ l₂ : List α} (p : l₁ <+~ l₂) : map f l₁ <+~ map f l₂ :=
  ⟨p.choose.map _, p.choose_spec.1.map _, p.choose_spec.2.map _⟩

end List

namespace Function.Embedding

open List

variable {n m : ℕ} {l₁ l₂ : List α}

theorem map_finRange_subperm (f : Fin n ↪ Fin m) : map f (finRange n) <+~ finRange m := by
  exact List.Nodup.subperm ((nodup_finRange _).map f.injective) (fun a _ => mem_finRange a)

theorem subperm_of_get_comp (f : Fin l₁.length ↪ Fin l₂.length)
    (h : l₂.get ∘ f = l₁.get) : l₁ <+~ l₂ := by
  simp_rw [← l₂.map_get_finRange, ← l₁.map_get_finRange, ← h, ← map_map]
  refine Subperm.map l₂.get ?_
  exact f.map_finRange_subperm

end Function.Embedding

namespace Equiv

open List

variable {n m : ℕ} {l₁ l₂ : List α}

theorem map_finRange_perm (e : Fin n ≃ Fin m) : map e (finRange n) ~ finRange m := by
  simp only [perm_ext_iff_of_nodup ((nodup_finRange _).map e.injective) (nodup_finRange _), mem_map,
    mem_finRange, e.apply_eq_iff_eq_symm_apply, true_and, exists_eq, implies_true]

theorem map_symm_finRange_perm (e : Fin n ≃ Fin m) : map e.symm (finRange m) ~ finRange n :=
  map_finRange_perm e.symm

theorem perm_of_get_comp (e : Fin l₁.length ≃ Fin l₂.length)
    (h : l₂.get ∘ e = l₁.get) : l₁ ~ l₂ := by
  simp_rw [← l₂.map_get_finRange, ← l₁.map_get_finRange, ← h, ← map_map]
  refine Perm.map l₂.get ?_
  exact e.map_finRange_perm

end Equiv

namespace List


theorem exists_perm_sublist' {l₁ l₁' l₂' : List α} (s : l₁ ~ l₁') (p : l₁' <+ l₂') :
    ∃ l₂, l₁ <+ l₂ ∧ l₂ ~ l₂' := by
  induction s generalizing l₂' with
  | nil => exact ⟨l₂', p, .refl _⟩
  | cons x _ IH =>
    simp_rw [List.cons_sublist_iff] at p ⊢
    rcases p with ⟨r₁, r₂, rfl, h₂, h₃⟩
    rcases IH h₃ with ⟨l₂, hl₂, hl₂'⟩
    exact ⟨r₁ ++ l₂, ⟨_, _, rfl, h₂, hl₂⟩, Perm.rfl.append hl₂'⟩
  | swap x y l' =>
    match p with
    | .cons _ (.cons _ s) => _
    | .cons _ (.cons₂ _ s) => _
    | .cons₂ _ (.cons _ s) => _
    | .cons₂ _ (.cons₂ _ s) => _
  | trans _ _ IH₁ IH₂ => _

inductive MySubPerm : List α → List α

variable {l l₁ l₂ : List α}

section LawfulBEq
variable [BEq α] [LawfulBEq α]

def Subperm.embedding (h : l₁ <+~ l₂) :
    Fin l₁.length ↪ Fin l₂.length  where
  toFun := h.idxInj
  inj' := h.idxInj_injective

@[simp, grind =]
theorem Subperm.getElem_val_embedding_apply {l₁ l₂ : List α} (h : l₁ <+~ l₂)
    (x : Fin l₁.length) : l₂[(h.embedding x).1] = l₁[x.1] := by simp [Subperm.embedding]

theorem Subperm.get_comp_embedding {l₁ l₂ : List α} (h : l₁ <+~ l₂) :
    l₂.get ∘ h.embedding = l₁.get := funext <| h.getElem_val_embedding_apply

theorem subperm_iff_exists_equiv {l₁ l₂ : List α} :
    l₁ <+~ l₂ ↔ ∃ (f : Fin l₁.length  ↪ Fin l₂.length), l₂.get ∘ f = l₁.get :=
  ⟨fun h => ⟨h.embedding, h.get_comp_embedding⟩, fun ⟨f, hf⟩ => f.subperm_of_get_comp hf⟩

@[simps!]
def Perm.equiv {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    Fin l₁.length ≃ Fin l₂.length  where
  toFun := h.idxBij
  invFun := h.symm.idxBij
  left_inv := h.idxBij_symm_leftInverse_idxBij
  right_inv := h.idxBij_symm_rightInverse_idxBij

@[simp, grind =]
theorem Perm.symm_equiv {l₁ l₂ : List α} (h : l₁ ~ l₂) : h.symm.equiv = h.equiv.symm := rfl

@[simp, grind =]
theorem Perm.getElem_val_equiv_apply {l₁ l₂ : List α} (h : l₁ ~ l₂)
    (x : Fin l₁.length) : l₂[(h.equiv x).1] = l₁[x.1] := by simp

@[simp, grind =]
theorem Perm.getElem_val_equiv_symm_apply {l₁ l₂ : List α} (h : l₁ ~ l₂)
    (x : Fin l₂.length) : l₁[(h.equiv.symm x).1] = l₂[x.1] := by simp

theorem Perm.get_comp_equiv {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    l₂.get ∘ h.equiv = l₁.get := funext <| h.getElem_val_equiv_apply

theorem Perm.get_comp_equiv_symm {l₁ l₂ : List α} (h : l₁ ~ l₂) :
    l₁.get ∘ h.equiv.symm = l₂.get := funext <| h.getElem_val_equiv_symm_apply

theorem perm_iff_exists_equiv {l₁ l₂ : List α} :
    l₁ ~ l₂ ↔ ∃ (e : Fin l₁.length ≃ Fin l₂.length), l₂.get ∘ e = l₁.get :=
  ⟨fun h => ⟨h.equiv, h.get_comp_equiv⟩, fun ⟨e, he⟩ => e.perm_of_get_comp he⟩

abbrev SigmaCount [BEq α] (l : List α) := (x : α) × Fin (l.count x)


@[simp, grind =]
theorem fst_comp_idxToSigmaCount : Sigma.fst ∘ l.idxToSigmaCount = l.get := rfl

@[simp, grind .]
theorem fst_SigmaCount_mem (xc : l.SigmaCount) : xc.1 ∈ l := l.count_pos_iff.mp xc.2.pos

@[simps!]
def idxEquivSigmaCount : Fin l.length ≃ l.SigmaCount where
  toFun := l.idxToSigmaCount
  invFun := l.sigmaCountToIdx
  left_inv := l.leftInverse_sigmaCountToIdx_idxToSigmaCount
  right_inv := l.rightInverse_sigmaCountToIdx_idxToSigmaCount

instance : Fintype (l.SigmaCount) := Fintype.ofEquiv _ idxEquivSigmaCount

@[simp]
theorem sigmaCount_card_eq : Fintype.card (l.SigmaCount) = l.length :=
  (Fintype.ofEquiv_card _).trans (Fintype.card_fin _)

@[simps!]
def getAttachSigmaCount (l : List α) : l.SigmaCount → {x // x ∈ l} :=
  Subtype.coind Sigma.fst fst_SigmaCount_mem

@[simp, grind =]
theorem val_comp_getAttachSigmaCount : Subtype.val ∘ l.getAttachSigmaCount = Sigma.fst := rfl

@[simp, grind =]
theorem getAttachSigmaCount_comp_idxToSigmaCount :
    l.getAttachSigmaCount ∘ l.idxToSigmaCount = l.getAttach := rfl

def attachCount (l : List α) : List (l.SigmaCount) :=
  (finRange l.length).map l.idxToSigmaCount

theorem length_attachCount : l.attachCount.length = l.length :=
  (length_map _).trans length_finRange

@[simp, grind .]
theorem nodup_attachCount : l.attachCount.Nodup :=
  (List.nodup_finRange _).map injective_idxToSigmaCount

@[simp, grind .]
theorem complete_attachCount (xc : l.SigmaCount) : xc ∈ l.attachCount := by
  simp_rw [attachCount, List.mem_map, mem_finRange, true_and]
  exact ⟨l.sigmaCountToIdx xc, idxToSigmaCount_sigmaCountToIdx⟩

theorem map_fst_attachCount : l.attachCount.map Sigma.fst = l := map_map.trans l.map_get_finRange

theorem map_getAttachSigmaCount_attachCount :
    l.attachCount.map l.getAttachSigmaCount = l.attach := map_map.trans l.map_getAttach_finRange

end LawfulBEq

section DecidableEq

variable {l : List α} [DecidableEq α]

theorem toFinset_attachCount : l.attachCount.toFinset = Finset.univ := Finset.ext <| by simp

end DecidableEq

instance : IsEmpty (Fin ([] : List α).length) := Fin.isEmpty

instance {v : α} : Unique (Fin [v].length) := Fin.instUnique

end List

namespace List

structure ToType (l : List α) where
  idx : Fin l.length
  val : α
  get_of_idx : l.get idx = val

instance instCoeType {α : Type u} : CoeSort (List α) (Type u) := ⟨ToType⟩

notation:max "↥" l:40  => ToType l

namespace ToType

variable {l l' : List α}

@[ext, grind ext] theorem ext {x y : l} : x.idx = y.idx → x = y := by
  cases x; cases y; grind

def mkOfFin (i : Fin l.length) : l := ⟨i, l.get i, rfl⟩

@[simp, grind =]
theorem mk_eq_mkOfFin {idx : Fin l.length} {val : α} {get_idx} :
    mk idx val get_idx = mkOfFin idx := ext rfl

/-- There is a coercion from `l : Type` to `α`. -/
instance instCoeOutFinLength : CoeOut l α := ⟨val⟩

@[grind =] theorem val_eq {x : l} : x.val = l[x.idx.1] := x.get_of_idx.symm
theorem getElem_of_idx {x : l} : l[x.idx] = x.val := x.get_of_idx

@[simp] theorem mem_val {x : l} : x.val ∈ l := mem_of_getElem getElem_of_idx

@[grind =] theorem mkOfFin_idx {i : Fin l.length} : (mkOfFin i).idx = i := rfl
@[grind =] theorem mkOfFin_apply_idx {x : l} : mkOfFin x.idx = x := by grind
theorem val_mkOfFin {i : Fin l.length} : (mkOfFin i).val = l[i.1] := by grind

theorem get_comp_idx : l.get ∘ idx = val := funext fun _ => getElem_of_idx

@[simps!]
def finEquiv : Fin l.length ≃ l where
  toFun := mkOfFin
  invFun := idx
  left_inv := by grind
  right_inv := by grind

@[simp]
protected theorem forall_mkOfFin (p : l → Prop) :
    (∀ x : l, p x) ↔ ∀ (i : Fin l.length), p (mkOfFin i) := finEquiv.symm.forall_congr_left

@[simp]
protected theorem exists_mkOfFin (p : l → Prop) :
    (∃ x : l, p x) ↔ ∃ (i : Fin l.length), p (mkOfFin i) := finEquiv.symm.exists_congr_left

instance : DecidableEq l := finEquiv.symm.decidableEq

instance : Fintype l := Fintype.ofEquiv _ finEquiv

theorem card_eq : Fintype.card l = l.length :=
  (Fintype.ofEquiv_card _).trans (Fintype.card_fin l.length)

instance : IsEmpty ([] : List α) := finEquiv.symm.isEmpty

instance {v : α} : Unique [v] := finEquiv.symm.unique

instance {v : α} : Inhabited (v :: l) := ⟨mkOfFin 0⟩

@[simp, grind =]
theorem coe_default {v : α} : (default : v :: l) = v := rfl

/-- If `l = l'` then there's an equivalence between the appropriate types. -/
@[simps!]
def cast (h : l = l') : l ≃ l' :=
  finEquiv.symm.trans <| (finCongr <| h ▸ rfl).trans finEquiv

@[simps!]
def mapEquiv {α β} {l : List α} (f : α → β) : l ≃ l.map f :=
  finEquiv.symm.trans <| (finCongr (length_map _).symm).trans finEquiv

def equivSigmaCount [BEq α] [LawfulBEq α] {l : List α} : l ≃ l.SigmaCount :=
  finEquiv.symm.trans l.idxEquivSigmaCount

@[simps! apply_val]
def embeddingOfSubperm [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ <+~ l₂) :
    l₁ ↪ l₂ := finEquiv.embeddingCongr finEquiv h.embedding

@[simps! symm_apply_val apply_val]
def equivOfPerm [BEq α] [LawfulBEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁ ≃ l₂ :=
  finEquiv.equivCongr finEquiv h.equiv

end ToType


end List
