module

public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem injective_of_scalars {ι V W : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S)
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (h : ∀ σ, S σ ≠ ⊥ → ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f) :
    Function.Injective A := by
  classical
  have h' : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f := by
    intro σ
    by_cases hσ : S σ = ⊥
    · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
      rw [hσ, Submodule.mem_bot] at hf
      simp [hf]
    · exact h σ hσ
  choose c hc0 hc using h'
  let _ := hS.chooseDecomposition
  have key : ∀ v : V, ∀ k, ((DirectSum.decompose S (B (A v)) k : S k) : V) =
      c k • ((DirectSum.decompose S v k : S k) : V) := by
    intro v
    induction v using DirectSum.Decomposition.inductionOn S with
    | zero => intro k; simp
    | @homogeneous i m =>
      intro k
      have hm : B (A (m : V)) ∈ S i := by
        rw [hc i _ m.2]; exact (S i).smul_mem _ m.2
      by_cases hik : i = k
      · subst hik
        rw [DirectSum.decompose_of_mem_same S hm, DirectSum.decompose_of_mem_same S m.2, hc i _ m.2]
      · rw [DirectSum.decompose_of_mem_ne S hm hik, DirectSum.decompose_of_mem_ne S m.2 hik, smul_zero]
    | add a b ha hb =>
      intro k
      simp only [map_add (f := _), DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, smul_add, ha k, hb k]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have hz : DirectSum.decompose S v = 0 := by
    ext k
    have := key v k
    rw [hv, map_zero, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 k)
  exact (DirectSum.decompose S).injective (by rw [hz, DirectSum.decompose_zero])

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLp
section
noncomputable section

namespace Formalism.MainNotions.J

open Finset Matrix

section Pattern

variable {n : ℕ} {F : Type} [Field F]

def Pat (S : Finset (Fin n × Fin n)) (A : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, (i, j) ∉ S → A i j = if i = j then 1 else 0

theorem pat_det (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) (A : Matrix (Fin n) (Fin n) F)
    (h : Pat S A) : A.det = 1 := by
  have ht : A.BlockTriangular id := by
    intro i j hij
    have hn : (i, j) ∉ S := fun hm => absurd (hS _ hm) (not_lt.mpr (le_of_lt hij))
    have hij' : j < i := hij
    rw [h i j hn, if_neg (ne_of_gt hij')]
  rw [Matrix.det_of_isUpperTriangular ht]
  refine Finset.prod_eq_one fun i _ => ?_
  have hn : (i, i) ∉ S := fun hm => lt_irrefl _ (hS _ hm)
  rw [h i i hn, if_pos rfl]

def patMat (S : Finset (Fin n × Fin n)) (φ : S → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if h : (i, j) ∈ S then φ ⟨(i, j), h⟩ else if i = j then 1 else 0

theorem patMat_pat (S : Finset (Fin n × Fin n)) (φ : S → F) : Pat S (patMat S φ) := fun i j h => by
  simp [patMat, h]

def patEquiv (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} ≃ (S → F) where
  toFun A := fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2
  invFun φ := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (patMat S φ)
    (by rw [pat_det S hS _ (patMat_pat S φ)]; exact one_ne_zero), patMat_pat S φ⟩
  left_inv A := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    show patMat S (fun p => (A.1 : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) i j = (A.1 : Matrix (Fin n) (Fin n) F) i j
    by_cases h : (i, j) ∈ S
    · simp [patMat, h]
    · simp [patMat, h, A.2 i j h]
  right_inv φ := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    show patMat S φ i j = _
    simp [patMat, h]

theorem card_pat [Finite F] (S : Finset (Fin n × Fin n)) (hS : ∀ p ∈ S, p.1 < p.2) :
    Nat.card {A : GL (Fin n) F // Pat S (A : Matrix (Fin n) (Fin n) F)} = Nat.card F ^ S.card := by
  rw [Nat.card_congr (patEquiv S hS), Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]

end Pattern

def upS (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun p => p.1 < p.2

theorem card_upS (n : ℕ) : (upS n).card = n * (n - 1) / 2 := by
  unfold upS
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have : ∀ j : Fin n, (∑ i : Fin n, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have : (univ.filter fun i : Fin n => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

def rowS (k rS n : ℕ) : Finset (Fin n × Fin n) :=
  (upS n).filter fun p => ¬ (p.2.val = rS + k ∧ rS ≤ p.1.val)

theorem card_rowS (k rS n : ℕ) (hn : rS + k < n) : (rowS k rS n).card + k = n * (n - 1) / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := upS n)
    (fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val)
  rw [card_upS] at h
  have hk : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val).card = k := by
    have : ((upS n).filter fun p : Fin n × Fin n => p.2.val = rS + k ∧ rS ≤ p.1.val) =
        (univ : Finset (Fin k)).image fun i => ((⟨rS + i.val, by omega⟩ : Fin n), (⟨rS + k, hn⟩ : Fin n)) := by
      ext ⟨a, b⟩
      simp only [upS, mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨hab, hb, ha⟩
        have hab' : a.val < b.val := hab
        exact ⟨⟨a.val - rS, by omega⟩, Fin.ext (by simp; omega), Fin.ext (by simp [hb])⟩
      · rintro ⟨i, rfl, rfl⟩
        refine ⟨?_, rfl, by simp⟩
        show rS + i.val < rS + k
        omega
    rw [this, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
    intro i j hij
    have := congrArg (fun p : Fin n × Fin n => p.1.val) hij
    simp at this
    exact Fin.ext this
  unfold rowS
  omega

theorem isUnitri_iff {n : ℕ} {F : Type} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsUnitri A ↔ Pat (upS n) A := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    simp only [upS, mem_filter, mem_univ, true_and, not_lt] at hij
    rcases eq_or_lt_of_le hij with h | h
    · subst h; simp [h2]
    · rw [h1 i j h, if_neg (ne_of_gt h)]
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [h i j (by simp [upS, le_of_lt hij]), if_neg (ne_of_gt hij)]
    · rw [h i i (by simp [upS]), if_pos rfl]

theorem isRowLev_iff {n : ℕ} {F : Type} [Field F] (k rS : ℕ) (A : Matrix (Fin n) (Fin n) F) :
    StandardLattice.IsRowLev k rS A ↔ Pat (rowS k rS n) A := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ i j hij
    by_cases e : i = j
    · subst e; simp [h2]
    rw [if_neg e]
    have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp only [rowS, upS, mem_filter, mem_univ, true_and, not_and] at hij
    by_cases hlt : i < j
    · obtain ⟨hj, hi⟩ : j.val = rS + k ∧ rS ≤ i.val := by
        by_contra hc
        exact hij hlt (fun a b => hc ⟨a, b⟩)
      have hlt' : i.val < j.val := hlt
      exact h4 i j hj e (by unfold StandardLattice.blk; split_ifs <;> omega)
    · have hlt' : j.val < i.val := by
        have : ¬ i.val < j.val := hlt
        omega
      by_cases hb : StandardLattice.blk rS k j.val < StandardLattice.blk rS k i.val
      · exact h1 i j hb
      · refine h3 i j ?_ hlt'
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hb hij => ?_, fun i j hj hne hb => ?_⟩
    · have hlt : j.val < i.val := by
        revert hij
        unfold StandardLattice.blk
        split_ifs <;> omega
      have hlt2 : ¬ i < j := fun hh => by
        have : i.val < j.val := hh
        omega
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (fun e => by subst e; omega)]
    · rw [h i i (by simp [rowS, upS]), if_pos rfl]
    · have hlt2 : ¬ i < j := not_lt.mpr (le_of_lt hij)
      rw [h i j (by simp [rowS, upS, hlt2]), if_neg (ne_of_gt hij)]
    · have hi : rS ≤ i.val := by
        revert hb
        unfold StandardLattice.blk
        split_ifs <;> omega
      rw [h i j (by simp [rowS, hj, hi]), if_neg hne]

end Formalism.MainNotions.J

end
end

