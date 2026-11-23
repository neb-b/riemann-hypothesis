module

public import Mathlib
public import Formalism.PeriodIntegrals.JointBlockShapes.MinusPart
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.SameSign

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.FockInnerEqSumRight
section
noncomputable section

namespace FockRaiseLowInner

open MvPolynomial FockH1Action

variable {σ : Type*}

def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))

theorem fockInner_eq_support (P Q : MvPolynomial σ ℂ) :
    fockInner P Q = ∑ α ∈ P.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  unfold FockH1Action.fockInner
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.sum_eq_single α]
  · rw [if_pos rfl]
    rfl
  · intro β _ hβ
    rw [if_neg (Ne.symm hβ), mul_zero]
  · intro hα
    have h : AddMonoidAlgebra.coeff Q α = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
    rw [h]
    simp

theorem fockInner_eq_sum (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, α ∉ S → (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α = 0) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  classical
  rw [fockInner_eq_support]
  have h1 : (∑ α ∈ P.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx) (fun α _ hα => ?_)
    have h : AddMonoidAlgebra.coeff P α = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
    rw [h]
    simp
  have h2 : (∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx) (fun α _ hα => ?_)
    rw [hS α hα, zero_mul]
  rw [h1, h2]

theorem fockInner_eq_sum_left (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : P.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  refine fockInner_eq_sum P Q S (fun α hα => ?_)
  have h : AddMonoidAlgebra.coeff P α = 0 := by
    by_contra h'
    exact hα (hS (MvPolynomial.mem_support_iff.mpr h'))
  rw [h]
  simp

theorem fockInner_eq_sum_right (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : Q.support ⊆ S) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α := by
  refine fockInner_eq_sum P Q S (fun α hα => ?_)
  have h : AddMonoidAlgebra.coeff Q α = 0 := by
    by_contra h'
    exact hα (hS (MvPolynomial.mem_support_iff.mpr h'))
  rw [h, mul_zero]

theorem fockInner_zero_left (Q : MvPolynomial σ ℂ) : fockInner 0 Q = 0 := by
  rw [fockInner_eq_support]
  simp

theorem fockInner_zero_right (P : MvPolynomial σ ℂ) : fockInner P 0 = 0 := by
  rw [fockInner_eq_support]
  simp

theorem fockInner_add_right (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ + Q₂) = fockInner P Q₁ + fockInner P Q₂ := by
  rw [fockInner_eq_support P (Q₁ + Q₂), fockInner_eq_support P Q₁,
    fockInner_eq_support P Q₂, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [MvPolynomial.coeff_add]
  ring

theorem fockInner_smul_right (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner P (c • Q) = c * fockInner P Q := by
  rw [fockInner_eq_support P (c • Q), fockInner_eq_support P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul]
  ring

theorem fockInner_neg_right (P Q : MvPolynomial σ ℂ) :
    fockInner P (-Q) = - fockInner P Q := by
  rw [fockInner_eq_support P (-Q), fockInner_eq_support P Q, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg]
  ring

theorem fockInner_sub_right (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    fockInner P (Q₁ - Q₂) = fockInner P Q₁ - fockInner P Q₂ := by
  rw [sub_eq_add_neg, fockInner_add_right, fockInner_neg_right, ← sub_eq_add_neg]

private theorem fockInner_eq_sum_support_right (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P Q = ∑ α ∈ Q.support, (starRingEnd ℂ) (AddMonoidAlgebra.coeff P α) * AddMonoidAlgebra.coeff Q α * wt α :=
  fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _)

theorem fockInner_add_left (P₁ P₂ Q : MvPolynomial σ ℂ) :
    fockInner (P₁ + P₂) Q = fockInner P₁ Q + fockInner P₂ Q := by
  rw [fockInner_eq_sum_support_right (P₁ + P₂) Q, fockInner_eq_sum_support_right P₁ Q,
    fockInner_eq_sum_support_right P₂ Q, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [MvPolynomial.coeff_add, map_add (f := _)]
  ring

theorem fockInner_smul_left (P Q : MvPolynomial σ ℂ) (c : ℂ) :
    fockInner (c • P) Q = (starRingEnd ℂ) c * fockInner P Q := by
  rw [fockInner_eq_sum_support_right (c • P) Q, fockInner_eq_sum_support_right P Q, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_smul, smul_eq_mul, map_mul]
  ring

theorem fockInner_neg_left (P Q : MvPolynomial σ ℂ) :
    fockInner (-P) Q = - fockInner P Q := by
  rw [fockInner_eq_sum_support_right (-P) Q, fockInner_eq_sum_support_right P Q,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring

theorem fockInner_sum_right {ι : Type*} (s : Finset ι) (P : MvPolynomial σ ℂ)
    (f : ι → MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ s, f i) = ∑ i ∈ s, fockInner P (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_right, ih]

theorem fockInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ s, f i) Q = ∑ i ∈ s, fockInner (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, fockInner_zero_left]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, fockInner_add_left, ih]

theorem wt_conj (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by
  unfold wt Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact map_natCast _ _

theorem fockInner_swap (P Q : MvPolynomial σ ℂ) :
    fockInner Q P = (starRingEnd ℂ) (fockInner P Q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockInner_eq_support Q P, fockInner_eq_sum_support_right P Q, map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, map_mul, Complex.conj_conj, wt_conj]
  ring

theorem wt_single_add (l : σ) (α : σ →₀ ℕ) :
    wt (Finsupp.single l 1 + α) = ((α l : ℂ) + 1) * wt α := by
  classical
  have hl : l ∈ insert l α.support := Finset.mem_insert_self l α.support
  have hsub1 : (Finsupp.single l 1 + α).support ⊆ insert l α.support := by
    intro i hi
    rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hi
    by_cases h : i = l
    · rw [h]
      exact hl
    · rw [Finsupp.single_apply, if_neg (Ne.symm h), zero_add] at hi
      exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hi)
  have hsub2 : α.support ⊆ insert l α.support := fun i hi => Finset.mem_insert_of_mem hi
  unfold wt
  rw [Finsupp.prod_of_support_subset _ hsub1 _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hsub2 _ (fun _ _ => by simp)]
  have e1 := Finset.mul_prod_erase (insert l α.support)
    (fun i => (((Finsupp.single l 1 + α : σ →₀ ℕ) i).factorial : ℂ)) hl
  have e2 := Finset.mul_prod_erase (insert l α.support) (fun i => ((α i).factorial : ℂ)) hl
  try beta_reduce at e1 e2
  rw [← e1, ← e2]
  have hrest : ∏ x ∈ (insert l α.support).erase l, (((Finsupp.single l 1 + α : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ (insert l α.support).erase l, ((α x).factorial : ℂ) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hil : i ≠ l := Finset.ne_of_mem_erase hi
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hil), zero_add]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same,
    show (1 + α l).factorial = (α l + 1) * (α l).factorial from by
      rw [add_comm]
      exact Nat.factorial_succ _]
  push_cast
  ring

theorem fockInner_X_mul (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' Q (fun β b => ?_) (fun Q₁ Q₂ h₁ h₂ => ?_)
  · rw [pderiv_monomial,
      fockInner_eq_sum_right (X l * P) (monomial β b) {β} support_monomial_subset,
      fockInner_eq_sum_right P (monomial (β - Finsupp.single l 1) (b * (β l : ℂ)))
        {β - Finsupp.single l 1} support_monomial_subset,
      Finset.sum_singleton, Finset.sum_singleton, coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl]
    by_cases h : β l = 0
    · have hl : l ∉ β.support := by
        rw [Finsupp.mem_support_iff, not_not]
        exact h
      rw [coeff_X_mul', if_neg hl, h]
      simp
    · have hβ : β = Finsupp.single l 1 + (β - Finsupp.single l 1) := by
        ext i
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with hli
        · subst hli
          omega
        · omega
      obtain ⟨γ, rfl⟩ : ∃ γ, β = Finsupp.single l 1 + γ := ⟨_, hβ⟩
      rw [add_tsub_cancel_left, coeff_X_mul, wt_single_add, Finsupp.add_apply,
        Finsupp.single_eq_same]
      push_cast
      ring
  · rw [map_add (f := _), fockInner_add_right, fockInner_add_right, h₁, h₂]

theorem fockInner_mul_X (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner P (X l * Q) = fockInner (pderiv l P) Q := by
  rw [fockInner_swap (X l * Q) P, fockInner_X_mul, ← fockInner_swap]

theorem fischerConjLinearLeft : FockRL.FockLinL := by
  intro τ c P₁ P₂ Q
  rw [fockInner_add_left, fockInner_smul_left]

theorem fischerLinearRight : FockRL.FockLinR := by
  intro τ c P Q₁ Q₂
  rw [fockInner_add_right, fockInner_smul_right]

theorem fischerXAdjoint : FockRL.FockXAdj := by
  intro τ l P Q
  exact fockInner_X_mul l P Q

end FockRaiseLowInner
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.GradedOscillatorPropertyOf
section
namespace FockRL

theorem gradedOscillatorProperty_of (hK : KCStep) (hP : PCStep) (hA : AdjStep) (hM : MatStep) : FockH1Action.H1 := by
  intro p q r s
  obtain ⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩ := hM p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ d P hP'
    rw [e1]; exact hK p q r s _ (k1 Z hZ) d P hP'
  · intro Z hZ d P hP'
    rw [e2]; exact hK p q r s _ (k2 Z hZ) d P hP'
  · intro Z hZ P
    rw [e1]; exact hP p q r s _ (o1 Z hZ) P
  · intro Z hZ P
    rw [e2]; exact hP p q r s _ (o2 Z hZ) P
  · intro Z hZ P Q
    rw [e1, e1]; exact hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q
  · intro Z hZ P Q
    rw [e2, e2]; exact hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q

end FockRL
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.KroneckerMapOneRightNeZero
section
noncomputable section

open Matrix

namespace FockRL

def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

theorem Jm_eq_diagonal (p q : ℕ) : FockH1Action.Jm p q = Matrix.diagonal (jsgn (p := p) (q := q)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FockH1Action.Jm, FockH1Action.Jpq, jsgn,
      Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp_all

theorem conjR_apply {p q : ℕ} (Z : FockH1Action.Mat p q) (a b : FockH1Action.Ix p q) :
    FockH1Action.conjR Z a b = -(jsgn a * star (Z b a) * jsgn b) := by
  simp only [FockH1Action.conjR, FockH1Action.adjZ,
    Jm_eq_diagonal, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply]

theorem conjR_apply_of_not {p q : ℕ} (Z : FockH1Action.Mat p q) {a b : FockH1Action.Ix p q}
    (h : ¬ FockH1Action.sameBlock a b) : FockH1Action.conjR Z a b = (starRingEnd ℂ) (Z b a) := by
  rw [conjR_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp_all [FockH1Action.sameBlock, jsgn]

theorem sameBlock_symm {p q : ℕ} {a b : FockH1Action.Ix p q} (h : FockH1Action.sameBlock a b) :
    FockH1Action.sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [FockH1Action.sameBlock]

theorem conjR_isPC {p q : ℕ} (Z : FockH1Action.Mat p q) (hZ : FockH1Action.IsPC Z) :
    FockH1Action.IsPC (FockH1Action.conjR Z) := by
  intro a b hab
  rw [conjR_apply, hZ b a (sameBlock_symm hab)]
  simp

theorem linePos_left {p q r s : ℕ} (a a' : FockH1Action.Ix p q) (b : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a', b) : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock a a' := by
  rcases a with a | a <;> rcases a' with a' | a' <;> rcases b with b | b <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem linePos_right {p q r s : ℕ} (a : FockH1Action.Ix p q) (b b' : FockH1Action.Ix r s) :
    FockH1Action.linePos ((a, b) : FockH1Action.Ln p q r s) = FockH1Action.linePos ((a, b') : FockH1Action.Ln p q r s) ↔
      FockH1Action.sameBlock b b' := by
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [FockH1Action.linePos, FockH1Action.sameBlock]

theorem fockAct1_eq (p q r s : ℕ) (Z : FockH1Action.Mat p q) : FockH1Action.fockAct1 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s)) := by
  rfl

theorem fockAct2_eq (p q r s : ℕ) (Z : FockH1Action.Mat r s) : FockH1Action.fockAct2 p q r s Z =
    FockH1Action.omAct p q r s (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z) := by
  rfl

theorem kroneckerMap_one_right_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat p q) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) Z (1 : FockH1Action.Mat r s) (a, b) (a', b') ≠ 0) :
    Z a a' ≠ 0 ∧ b = b' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with hb
  · exact ⟨by simpa using h, hb⟩
  · simp at h

theorem kroneckerMap_one_left_ne_zero {p q r s : ℕ} (Z : FockH1Action.Mat r s) {a a' : FockH1Action.Ix p q} {b b' : FockH1Action.Ix r s}
    (h : Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : FockH1Action.Mat p q) Z (a, b) (a', b') ≠ 0) :
    Z b b' ≠ 0 ∧ a = a' := by
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at h
  split_ifs at h with ha
  · exact ⟨by simpa using h, ha⟩
  · simp at h

theorem kroneckerProperties : MatStep := by
  intro p q r s
  refine ⟨fockAct1_eq p q r s, fockAct2_eq p q r s, ?_, ?_, ?_, ?_,
    conjR_isPC, conjR_isPC, ?_, ?_⟩
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    have hs : FockH1Action.sameBlock a a' := by
      by_contra hn
      exact hz (hZ a a' hn)
    exact (linePos_left a a' b).2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    have hs : FockH1Action.sameBlock b b' := by
      by_contra hn
      exact hz (hZ b b' hn)
    exact (linePos_right a b b').2 hs
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_right_ne_zero Z h
    exact hz (hZ a a' ((linePos_left a a' b).1 heq))
  · rintro Z hZ ⟨a, b⟩ ⟨a', b'⟩ h heq
    obtain ⟨hz, rfl⟩ := kroneckerMap_one_left_ne_zero Z h
    exact hz (hZ b b' ((linePos_right a b b').1 heq))
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hb : b = b'
    · subst hb
      have hn : ¬ FockH1Action.sameBlock a' a := fun hs => by
        have := (linePos_left a a' b).2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have hb' : ¬ b' = b := fun e => hb e.symm
      simp [hb, hb']
  · rintro Z ⟨a, b⟩ ⟨a', b'⟩ h1 h2
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases ha : a = a'
    · subst ha
      have hn : ¬ FockH1Action.sameBlock b' b := fun hs => by
        have := (linePos_right a b b').2 (sameBlock_symm hs)
        rw [h1, h2] at this
        simp at this
      simp [conjR_apply_of_not Z hn]
    · have ha' : ¬ a' = a := fun e => ha e.symm
      simp [ha, ha']

end FockRL
end
end

