module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PVdmSplit
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.vdmSplit_of :
    PairSplit → VdmSplit := by
  intro h R _ n g i
  have key := h R n (fun a b => g a - g b) i
  have h1 : ∀ k ∈ univ.erase i, (if k < i then g k - g i else g i - g k) =
      (if k < i then (-1 : R) else 1) * (g i - g k) := by
    intro k _
    split_ifs <;> ring
  have h2 : ∏ k ∈ univ.erase i, (if k < i then (-1 : R) else 1) = (-1) ^ (i : ℕ) := by
    have hf : (univ.erase i).filter (· < i) = Finset.Iio i := by
      ext k
      simp only [mem_filter, mem_erase, mem_univ, and_true, mem_Iio]
      exact ⟨fun hk => hk.2, fun hk => ⟨ne_of_lt hk, hk⟩⟩
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, hf, Fin.card_Iio]
  unfold vdm vdmAway
  rw [key, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, h2]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurDetOf
section
open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

private lemma vdm_X_ne (n : ℕ) : vdm (X : Fin n → MvPolynomial (Fin n) ℚ) ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (MvPolynomial.X_injective.ne (Finset.mem_Ioi.1 hj).ne)

private lemma aeval_sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ)
    (g : Fin n → R) :
    aeval g (sch lam (X : Fin n → MvPolynomial (Fin n) ℚ)) = sch lam g := by
  unfold sch
  rw [MvPolynomial.aeval_X_left_apply]

private lemma altn_zero {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) :
    altn (shift fun _ => 0) g = vdm g := by
  have h := GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_staircase_eq_vandermondeOf g
  have h' : vdm g = GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf g := rfl
  unfold altn
  rw [h']
  simpa [shift] using h

private lemma altn_add {R : Type} [CommRing R] {n : ℕ} (lam : Fin n → ℕ) (m : ℕ) (g : Fin n → R) :
    altn (shift fun i => lam i + m) g = (∏ k, g k) ^ m * altn (shift lam) g := by
  unfold altn
  have h : (Matrix.of fun i j : Fin n => g j ^ (shift (fun i => lam i + m)) i) =
      Matrix.of fun i j : Fin n =>
        g j ^ m * (Matrix.of fun i j : Fin n => g j ^ (shift lam) i) i j := by
    ext i j
    simp only [Matrix.of_apply, shift]
    rw [← pow_add]
    congr 1
    omega
  rw [h, Matrix.det_mul_row, Finset.prod_pow]

private lemma sch_zero_X (tie : Comparison₂) (n : ℕ) :
    sch (fun _ => 0) (X : Fin n → MvPolynomial (Fin n) ℚ) = 1 := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun _ => 0) X
  rw [altn_zero] at h
  exact mul_right_cancel₀ (vdm_X_ne n) (h.trans (one_mul _).symm)

private lemma sch_add_X (tie : Comparison₂) (n : ℕ) (lam : Fin n → ℕ) (m : ℕ) :
    sch (fun i => lam i + m) (X : Fin n → MvPolynomial (Fin n) ℚ) =
      (∏ k, (X k : MvPolynomial (Fin n) ℚ)) ^ m * sch lam X := by
  have h := tie (MvPolynomial (Fin n) ℚ) n (fun i => lam i + m) X
  rw [altn_add, ← tie (MvPolynomial (Fin n) ℚ) n lam X, ← mul_assoc] at h
  exact mul_right_cancel₀ (vdm_X_ne n) h

theorem schurDet_of :
    Comparison₂ → SchurDet := by
  intro tie R _ _ n g
  refine ⟨?_, fun lam m => ?_⟩
  · rw [← aeval_sch, sch_zero_X tie, map_one]
  · rw [← aeval_sch, sch_add_X tie, map_mul, map_pow, map_prod, aeval_sch]
    simp only [aeval_X]

end UpperTheory.Gal.Schur
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYClrOf
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYClr_of : Comparison₂ → MixDet → SchurYClr ∧ SchurYOffClr := by
  intro hT hM
  constructor
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun a => y ^ shift lam a) (fun _ => 1)
    simp only [Matrix.of_apply, prod_const_one, mul_one] at h
    calc ∑ i, altn (shift lam) (scaleAt y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then y ^ shift lam a else 1) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleAt]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring
  · intro R _ _ n lam g y
    simp only [hT R]
    have h := hM R n (Matrix.of fun a j => g j ^ shift lam a) (fun _ => 1) (fun a => y ^ shift lam a)
    simp only [Matrix.of_apply, one_mul, prod_pow_eq_pow_sum] at h
    calc ∑ i, altn (shift lam) (scaleOff y i g)
        = ∑ i, (Matrix.of fun a j => (if j = i then 1 else y ^ shift lam a) * g j ^ shift lam a).det := by
          refine sum_congr rfl fun i _ => ?_
          unfold altn
          congr 1
          ext a j
          simp only [Matrix.of_apply, scaleOff]
          split_ifs <;> simp [mul_pow]
      _ = _ := by
          rw [h]
          simp only [altn, shift]
          ring

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOf
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.schurY_of :
    SchurYClr → VdmSplit → SchurY := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  have hScale : ∀ i, vdm (scaleAt y i g) =
      (-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [hSplit R n (scaleAt y i g) i]
    congr 1
    · congr 1
      unfold vdmAway
      refine Finset.prod_congr rfl fun a ha => Finset.prod_congr rfl fun b hb => ?_
      have ha' : a ≠ i := Finset.ne_of_mem_erase ha
      have hb' : b ≠ i := Finset.ne_of_mem_erase hb
      simp [scaleAt, ha', hb']
    · refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := Finset.ne_of_mem_erase hk
      simp [scaleAt, hk']
  have key : ∀ i, (∏ k ∈ univ.erase i, (g k - y * g i) * Ring.inverse (g k - g i)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (y * g i - g k) := by
    intro i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [show g i - g k = -(g k - g i) by ring, mul_neg, mul_assoc,
      Ring.inverse_mul_cancel _ (hu i k hki), mul_one]
    ring
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) * vdm g =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ))) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hScale i, hSplit R n g i, ← key i]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffOf
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem schurYOff_of : OffClrRed → VdmSplit → SchurYOff := by
  intro hOff hSplit R _ _ n lam g y hu
  have hv : IsUnit (vdm g) := by
    unfold vdm
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : i < j := by simpa using hj
    simpa using (hu i j (ne_of_gt hij)).neg
  apply hv.mul_right_cancel
  have hR : sch lam g * (∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))) * vdm g =
      sch lam g * vdm g * ∑ i, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by ring
  rw [hR, ← hOff R n lam g y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hSplit R n g i]
  have key : (∏ k ∈ univ.erase i, (g i - y * g k) * Ring.inverse (g i - g k)) *
      ∏ k ∈ univ.erase i, (g i - g k) = ∏ k ∈ univ.erase i, (g i - y * g k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [mul_assoc, Ring.inverse_mul_cancel _ (by simpa using (hu i k hki).neg), mul_one]
  rw [← key]
  ring

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Vdm
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.tie :
    Comparison₂ := by
  intro R _ _ n lam g
  have h := congrArg (aeval g) (GroundTheory.Heights₂.Heights.RestTerms.Schur.det_pow_add_staircase_eq lam)
  rw [AlgHom.map_det, map_mul] at h
  have hM : ((Matrix.of fun i j => (X j : MvPolynomial (Fin n) ℚ) ^ (lam i + (n - 1 - (i : ℕ)))).map
      (aeval g)) = Matrix.of fun i j => g j ^ (lam i + (n - 1 - (i : ℕ))) := by
    ext i j
    simp
  simp [AlgHom.mapMatrix_apply, GroundTheory.Heights₂.Heights.RestTerms.vandermondeOf, map_prod, hM] at h
  simpa [sch, vdm, altn, shift] using h.symm
end

