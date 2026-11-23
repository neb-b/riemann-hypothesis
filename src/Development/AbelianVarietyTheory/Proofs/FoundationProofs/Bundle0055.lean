module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashOldformLevelRaisingMatrix
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wConjMat (N l a b p q t s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![l * b * p + a * b * (N * l * t) - N * l * q - N * a * s, -a * p - a ^ 2 * N * t + l * q + a * s;
    N * l * (b * p + l * b ^ 2 * t - N * q - b * s), -N * a * p - a * b * (N * l * t) + N * l * q + l * b * s]

lemma wConjMat_det (N l a b p q t s : ℤ) (hab : l * b - N * a = 1) (hd : p * s - q * (N * l * t) = 1) :
    (wConjMat N l a b p q t s).det = 1 := by
  rw [wConjMat, Matrix.det_fin_two_of]
  linear_combination (l * b - N * a) ^ 2 * hd + (l * b - N * a + 1) * hab

lemma wOld_mul_eq (N l : ℕ) (a b p q t s : ℤ) (hab : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * !![p, q; (N : ℤ) * l * t, s] = wConjMat N l a b p q t s * wOld N l a b := by
  rw [wOld, wConjMat, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-((l : ℤ) * p + a * (N * l * t))) * hab
  · linear_combination (-((l : ℤ) * q + a * s)) * hab
  · linear_combination (-((N : ℤ) * l * p + l * b * (N * l * t))) * hab
  · linear_combination (-((N : ℤ) * l * q + l * b * s)) * hab

theorem chiInv_slash_wOld : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 →
    ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G →
      ChiInv k N (N * l) χ (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b hab χ G hl hG γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have ht' : mat γ 1 0 = (N : ℤ) * l * t := by rw [← Nat.cast_mul]; exact ht
  have hm : mat γ = !![mat γ 0 0, mat γ 0 1; (N : ℤ) * l * t, mat γ 1 1] := by
    rw [← ht']; exact Matrix.eta_fin_two _
  have hd : mat γ 0 0 * mat γ 1 1 - mat γ 0 1 * ((N : ℤ) * l * t) = 1 := by
    rw [← ht', ← Matrix.det_fin_two]; exact γ.2
  let δ : SL(2, ℤ) := ⟨wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1),
    wConjMat_det _ _ _ _ _ _ _ _ hab hd⟩
  have hδ : mat δ = wConjMat N l a b (mat γ 0 0) (mat γ 0 1) t (mat γ 1 1) := rfl
  have key : wOld N l a b * mat γ = mat δ * wOld N l a b := by
    rw [hδ, ← wOld_mul_eq N l a b _ _ t _ hab, ← hm]
  have hW : 0 < (wOld N l a b).det := by
    have : (wOld N l a b).det = l := by
      rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * hab
    rw [this]; exact_mod_cast hl
  have h1 : ∀ x : SL(2, ℤ), (mat x).det ≠ 0 := fun x => by simp [mat]
  have hδ0 : δ ∈ Gamma0 (N * l) := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine ⟨b * mat γ 0 0 + l * b ^ 2 * t - N * mat γ 0 1 - b * mat γ 1 1, ?_⟩
    rw [Nat.cast_mul]; rfl
  have h11 : ((mat δ 1 1 : ℤ) : ZMod N) = ((mat γ 1 1 : ℤ) : ZMod N) := by
    have : mat δ 1 1 = mat γ 1 1 +
        N * (-a * mat γ 0 0 - a * b * l * t + l * mat γ 0 1 + a * mat γ 1 1) := by
      have e : mat δ 1 1 = -(N : ℤ) * a * mat γ 0 0 - a * b * (N * l * t) + N * l * mat γ 0 1 +
        l * b * mat γ 1 1 := rfl
      rw [e]; linear_combination (mat γ 1 1) * hab
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [slash_SL_eq, ← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (h1 γ), key,
    toGL_mul _ _ (h1 δ) hW.ne', SlashAction.slash_mul, ← slash_SL_eq, hG δ hδ0,
    smul_slash_toGL k _ hW, h11]

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlash
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem norm_eval_smul_mul_im_rpow : ∀ (w : ℕ) (σ : SL(2, ℤ)) (P : ℂ[X]) (τ : ℍ), P ∈ degreeLT ℂ (w + 1) → ‖P.eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-(w : ℝ) / 2) = ‖(slP w (mat σ) P).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
  intro w σ P τ hP
  have hden : denom σ τ = ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hj : ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ _
  have hc : ((σ • τ : ℍ) : ℂ) = (((mat σ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 0 1 : ℤ) : ℂ)) /
      (((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ)) := by
    rw [specialLinearGroup_apply]
    simp
  have him := ModularGroup.im_smul_eq_div_normSq σ τ
  rw [hden] at him
  rw [eval_polySlash w (mat σ) P τ hP hj, ← hc, him]
  set j := ((mat σ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((mat σ 1 1 : ℤ) : ℂ) with hjdef
  have hn : 0 < ‖j‖ := norm_pos_iff.2 hj
  have hτ : 0 < τ.im := τ.im_pos
  rw [Complex.normSq_eq_norm_sq, Real.div_rpow hτ.le (by positivity), norm_mul, norm_pow]
  have h2 : (‖j‖ ^ 2) ^ (-(w : ℝ) / 2) = (‖j‖ ^ w)⁻¹ := by
    rw [← Real.rpow_natCast ‖j‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖j‖ w,
      ← Real.rpow_neg hn.le]
    congr 1
    push_cast
    ring
  rw [h2, div_inv_eq_mul]
  ring

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelEqZeroIffLattice
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.ThZero

lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

lemma ee_ne (a : ℂ) : ee a ≠ 0 := Complex.exp_ne_zero _

lemma ee_neg (a : ℂ) : ee (-a) = (ee a)⁻¹ := by
  simp only [ee, mul_neg, Complex.exp_neg]

lemma ee_pow (a : ℂ) (n : ℕ) : ee a ^ n = ee ((n : ℂ) * a) := by
  simp only [ee]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma ee_eq_one_iff (a : ℂ) : ee a = 1 ↔ ∃ k : ℤ, a = k := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [ee, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · apply mul_left_cancel₀ h
    rw [hk]; ring
  · rw [hk]; ring

lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  simp only [ee, Complex.norm_exp]
  rw [Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

lemma summable_nine_pow_mul_inv_sq_succ (τ : ℍ) (c : ℂ) : Summable fun n : ℕ => ‖-(ee (τ : ℂ) ^ (n + 1) * c)‖ := by
  have h := summable_geometric_of_lt_one (norm_nonneg _) (norm_ee_lt_one τ)
  refine (h.mul_right (‖ee (τ : ℂ)‖ * ‖c‖)).congr fun n => ?_
  simp only [norm_neg, norm_mul, norm_pow, pow_succ]
  ring

lemma tprod_ne (τ : ℍ) (a b : ℂ) (ha : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * a ≠ 0)
    (hb : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * b ≠ 0) :
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * a) * (1 - ee (τ : ℂ) ^ (n + 1) * b) ≠ 0 := by
  simp only [sub_eq_add_neg] at ha hb ⊢
  rw [(multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ a)).tprod_mul
    (multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ b))]
  exact mul_ne_zero (tprod_one_add_ne_zero_of_summable ha (summable_nine_pow_mul_inv_sq_succ τ a))
    (tprod_one_add_ne_zero_of_summable hb (summable_nine_pow_mul_inv_sq_succ τ b))

lemma first_iff (z : ℂ) : ee (z / 2) - ee (-z / 2) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [← ee_eq_one_iff, sub_eq_zero]
  have h1 : ee z = ee (z / 2) * ee (z / 2) := by rw [← ee_add]; congr 1; ring
  have h2 : ee (-z / 2) = (ee (z / 2))⁻¹ := by rw [← ee_neg]; congr 1; ring
  rw [h1, h2]
  have h3 := ee_ne (z / 2)
  constructor
  · intro h
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ h3
  · intro h
    exact eq_inv_of_mul_eq_one_left h

lemma fac_iff (τ : ℍ) (w : ℂ) (n : ℕ) :
    1 - ee (τ : ℂ) ^ (n + 1) * ee w = 0 ↔ ∃ k : ℤ, ((n : ℂ) + 1) * τ + w = k := by
  rw [ee_pow, ← ee_add, sub_eq_zero, eq_comm, ee_eq_one_iff]
  push_cast
  rfl

theorem th_eq_zero_iff :
    ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  intro τ z
  unfold th
  constructor
  · intro h
    by_contra hne
    refine (mul_ne_zero (mul_ne_zero (ee_ne _) ?_) (tprod_ne τ _ _ ?_ ?_)) h
    · rw [Ne, first_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨0, k, by simp [hk]⟩
    · intro n
      rw [Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨-((n : ℤ) + 1), k, by push_cast; linear_combination hk⟩
    · intro n
      rw [← ee_neg, Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨(n : ℤ) + 1, -k, by push_cast; linear_combination -hk⟩
  · rintro ⟨m, k, hz⟩
    rcases lt_trichotomy m 0 with hm | hm | hm
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * ee z = 0 :=
        (fac_iff τ z n).2 ⟨k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, zero_mul]⟩, mul_zero]
    · have : ee (z / 2) - ee (-z / 2) = 0 := (first_iff z).2 ⟨k, by simp [hz, hm]⟩
      rw [this, mul_zero, zero_mul]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹ = 0 := by
        rw [← ee_neg]
        exact (fac_iff τ (-z) n).2 ⟨-k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, mul_zero]⟩, mul_zero]

end GlobalTheory.ThZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypus
section
noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

def wSqOld (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : SL(2, ℤ) :=
  ⟨!![(l : ℤ) + a * N, a * (1 + b); (N : ℤ) * l * (1 + b), (N : ℤ) * a + l * b ^ 2], by
    rw [Matrix.det_fin_two_of]; linear_combination ((l : ℤ) * b - N * a + 1) * h⟩

lemma oldformLevelRaisingMatrix_det_eq_level (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma atkin_lehner_square_mul (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wOld N l a b * wOld N l a b = (l : ℤ) • mat (wSqOld N l a b h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wOld, wSqOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wSqOld_mem (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    wSqOld N l a b h ∈ Gamma0 (N * l) := by
  rw [Gamma0_mem]
  have : ((((wSqOld N l a b h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) = ((N * l : ℕ) : ℤ) * (1 + b) := by
    simp [wSqOld]
  rw [this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

lemma wSqOld_entry (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) :
    ((mat (wSqOld N l a b h) 1 1 : ℤ) : ZMod N) = (b : ZMod N) := by
  have e : mat (wSqOld N l a b h) 1 1 = b + (N : ℤ) * (a * (1 + b)) := by
    simp [wSqOld, mat]; linear_combination b * h
  rw [e]; push_cast; simp

theorem wOld_slash_slash (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (χ : DirichletCharacter ℂ N)
    (G : ℍ → ℂ) (hl : 0 < l) (hG : ChiInv k N (N * l) χ G) :
    (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  have hd : (wOld N l a b).det ≠ 0 := by rw [oldformLevelRaisingMatrix_det_eq_level N l a b h]; exact_mod_cast hl.ne'
  have hM : 0 < (mat (wSqOld N l a b h)).det := by simp [mat]
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hd hd, atkin_lehner_square_mul N l a b h, slash_toGL_smul k l hl _ hM,
    ← slash_SL_eq, hG _ (wSqOld_mem N l a b h), wSqOld_entry, smul_smul]

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformTraceToGammaOneEqHeckeUlLevelRaising
section
noncomputable section

open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.HeckeFamilyMatrices

lemma wOld_mul_ulFam (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (j : ℕ) :
    wOld N l a b * !![1, (j : ℤ); 0, (l : ℤ)] = (l : ℤ) • mat (gaOld N l a b h j) := by
  ext i m
  fin_cases i <;> fin_cases m <;>
    simp [wOld, gaOld, mat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma wOld_det (N l : ℕ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) : (wOld N l a b).det = l := by
  rw [wOld, Matrix.det_fin_two_of]; linear_combination (l : ℤ) * h

lemma mat_det_pos (γ : SL(2, ℤ)) : 0 < (mat γ).det := by simp [mat]

theorem trOld_eq : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ) (h : (l : ℤ) * b - N * a = 1) (G : ℍ → ℂ), 0 < l →
    trOld k N l a b h G = G + ((l : ℂ) ^ (2 - k)) • UlF k l (G ∣[k] toGL (wOld N l a b)) := by
  intro N l k a b h G hl
  have hW : 0 < (wOld N l a b).det := by rw [wOld_det N l a b h]; exact_mod_cast hl
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  unfold trOld
  congr 1
  rw [UlF, hkF, Finset.smul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, ← toGL_mul _ _ hW.ne' (ulFam_det l hl j).ne']
  have e : wOld N l a b * ulFam l j = (l : ℤ) • mat (gaOld N l a b h j) := wOld_mul_ulFam N l a b h j
  rw [e, slash_toGL_smul k l hl _ (mat_det_pos _), smul_smul, ← zpow_add₀ hl', slash_SL_eq]
  simp

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitary
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma petersson_smul_of_mem {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f g : CuspForm Γ k) {h : SL(2, ℤ)}
    (hh : h ∈ Γ) (τ : ℍ) : petersson k ⇑f ⇑g (h • τ) = petersson k ⇑f ⇑g τ := by
  have hf : (⇑f ∣[k] h) = ⇑f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn f _ ⟨h, hh, rfl⟩
  have hg : (⇑g ∣[k] h) = ⇑g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantForm.slash_action_eqn g _ ⟨h, hh, rfl⟩
  rw [← petersson_slash_SL, hf, hg]

def cosetShift (Γ : Subgroup SL(2, ℤ)) (σ : SL(2, ℤ))
    (h₁ : ∀ γ ∈ Γ, σ * γ * σ⁻¹ ∈ Γ) (h₂ : ∀ γ ∈ Γ, σ⁻¹ * γ * σ ∈ Γ) :
    SL(2, ℤ) ⧸ Γ ≃ SL(2, ℤ) ⧸ Γ where
  toFun := Quotient.map' (· * σ⁻¹) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₁ _ hab
  invFun := Quotient.map' (· * σ) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa [mul_assoc] using h₂ _ hab
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

theorem pet_dia_dia : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) =
        GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  intro N l k d σ _ _ hσ f g
  have h₁ : ∀ γ ∈ lev N l, σ * γ * σ⁻¹ ∈ lev N l := fun γ hγ => _root_.GlobalTheory.Hk.isDia_conj_mem_lev N l d σ γ hσ hγ
  have hσ' : IsDia N l (σ 0 0) σ⁻¹ := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl, hσ.1]
    · simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  have h₂ : ∀ γ ∈ lev N l, σ⁻¹ * γ * σ ∈ lev N l := fun γ hγ => by
    simpa using _root_.GlobalTheory.Hk.isDia_conj_mem_lev N l _ σ⁻¹ γ hσ' hγ
  set e := cosetShift (lev N l) σ h₁ h₂
  unfold pet
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun γ => ?_
  congr 1
  funext z
  have he : e γ = QuotientGroup.mk (γ.out * σ⁻¹) := by
    conv_lhs => rw [← QuotientGroup.out_eq' γ]
    rfl
  have hx : (QuotientGroup.mk (e γ).out : SL(2, ℤ) ⧸ lev N l) = QuotientGroup.mk (γ.out * σ⁻¹) := by
    rw [QuotientGroup.out_eq', he]
  have hmem := QuotientGroup.eq.mp hx.symm
  have hinv : (e γ).out⁻¹ = ((γ.out * σ⁻¹)⁻¹ * (e γ).out)⁻¹ * (σ * γ.out⁻¹) := by group
  rw [hinv, mul_smul, petersson_smul_of_mem f g (inv_mem hmem), dia, dia, petersson_slash_SL,
    mul_smul]

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceTUnitSetEqFourPieceTRaw
section
noncomputable section

open Finset
open scoped Classical
open GlobalTheory.KummerEisensteinGalois GlobalTheory.KummerEisensteinGalois.Smoothing

namespace GlobalTheory.TameSmoothing

variable {K : Type*} [Field K] [CharZero K]

theorem modEq_scale_tame {N q : ℕ} [NeZero q] (e : ℤ) (y : ZMod q) (s : ℤ) :
    e * ((N : ℤ) * y.val + (q : ℤ) * s) ≡ (N : ℤ) * ((e : ZMod q) * y).val + (q : ℤ) * (e * s)
      [ZMOD ((N * q : ℕ) : ℤ)] := by
  have h : ((e * (y.val : ℤ) : ℤ) : ZMod q) = (((((e : ZMod q) * y).val : ℕ) : ℤ) : ZMod q) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp h
  rw [Int.modEq_iff_dvd]
  exact ⟨w, by push_cast; linear_combination (N : ℤ) * hw⟩

theorem eisF_scale_tame {j N p n : ℕ} [NeZero p] (hN : 0 < N) {ζ : K} (hζ : ζ ^ (N * p ^ n) = 1) (e : ℤ)
    (γ δ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (w : ℤ × ℤ)
    (h : ∀ l, (δ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l =
      (e : ZMod (p ^ n)) * (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i l) :
    eisF j (N * p ^ n) ζ (e * (rowT N p n γ i w).1) (e * (rowT N p n γ i w).2) =
      eisF j (N * p ^ n) ζ (rowT N p n δ i (e * w.1, e * w.2)).1 (rowT N p n δ i (e * w.1, e * w.2)).2 := by
  have hM : 0 < N * p ^ n := Nat.mul_pos hN (Nat.pos_of_ne_zero (NeZero.ne _))
  refine eisF_congr_mod hM hζ ?_ ?_
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0) w.1
    simpa only [rowT, h, Nat.cast_pow] using this
  · have := modEq_scale_tame (N := N) e ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1) w.2
    simpa only [rowT, h, Nat.cast_pow] using this

theorem sum_scaled_tame (p : ℕ) [hp : Fact p.Prime] (N n m k : ℕ) (ψ : DirichletCharacter K (p ^ m))
    (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K) (hζ : IsPrimitiveRoot ζ (N * p ^ n)) (hN : 0 < N) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hpc : ¬ (p : ℤ) ∣ c) (hpd : ¬ (p : ℤ) ∣ d) (r : ℕ) :
    ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (c * (rowT N p n γ 0 w).1) (c * (rowT N p n γ 0 w).2))
           (eisF 1 (N * p ^ n) ζ (d * (rowT N p n γ 1 w').1) (d * (rowT N p n γ 1 w').2)) r =
    ψ⁻¹ (c : ZMod (p ^ m)) * ψ⁻¹ (d : ZMod (p ^ m)) *
      ∑ γ ∈ unitSet p n, ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (eisF (k - 1) (N * p ^ n) ζ (rowT N p n γ 0 (c * w.1, c * w.2)).1 (rowT N p n γ 0 (c * w.1, c * w.2)).2)
           (eisF 1 (N * p ^ n) ζ (rowT N p n γ 1 (d * w'.1, d * w'.2)).1
             (rowT N p n γ 1 (d * w'.1, d * w'.2)).2) r := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have huc : IsUnit (c : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpc
  have hud : IsUnit (d : ZMod (p ^ n)) := isUnit_intCast_of_not_dvd hpd
  have hψ : ∀ e : ℤ, ¬ (p : ℤ) ∣ e → ψ⁻¹ (e : ZMod (p ^ m)) * ψ (e : ZMod (p ^ m)) = 1 := by
    intro e he
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_intCast_of_not_dvd he)]
  have hcast : ∀ y : ZMod (p ^ n), ((y.val : ℕ) : ZMod (p ^ m)) =
      ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)) y := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun γ => diagGL huc.unit hud.unit * γ)
    (fun γ => (diagGL huc.unit hud.unit)⁻¹ * γ) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    exact (diagGL_mul_mem hn _ _ γ).mpr hγ
  · intro γ hγ
    refine (diagGL_mul_mem hn huc.unit hud.unit _).mp ?_
    rwa [mul_inv_cancel_left]
  · intro γ _
    exact inv_mul_cancel_left _ _
  · intro γ _
    exact mul_inv_cancel_left _ _
  · intro γ _
    rw [eisF_scale_tame hN hζ.pow_eq_one c γ (diagGL huc.unit hud.unit * γ) 0 w
        (fun l => diagGL_mul_zero _ _ _ l),
      eisF_scale_tame hN hζ.pow_eq_one d γ (diagGL huc.unit hud.unit * γ) 1 w'
        (fun l => diagGL_mul_one _ _ _ l),
      diagGL_mul_det, hcast, hcast, IsUnit.unit_spec, IsUnit.unit_spec,
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_mul (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))),
      map_intCast (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m))), map_mul ψ, map_mul ψ]
    have h1 := hψ c hpc
    have h2 := hψ d hpd
    generalize ψ⁻¹ (c : ZMod (p ^ m)) = A at h1 ⊢
    generalize ψ⁻¹ (d : ZMod (p ^ m)) = B at h2 ⊢
    generalize ψ (c : ZMod (p ^ m)) = A' at h1 ⊢
    generalize ψ (d : ZMod (p ^ m)) = B' at h2 ⊢
    generalize cmul (K := K) _ _ r = T
    generalize ψ (ZMod.castHom _ _ _) = S
    linear_combination (-(S * T)) * h1 - (A * A' * S * T) * h2

theorem pieceT_unitSet_eq_four_pieceTRaw :
    ∀ (p : ℕ) [Fact p.Prime] (N n m k : ℕ) (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) (w w' : ℤ × ℤ) (ζ : K), IsPrimitiveRoot ζ (N * p ^ n) → 0 < N → ¬ p ∣ N → 1 ≤ m → m ≤ n → 3 ≤ k → ¬ (p : ℤ) ∣ c → ¬ (p : ℤ) ∣ d → ∀ r : ℕ, pieceT N p n m k ψ c d w w' ζ (unitSet p n) r = (c : K) ^ 2 * (d : K) ^ 2 * pieceTRaw N p n m k ψ w w' ζ (unitSet p n) r - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * pieceTRaw N p n m k ψ (c * w.1, c * w.2) w' ζ (unitSet p n) r - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ w (d * w'.1, d * w'.2) ζ (unitSet p n) r + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * pieceTRaw N p n m k ψ (c * w.1, c * w.2) (d * w'.1, d * w'.2) ζ (unitSet p n) r := by
  intro p hp N n m k K _ _ ψ c d w w' ζ hζ hN _ hm hmn hk hpc hpd r
  have hp1 : ¬ (p : ℤ) ∣ 1 := (Nat.prime_iff_prime_int.mp hp.out).not_dvd_one
  have h2 := sum_scaled_tame p N n m k ψ 1 d w w' ζ hζ hN hm hmn hp1 hpd r
  have h3 := sum_scaled_tame p N n m k ψ c 1 w w' ζ hζ hN hm hmn hpc hp1 r
  have h4 := sum_scaled_tame p N n m k ψ c d w w' ζ hζ hN hm hmn hpc hpd r
  simp only [one_mul, Int.cast_one, map_one, mul_one, Prod.mk.eta] at h2 h3
  have e1 : (2 : ℤ) - ((k - 1 : ℕ) : ℤ) = 3 - k := by omega
  have e2 : (2 : ℤ) - ((1 : ℕ) : ℤ) = 1 := by norm_num
  have hs : ∀ (e : ℤ) (j M : ℕ) (a b : ℤ), smF e j M ζ a b =
      fun i => (e : K) ^ 2 * eisF j M ζ a b i - (e : K) ^ ((2 : ℤ) - j) * eisF j M ζ (e * a) (e * b) i :=
    fun _ _ _ _ _ => rfl
  unfold pieceT pieceTRaw
  simp only [hs, cmul_expand, e1, e2, zpow_one, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  simp only [mul_left_comm (ψ _), ← Finset.mul_sum]
  rw [h2, h3, h4]
  ring

end GlobalTheory.TameSmoothing
end
end

