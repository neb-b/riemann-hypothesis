module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0002
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
section
noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
section
noncomputable section

namespace Formalism.L2.Th1.B.Wr

open MvPowerSeries

variable {K : Type} [Field K] [CharZero K]

private theorem hasSubst_fin_three_of_constantCoeff_eq_zero {a : Fin 3 → MvPowerSeries (Fin 3) K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  exact hasSubst_of_constantCoeff_zero ha

theorem hasSubst_restrictThirdZero : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1, 0] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero (fun s => by fin_cases s <;> simp)

theorem restrictThirdZero_eq_rescale (h : MvPowerSeries (Fin 3) K) : ev3 h = rescale ![1, 1, 0] h := by
  rw [rescale_eq_subst]
  unfold Formalism.L2.Th1.B.ev3
  congr 1
  funext s
  fin_cases s <;> simp

theorem coeff_restrictThirdZero (h : MvPowerSeries (Fin 3) K) (n : Fin 3 →₀ ℕ) (hn : n 2 = 0) :
    coeff n (ev3 h) = coeff n h := by
  rw [restrictThirdZero_eq_rescale]
  rw [coeff_rescale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [hn]

theorem restrictThirdZero_mul (f g : MvPowerSeries (Fin 3) K) : ev3 (f * g) = ev3 f * ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_mul]

theorem restrictThirdZero_add (f g : MvPowerSeries (Fin 3) K) : ev3 (f + g) = ev3 f + ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_add (f := _)]

theorem restrictThirdZero_sub (f g : MvPowerSeries (Fin 3) K) : ev3 (f - g) = ev3 f - ev3 g := by
  simp only [restrictThirdZero_eq_rescale, map_sub]

theorem restrictThirdZero_natCast (k : ℕ) : ev3 (k : MvPowerSeries (Fin 3) K) = k := by
  simp only [restrictThirdZero_eq_rescale, map_natCast]

theorem restrictThirdZero_X_two : ev3 (X 2 : MvPowerSeries (Fin 3) K) = 0 := by
  unfold Formalism.L2.Th1.B.ev3
  rw [subst_X hasSubst_restrictThirdZero]
  simp

theorem X_two_dvd_of_restrictThirdZero {h : MvPowerSeries (Fin 3) K} (h0 : ev3 h = 0) : X 2 ∣ h := by
  rw [X_dvd_iff]
  intro m hm
  rw [← coeff_restrictThirdZero h m hm, h0]
  simp

private theorem X_two_fin_three_ne_zero : (X 2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single (2 : Fin 3) 1)) h
  simp [coeff_X] at this

private theorem pderiv_X_fin_three_self (i : Fin 3) :
    MvPowerSeries.pderiv (R := K) i (X i : MvPowerSeries (Fin 3) K) = 1 := by
  simp

private theorem pderiv_two_X_two_pow_succ (m : ℕ) :
    MvPowerSeries.pderiv (R := K) 2 ((X 2 : MvPowerSeries (Fin 3) K) ^ (m + 1)) =
      ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (X 2 : MvPowerSeries (Fin 3) K) (m + 1), Derivation.leibniz, ih, pderiv_X_fin_three_self]
    simp only [smul_eq_mul]
    push_cast
    ring

private theorem pd_two_X_two_pow_succ_mul (m : ℕ) (R : MvPowerSeries (Fin 3) K) :
    Formalism.L2.Th1.B.pd 2 (X 2 ^ (m + 1) * R) =
      X 2 ^ (m + 1) * Formalism.L2.Th1.B.pd 2 R + R * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * X 2 ^ m) := by
  unfold Formalism.L2.Th1.B.pd
  rw [Derivation.leibniz, pderiv_two_X_two_pow_succ]
  simp only [smul_eq_mul]

theorem eq_zero_of_wronsk {Q B : MvPowerSeries (Fin 3) K} (hw : Q * pd 2 B = B * pd 2 Q)
    (hQ : ev3 Q = 0) (hB : ev3 B ≠ 0) : Q = 0 := by
  have key : ∀ m : ℕ, ∃ R : MvPowerSeries (Fin 3) K, Q = X 2 ^ (m + 1) * R := by
    intro m
    induction m with
    | zero =>
      obtain ⟨R, hR⟩ := X_two_dvd_of_restrictThirdZero hQ
      exact ⟨R, by rw [hR]; ring⟩
    | succ m ih =>
      obtain ⟨R, rfl⟩ := ih
      rw [pd_two_X_two_pow_succ_mul] at hw
      have h1 : X 2 ^ m * (X 2 * R * Formalism.L2.Th1.B.pd 2 B) =
          X 2 ^ m * (B * (((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) * R + X 2 * Formalism.L2.Th1.B.pd 2 R)) := by
        linear_combination hw
      have h2 := mul_left_cancel₀ (pow_ne_zero m X_two_fin_three_ne_zero) h1
      have h3 := congrArg Formalism.L2.Th1.B.ev3 h2
      simp only [restrictThirdZero_mul, restrictThirdZero_add, restrictThirdZero_X_two,
        restrictThirdZero_natCast, zero_mul, add_zero] at h3
      have hc : ((m + 1 : ℕ) : MvPowerSeries (Fin 3) K) ≠ 0 := by
        intro hc
        have := congrArg (coeff (0 : Fin 3 →₀ ℕ)) hc
        simp at this
        exact Nat.cast_add_one_ne_zero m this
      have hR : Formalism.L2.Th1.B.ev3 R = 0 := by
        rcases mul_eq_zero.mp h3.symm with h | h
        · exact absurd h hB
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h hc
          · exact h
      obtain ⟨S, hS⟩ := X_two_dvd_of_restrictThirdZero hR
      exact ⟨S, by rw [hS]; ring⟩
  ext n
  obtain ⟨R, hR⟩ := key (n 2)
  suffices hz : coeff n ((X 2 : MvPowerSeries (Fin 3) K) ^ (n 2 + 1) * R) = 0 by
    rw [hR, hz]; simp
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨p, q⟩ hpq
  have hpq' : p + q = n := by simpa using hpq
  rw [coeff_X_pow]
  split_ifs with hp
  · exfalso
    subst hp
    have := DFunLike.congr_fun hpq' 2
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · simp

theorem wronskianUniqueness : WronskLemma := by
  intro L _ _ A Bs hw hr hB
  have hQ : Formalism.L2.Th1.B.ev3 (A - Bs) = 0 := by rw [restrictThirdZero_sub, hr, sub_self]
  have hd : Formalism.L2.Th1.B.pd 2 (A - Bs) = Formalism.L2.Th1.B.pd 2 A - Formalism.L2.Th1.B.pd 2 Bs := by
    simp only [Formalism.L2.Th1.B.pd, map_sub]
  have hw' : (A - Bs) * Formalism.L2.Th1.B.pd 2 Bs = Bs * Formalism.L2.Th1.B.pd 2 (A - Bs) := by
    rw [hd]
    linear_combination hw
  exact sub_eq_zero.mp (eq_zero_of_wronsk hw' hQ hB)

def sh (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] h

def shI (h : MvPowerSeries (Fin 3) K) : MvPowerSeries (Fin 3) K :=
  subst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] h

theorem cc_sh (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

theorem cc_shI (s : Fin 3) :
    constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] s) = 0 := by
  fin_cases s <;> simp

theorem hasSubst_sh : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 - X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_sh

theorem hasSubst_shI : HasSubst ![(X 0 : MvPowerSeries (Fin 3) K), X 1 + X 2, X 2] :=
  hasSubst_fin_three_of_constantCoeff_eq_zero cc_shI

private theorem subst_fin_three_mul {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f * g) = subst a f * subst a g := by
  exact subst_mul ha f g

theorem sh_mul (f g : MvPowerSeries (Fin 3) K) : sh (f * g) = sh f * sh g := by
  unfold sh
  exact subst_fin_three_mul hasSubst_sh f g

private theorem subst_fin_three_sub {a : Fin 3 → MvPowerSeries (Fin 3) K} (ha : HasSubst a)
    (f g : MvPowerSeries (Fin 3) K) : subst a (f - g) = subst a f - subst a g := by
  exact subst_sub ha f g

theorem sh_sub (f g : MvPowerSeries (Fin 3) K) : sh (f - g) = sh f - sh g := by
  unfold sh
  exact subst_fin_three_sub hasSubst_sh f g

private theorem subst_X_fin_three_eq_self (h : MvPowerSeries (Fin 3) K) :
    subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h = h := by
  rw [← map_algebraMap_eq_subst_X]
  simp

theorem shI_sh (h : MvPowerSeries (Fin 3) K) : shI (sh h) = h := by
  unfold shI sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_shI]
  trans subst (X : Fin 3 → MvPowerSeries (Fin 3) K) h
  · congr 1
    funext s
    fin_cases s <;> simp [subst_X hasSubst_shI, subst_fin_three_sub hasSubst_shI]
  · exact subst_X_fin_three_eq_self h

theorem restrictThirdZero_shear (h : MvPowerSeries (Fin 3) K) : ev3 (sh h) = ev3 h := by
  unfold Formalism.L2.Th1.B.ev3 sh
  rw [subst_comp_subst_apply hasSubst_sh hasSubst_restrictThirdZero]
  congr 1
  funext s
  fin_cases s <;> simp [subst_X hasSubst_restrictThirdZero, subst_fin_three_sub hasSubst_restrictThirdZero]

private theorem pderiv_X_fin_three_of_ne {i j : Fin 3} (hij : j ≠ i) :
    MvPowerSeries.pderiv (R := K) i (X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp [hij]

theorem partialDeriv_two_shear (h : MvPowerSeries (Fin 3) K) : pd 2 (sh h) = sh (pd 2 h) - sh (pd 1 h) := by
  unfold sh Formalism.L2.Th1.B.pd
  rw [Formalism.G.LogCR.pderiv_subst cc_sh, Fin.sum_univ_three]
  simp [pderiv_X_fin_three_self, pderiv_X_fin_three_of_ne]
  try ring

theorem shearedWronskianUniqueness : ShearLemma := by
  intro L _ _ A Bs hw hr hB
  have h1 : sh A * Formalism.L2.Th1.B.pd 2 (sh Bs) = sh Bs * Formalism.L2.Th1.B.pd 2 (sh A) := by
    rw [partialDeriv_two_shear, partialDeriv_two_shear]
    have e := congrArg sh hw
    rw [sh_mul, sh_mul, sh_sub, sh_sub] at e
    linear_combination -e
  have h2 : Formalism.L2.Th1.B.ev3 (sh A) = Formalism.L2.Th1.B.ev3 (sh Bs) := by
    rw [restrictThirdZero_shear, restrictThirdZero_shear, hr]
  have h3 : Formalism.L2.Th1.B.ev3 (sh Bs) ≠ 0 := by
    rwa [restrictThirdZero_shear]
  have h4 := wronskianUniqueness L (sh A) (sh Bs) h1 h2 h3
  calc A = shI (sh A) := (shI_sh A).symm
    _ = shI (sh Bs) := by rw [h4]
    _ = Bs := shI_sh Bs

end Formalism.L2.Th1.B.Wr
end
end

