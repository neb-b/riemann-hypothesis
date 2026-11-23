module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0029
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0031
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0032
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormSqrtNegPowPrimeSqSub
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0026
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0021
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0028

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.EndIntegral
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

theorem end_not_dvd (d : ℕ) (hd : d % 4 = 3) (l : ℕ) [Fact l.Prime]
    (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l)) : ¬ l ∣ (d + 1) / 4 := by
  intro h
  apply hin
  refine ⟨1, ?_⟩
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h0 : ((d + 1 : ℕ) : ZMod l) = 0 := by
    rw [← h4, ZMod.natCast_eq_zero_iff]
    exact Dvd.dvd.mul_left h 4
  push_cast at h0
  linear_combination h0

theorem end_unit (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : ¬ l ∣ n) (a : ℂ_[l]) (ha : ‖a‖ ≤ 1)
    (hq : a ^ 2 - a + (n : ℂ_[l]) = 0) : ‖a‖ = 1 := by
  have hnn : ‖(n : ℂ_[l])‖ = 1 := by
    simpa using kq_int_unit l (n : ℤ) (by exact_mod_cast hn)
  have hprod : a * (1 - a) = n := by linear_combination -hq
  have hb : ‖1 - a‖ ≤ 1 := by
    have e : 1 - a = 1 + -a := by ring
    rw [e]
    exact kq_add_le l _ _ 1 (by simp) (by rwa [norm_neg])
  refine le_antisymm ha ?_
  rw [← hnn, ← hprod, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

theorem end_card (d : ℕ) (hd : d % 4 = 3) (L : PeriodPair) (hCM : HasCMBy d L) (S : Finset ℂ)
    (h0 : omegaK d ≠ 0) (hS : Formalism.L2.Th1.F.IsKerReps L (omegaK d) S) :
    S.card + 1 = (d + 1) / 4 := by
  have h1 := Formalism.L2.Th1.F.kerRepsCard L (omegaK d) S h0 hCM hS
  have h2 := (Formalism.L2.Th1.F.hasCMByStable d L hCM 0 1).2
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  have h4' : (4 : ℝ) * (((d + 1) / 4 : ℕ) : ℝ) = (d : ℝ) + 1 := by exact_mod_cast h4
  have e : ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * omegaK d = omegaK d := by simp
  rw [e] at h2
  have h3 : ((S.card + 1 : ℕ) : ℝ) = (((d + 1) / 4 : ℕ) : ℝ) := by
    push_cast
    rw [h1, h2]
    push_cast
    linarith
  exact_mod_cast h3

theorem end_integral (d : ℕ) (L : PeriodPair) (hd : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (hl : 5 ≤ l) (hld : ¬ l ∣ d) (hin : ¬ ∃ a : ZMod l, a ^ 2 = -(d : ZMod l))
    (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    IntegralPS ((uSer g2 g3).subst (C (ι (omegaK d)) * lgS g2 g3)) := by
  obtain ⟨L', hM, hCM'⟩ := good_lattice l L ι g2 g3 hg
  have hCM1 : HasCMBy d L' := hCM' d hCM
  have hl2 : l ≠ 2 := by omega
  have hquadC := omegaK_quad d hd
  have hquad : (ι (omegaK d)) ^ 2 - ι (omegaK d) + (((d + 1) / 4 : ℕ) : ℂ_[l]) = 0 := by
    have := congrArg ι hquadC
    simpa using this
  have hln := end_not_dvd d hd l hin
  have hn0 : 0 < (d + 1) / 4 := by omega
  obtain ⟨ha1, -, -⟩ := kur_quad l d hd hl2 hld hin _ hquad
  have hau : ‖ι (omegaK d)‖ = 1 := end_unit l _ hln _ ha1 hquad
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := kq_int_unit l 2 (by
      intro h
      have h' : l ∣ 2 := by exact_mod_cast h
      exact hl2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h'))
    simpa using this
  have hα : omegaK d ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hau
    exact zero_ne_one hau
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L' (omegaK d) hα hCM1
  have hcard := end_card d hd L' hCM1 S hα hS
  obtain ⟨neg, hE⟩ := endo_curve l L' ι (omegaK d) S hα hCM1 hS
  rw [← hM.eq2, ← hM.eq3] at hE
  have htor : ∀ P : S, ‖ι (L'.weierstrassP (P : ℂ))‖ ≤ 1 ∧ ‖ι (L'.derivWeierstrassP (P : ℂ))‖ ≤ 1 := by
    intro P
    obtain ⟨hP1, hP2⟩ := hS.1 P P.2
    refine tor_integral l hl2 L' ι g2 g3 hM _ hn0 hln P ?_ hP2
    have e : (((d + 1) / 4 : ℕ) : ℂ) * (P : ℂ) = omegaK d * (P : ℂ) - omegaK d * (omegaK d * (P : ℂ)) := by
      linear_combination (P : ℂ) * hquadC
    rw [e]
    exact sub_mem hP1 (hCM1 _ hP1)
  have hc : Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[l]) (Formalism.L2.Th1.A.shortW g2 g3) :=
    shortW_intModel g2 g3 hM.n2 hM.n3 h2
  have h2R : (2 : ℂ_[l])⁻¹ ∈ unitBall ℂ_[l] := Formalism.L2.Th1.C.inv_mem_unitBall h2
  obtain ⟨hlp, hwp, hAx, -, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[l] (unitBall ℂ_[l]) _ hc
  have hDat := Formalism.L2.Th1.C.curveEndoR ℂ_[l] (unitBall ℂ_[l]) _ hc S neg _ _ (ι (omegaK d))
    (1 - ι (omegaK d)) hE (fun P => (htor P).1)
    (fun P => by
      change ‖ι (L'.derivWeierstrassP (P : ℂ)) / 2‖ ≤ 1
      rw [norm_div, h2, div_one]
      exact (htor P).2)
    (by
      rw [Fintype.card_coe]
      have : ((S.card : ℂ_[l]) + 1) = (((d + 1) / 4 : ℕ) : ℂ_[l]) := by exact_mod_cast hcard
      rw [this]
      linear_combination -hquad)
    hau.le (Formalism.L2.Th1.C.inv_mem_unitBall hau)
    (by
      have : (Formalism.L2.Th1.A.shortW g2 g3).b₂ = 0 := by
        simp [Formalism.L2.Th1.A.shortW, WeierstrassCurve.b₂]
      rw [this]
      simp)
  have hEnd := Formalism.L2.Th1.C.endIntFromDatum ℂ_[l] (unitBall ℂ_[l]) _ _ _ _ _ S neg _ _ _ _ _
    hlp hwp hAx h2R hDat
  rw [lgS_eq_logSer, Formalism.L2.Th1.A.uSerEq]
  exact hEnd

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgLevel
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem half_cubic (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hM : LatModel l L ι g2 g3) :
    4 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 3 - g2 * ι (L.weierstrassP (L.ω₁ / 2)) - g3 = 0 := by
  have hd : L.derivWeierstrassP (L.ω₁ / 2) = 0 :=
    (F.pDerivZero L _ L.ω₁_div_two_notMem_lattice).2
      (by rw [mul_div_cancel₀ _ (two_ne_zero)]; exact L.ω₁_mem_lattice)
  have h := L.derivWeierstrassP_sq _ L.ω₁_div_two_notMem_lattice
  rw [hd] at h
  have h' := congrArg ι h
  simp only [map_pow, map_mul, map_sub, map_zero, map_ofNat] at h'
  rw [hM.eq2, hM.eq3, ← h']
  norm_num

theorem half_prod_norm (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hM : LatModel l L ι g2 g3) (S : Finset ℂ) (hS : F.IsKerReps L (l : ℂ) S)
    (hκ : ‖3 * ι (L.weierstrassP (L.ω₁ / 2)) ^ 2 - g2 / 4‖ = 1) :
    ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L.weierstrassP (L.ω₁ / 2)) - ι (L.weierstrassP P)‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have h := congrArg ι (an_two L l (hlp.odd_of_ne_two hl) S hS L.ω₁ L.ω₁_mem_lattice
    L.ω₁_div_two_notMem_lattice)
  simp only [map_pow, map_mul, map_prod, map_sub, map_natCast, map_div₀, map_ofNat] at h
  rw [← hM.eq2] at h
  have hn := congrArg norm h
  rw [norm_pow, norm_pow _ (l ^ 2 - 1), hκ, one_pow, norm_mul, norm_prod] at hn
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 hn

theorem level_le (L : PeriodPair) (l : ℕ) [Fact l.Prime] (hl : 5 ≤ l) (ι : ℂ ≃+* ℂ_[l])
    (g2 g3 : ℂ_[l]) (hg : IsGoodModel l L ι g2 g3) :
    ∃ i, i ≤ l ^ 2 ∧ ‖coeff i ((uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3))‖ = 1 := by
  have hlp : l.Prime := Fact.out
  have hl2 : l ≠ 2 := by omega
  obtain ⟨L', hM, -⟩ := good_lattice l L ι g2 g3 hg
  obtain ⟨-, -, h2, h3, hΔ, -⟩ := hg
  have h22 : ‖(2 : ℂ_[l])‖ = 1 := by
    have := norm_natCast_Cl_of_not_dvd (l := l) (n := 2)
      (fun h => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 h))
    simpa using this
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  have hst : F.MulStable L' (l : ℂ) := fun ω hω => by
    have := L'.lattice.smul_mem (l : ℤ) hω
    simpa using this
  obtain ⟨S, hS⟩ := F.kerRepsExist L' (l : ℂ) hl0 hst
  have hcard : S.card + 1 = l ^ 2 := by
    have := F.kerRepsCard L' (l : ℂ) S hl0 hst hS
    rw [Complex.normSq_natCast] at this
    have h' : ((S.card + 1 : ℕ) : ℝ) = ((l ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [this]
      ring
    exact_mod_cast h'
  obtain ⟨U, hU0, hUi, hsq⟩ := sq_formula l hl2 L' ι g2 g3 hM l hlp.pos S hS
  obtain ⟨e', he'0, he'i, he'l⟩ := mulN_integral (curve_law g2 g3 h2 h3 h22) l
  have hee : e' = (uSer g2 g3).subst (C (l : ℂ_[l]) * lgS g2 g3) :=
    mult_unique g2 g3 _ e' he'0 he'l
  rw [← hee] at hsq ⊢
  obtain ⟨hAi, hA0, -⟩ :=
    A.bridgeCurve ℂ_[l] (A.shortW g2 g3) (shortW_intModel g2 g3 h2 h3 h22)
  have hAi' : IntegralPS (A.xS (A.shortW g2 g3)) := (integralPS_iff_mv _).2 hAi
  have hGi := integral_of_sq_eq he'i he'0 hUi hU0 hsq
  have hb := gauss_bound S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ hGi
  obtain ⟨he1, hκ⟩ := kap_unit g2 g3 _ h2 h3 hΔ h22 (half_cubic l L' ι g2 g3 hM)
  have hp := half_prod_norm l hl2 L' ι g2 g3 hM S hS hκ
  have hle : ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, ‖ι (L'.weierstrassP (L'.ω₁ / 2)) - ι (L'.weierstrassP P)‖
      ≤ ‖(l : ℂ_[l]) ^ 2‖ * ∏ P ∈ S, max 1 ‖ι (L'.weierstrassP P)‖ := by
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => ?_
    exact (norm_sub_le_max_Cl l _ _).trans (max_le_max he1 le_rfl)
  rw [hp] at hle
  obtain ⟨i, hi, hi1⟩ := unit_coeff_mul hUi hGi (by rw [hU0, norm_one]) _
    (gauss_unit S (fun P => ι (L'.weierstrassP P)) _ hAi' hA0 _ (le_antisymm hb hle))
  refine unit_coeff_of_sq he'i (l ^ 2) ⟨i + 2, by omega, ?_⟩
  rw [hsq, mul_assoc, coeff_X_pow_mul]
  exact hi1

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Norm1728EqOneOfFiveLe
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem valDiv2_even_of_pows {l t : ℝ} (hl : 1 < l) {a b : ℤ} {n : ℕ} (hn : ¬ 2 ∣ n)
    (h4 : t ^ 4 = l ^ b) (h1 : t ^ (2 * n) * l ^ a = 1) : ∃ m : ℤ, b = 2 * m := by
  have hl0 : l ≠ 0 := by positivity
  have e1 : l ^ (b * n + 2 * a) = 1 := by
    rw [zpow_add₀ hl0, zpow_mul, ← h4, zpow_natCast, mul_comm 2 a, zpow_mul]
    have h5 : (t ^ 4) ^ n = (t ^ (2 * n)) ^ 2 := by ring
    have h6 : (l ^ a) ^ (2 : ℤ) = (l ^ a) ^ 2 := by norm_cast
    rw [h5, h6, ← mul_pow, h1, one_pow]
  have e2 : b * n + 2 * a = 0 := (zpow_eq_one_iff_right₀ (by positivity) hl.ne').1 e1
  obtain ⟨k, hk⟩ : Odd n := Nat.not_even_iff_odd.1 (fun h => hn (even_iff_two_dvd.1 h))
  subst hk
  push_cast at e2
  exact ⟨-a - b * k, by linarith⟩

theorem norm_1728_eq_one_of_five_le (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) : ‖(1728 : ℂ_[l])‖ = 1 := by
  have hl : l.Prime := Fact.out
  have h : ¬ l ∣ 1728 := by
    intro h
    have h12 : l ∣ 12 := hl.dvd_of_dvd_pow (show l ∣ 12 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h12
    interval_cases l <;> first | omega | exact absurd hl (by norm_num)
  simpa using red_norm_natCast l h

theorem valDiv2_norm_27 (l : ℕ) [Fact l.Prime] (h5 : 5 ≤ l) : ‖(27 : ℂ_[l])‖ = 1 := by
  have hl : l.Prime := Fact.out
  have h : ¬ l ∣ 27 := by
    intro h
    have h12 : l ∣ 3 := hl.dvd_of_dvd_pow (show l ∣ 3 ^ 3 by norm_num; exact h)
    have := Nat.le_of_dvd (by norm_num) h12
    omega
  simpa using red_norm_natCast l h

theorem valDiv2 (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    [Fact l.Prime] (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (ι : ℂ ≃+* ℂ_[l]) (hJ : ι (jInv L) ∈ MaximalUnramifiedExtension l)
    (hJ1 : ‖ι (jInv L)‖ ≤ 1) (h0 : ι (jInv L) ≠ 1728) :
    ∃ m : ℤ, ‖ι (jInv L) - 1728‖ = (l : ℝ) ^ (2 * m) := by
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have n1728 := norm_1728_eq_one_of_five_le l h5
  have n27 := valDiv2_norm_27 l h5
  obtain ⟨J, hJdef⟩ : ∃ J, J = ι (jInv L) := ⟨_, rfl⟩
  rw [← hJdef] at hJ hJ1 h0 ⊢
  have hw0 : J - 1728 ≠ 0 := sub_ne_zero.2 h0
  have m1728 : (1728 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    have := natCast_mem (MaximalUnramifiedExtension l) 1728
    exact_mod_cast this
  have m27 : (27 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    have := natCast_mem (MaximalUnramifiedExtension l) 27
    exact_mod_cast this
  have hwK : J - 1728 ∈ MaximalUnramifiedExtension l := sub_mem hJ m1728
  obtain ⟨b, hb⟩ := kur_val l hwK hw0
  have hwle : ‖J - 1728‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hJ1 (by rw [norm_neg, n1728]))
  rcases hwle.eq_or_lt with h1 | hlt
  · exact ⟨0, by simpa using h1⟩
  have nJ : ‖J‖ = 1 := by
    have h : J = (J - 1728) + 1728 := by ring
    rw [h, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [n1728]; exact hlt.ne), n1728,
      max_eq_right hlt.le]
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h, norm_zero] at nJ
    exact zero_ne_one nJ
  have hj0 : jInv L ≠ 0 := fun h => hJ0 (by rw [hJdef, h, map_zero])
  have hj1 : jInv L ≠ 1728 := fun h => h0 (by rw [hJdef, h, map_ofNat])
  have h2 : L.g₂ ≠ 0 := fun h => hj0 ((jInv_eq_zero_iff L).2 h)
  have h3 : L.g₃ ≠ 0 := fun h => hj1 ((jInv_eq_iff L).2 h)
  obtain ⟨L0, hCM0, -, hg2, hg3⟩ := exists_cm_lattice_equal_invariants d L hCM h2 h3
  obtain ⟨c, hc⟩ : ∃ c : ℂ_[l], c = 27 * J / (J - 1728) := ⟨_, rfl⟩
  have ig2 : ι L0.g₂ = c := by
    rw [hg2, hc, hJdef, map_div₀, map_mul, map_sub, map_ofNat, map_ofNat]
  have ig3 : ι L0.g₃ = c := by
    rw [hg3, hc, hJdef, map_div₀, map_mul, map_sub, map_ofNat, map_ofNat]
  have mc : c ∈ MaximalUnramifiedExtension l := by
    rw [hc]
    exact div_mem (mul_mem m27 hJ) hwK
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ‖J - 1728‖ := ⟨_, rfl⟩
  rw [← hx] at hb hlt ⊢
  have hx0 : 0 < x := by rw [hx]; exact norm_pos_iff.2 hw0
  have nc : ‖c‖ = x⁻¹ := by
    rw [hc, norm_div, norm_mul, n27, nJ, ← hx]
    simp
  have iD : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = c ^ 2 * (27 * 1728 / (J - 1728)) := by
    rw [map_sub, map_mul, map_pow, map_pow, ig2, ig3, map_ofNat, hc]
    field_simp
    ring
  have nD : ‖ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2)‖ = (x⁻¹) ^ 3 := by
    rw [iD, norm_mul, norm_pow, nc, norm_div, norm_mul, n27, n1728, ← hx]
    ring
  have hD0 : ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) ≠ 0 := norm_ne_zero_iff.1 (by rw [nD]; positivity)
  obtain ⟨μ, hμ'⟩ := IsAlgClosed.exists_pow_nat_eq (ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2))⁻¹
    (n := 12) (by norm_num)
  have hμ : μ ^ 12 * ι (L0.g₂ ^ 3 - 27 * L0.g₃ ^ 2) = 1 := by
    rw [hμ']
    exact inv_mul_cancel₀ hD0
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖μ‖ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have ht12 : (t ^ 4) ^ 3 = x ^ 3 := by
    have h := congrArg norm hμ
    rw [norm_mul, norm_pow, nD, norm_one, ← ht] at h
    field_simp at h
    rw [← h]
    ring
  have ht4 : t ^ 4 = x := (pow_left_inj₀ (by positivity) hx0.le (by norm_num)).1 ht12
  have ht1 : t < 1 := by
    by_contra h
    have : 1 ≤ t ^ 4 := one_le_pow₀ (not_lt.1 h)
    linarith
  have n4 : ‖μ ^ 4 * ι L0.g₂‖ = 1 := by
    rw [ig2, norm_mul, norm_pow, nc, ← ht, ht4]
    exact mul_inv_cancel₀ hx0.ne'
  have n6 : ‖μ ^ 6 * ι L0.g₃‖ = t ^ 2 := by
    rw [ig3, norm_mul, norm_pow, nc, ← ht]
    have : t ^ 6 = x * t ^ 2 := by rw [← ht4]; ring
    rw [this]
    field_simp
  have n6lt : ‖μ ^ 6 * ι L0.g₃‖ < 1 := by
    rw [n6]
    exact pow_lt_one₀ ht0 ht1 (by norm_num)
  obtain ⟨N, T, hlN, h2N, h2T, hT, hk⟩ := kerProd d L0 hsq hd4 hCM0 l hl h5 hld 2 (Or.inl rfl)
  have hP : ι (∏ z ∈ T, L0.weierstrassP z) ∈ MaximalUnramifiedExtension l := by
    have := hk ((MaximalUnramifiedExtension l).comap (ι : ℂ →+* ℂ_[l])) (by rw [Subfield.mem_comap]; simpa [ig2] using mc)
      (by rw [Subfield.mem_comap]; simpa [ig3] using mc)
      (by rw [Subfield.mem_comap]; exact omega_mem_kur d hsq hd4 l hld ι)
    rw [Subfield.mem_comap] at this
    exact this
  have hU := unit_prod L0 l ι h5 μ hμ n4.le n6lt.le 2 N (Or.inr ⟨rfl, n6lt⟩) hlN h2N T hT
  have hP0 : ι (∏ z ∈ T, L0.weierstrassP z) ≠ 0 := by
    intro h
    rw [h, norm_zero, mul_zero] at hU
    exact zero_ne_one hU
  obtain ⟨a, ha⟩ := kur_val l hP hP0
  rw [ha, ← ht] at hU
  obtain ⟨m, hm⟩ := valDiv2_even_of_pows hl1 h2T (ht4.trans hb) hU
  exact ⟨m, by rw [hb, hm]⟩

end ReciprocityTheory.ChartRestriction.L1
end
end

