module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChosenDiamondMatrixLetterOperatorsCosetSums
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.DiamondOperatorFamilies

theorem isDiamondMatrixAtLevel_of_gamma1Gamma0 {N l d : ℕ} (hl : l.Prime) (hlN : ¬ l ∣ N) {γ : SL(2, ℤ)} (h : GlobalTheory.KZ.IsDiam N l d γ) :
    GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) γ := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hc : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have h0' : γ ∈ CongruenceSubgroup.Gamma0 N := h0
  have h1' : γ ∈ CongruenceSubgroup.Gamma0 l := h1
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem] at h0' h1' ⊢
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0' h1' ⊢
    push_cast
    exact IsCoprime.mul_dvd (Nat.isCoprime_iff_coprime.2 hc) h0' h1'
  · simpa [en, GlobalTheory.HeckeFamilyMatrices.mat] using h2

theorem sgD_fams : ∀ (N l : ℕ), 0 < N → l.Prime → ¬ l ∣ N → (∀ d : ℕ, Nat.Coprime d N → GlobalTheory.HeckeFamilyMatrices.IsDiam N l (d : ZMod N) (sgD N l d)) ∧ (∀ q : ℕ, opL ℂ N l (Letter.T q) = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.tqFam q (sgD N l q) i)) ∧ opL ℂ N l Letter.U = ∑ i, opP ℂ (GlobalTheory.HeckeFamilyMatrices.ulFam l i) ∧ ∀ d : ℕ, opL ℂ N l (Letter.D d) = ∑ _i : Unit, opP ℂ (GlobalTheory.HeckeFamilyMatrices.mat (sgD N l d)) := by
  intro N l hN hl hlN
  refine ⟨fun d hd => isDiamondMatrixAtLevel_of_gamma1Gamma0 hl hlN (Betti.isDiam_sgD hN.ne' hl.ne_zero hd), fun q => ?_, ?_, fun d => ?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.tqFam, Fin.coe_castSucc, Fin.is_lt, if_true, Fin.val_last,
      lt_irrefl, if_false, GlobalTheory.HeckeFamilyMatrices.dg, GlobalTheory.HeckeFamilyMatrices.mat]
  · simp only [opL, Finset.sum_range, GlobalTheory.HeckeFamilyMatrices.ulFam]
  · simp [opL, GlobalTheory.HeckeFamilyMatrices.mat]

end GlobalTheory.KZ.DiamondOperatorFamilies
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlane
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem summable_norm_mul_pow_of_polyB {a : ℕ → ℂ} (ha : PolyB a) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖a n * q ^ n‖ := by
  obtain ⟨C, A, hC⟩ := ha
  rcases eq_or_ne q 0 with rfl | hq0
  · exact (hasSum_single 0 (fun n hn => by simp [zero_pow hn])).summable
  · have hr0 : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hr : ‖‖q‖‖ < 1 := by rwa [norm_norm]
    have h := (summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * ‖q‖ ^ m)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (h.mul_left (C * ‖q‖⁻¹))
    rw [norm_mul, norm_pow]
    have hq' : ‖q‖ ≠ 0 := hr0.ne'
    have e : C * ‖q‖⁻¹ * (((n + 1 : ℕ) : ℝ) ^ A * ‖q‖ ^ (n + 1)) = C * ((n : ℝ) + 1) ^ A * ‖q‖ ^ n := by
      push_cast
      rw [pow_succ]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (hC n) (by positivity)

theorem qs_term_eq (a : ℕ → ℂ) (τ : ℍ) (n : ℕ) :
    a n * cexp (2 * π * Complex.I * n * τ) = a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n := by
  simp only [smul_eq_mul, Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem hasSum_qs {a : ℕ → ℂ} (ha : PolyB a) (τ : ℍ) :
    HasSum (fun n : ℕ => a n • (Function.Periodic.qParam 1 (τ : ℂ)) ^ n) (qs a τ) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hs : Summable fun n => a n • Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
    simpa only [smul_eq_mul] using (summable_norm_mul_pow_of_polyB ha hq).of_norm
  convert hs.hasSum using 1
  show ∑' n, a n * cexp (2 * π * Complex.I * n * τ) = _
  exact tsum_congr fun n => qs_term_eq a τ n

private theorem mdifferentiable_qs_of_polyB {a : ℕ → ℂ} (ha : PolyB a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  set r : ℝ := Real.exp (-(2 * π * y0)) with hrdef
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : ‖(r : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hrdef, Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm (summable_norm_mul_pow_of_polyB ha hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU ?_
    intro n w hw
    rw [norm_mul, norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, hrdef, ← Real.exp_nat_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Real.exp_le_exp]
    have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hw' : y0 < w.im := hw
    have := mul_nonneg (mul_nonneg Real.pi_pos.le hn) (sub_pos.2 hw').le
    nlinarith
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

private theorem periodic_qs_comp_ofComplex_one (a : ℕ → ℂ) :
    Function.Periodic (qs a ∘ ofComplex) 1 := by
  intro w
  by_cases hw : 0 < w.im
  · have hw1 : 0 < (w + 1).im := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw1, ofComplex_apply_of_im_pos hw]
    show ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * (w + 1))
      = ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)
    refine tsum_congr fun n => ?_
    congr 1
    rw [show 2 * π * Complex.I * n * (w + 1) = 2 * π * Complex.I * n * w + n * (2 * π * Complex.I) by ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · push_neg at hw
    have hw1 : (w + 1).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos hw1, ofComplex_apply_of_im_nonpos hw]

theorem analyticAt_cuspFunction_qs {a : ℕ → ℂ} (ha : PolyB a) :
    AnalyticAt ℂ (cuspFunction 1 (qs a)) 0 := by
  exact analyticAt_cuspFunction_zero one_pos (periodic_qs_comp_ofComplex_one a)
    (mdifferentiable_qs_of_polyB ha) (isBoundedAtImInfty_of_hasSum_qExpansion one_pos (hasSum_qs ha))

theorem coef_qs : ∀ a : ℕ → ℂ, PolyB a → ∀ n, coef (qs a) n = a n := by
  intro a ha n
  have hb := analyticAt_cuspFunction_qs ha
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos hb (hasSum_qs ha)).hasFPowerSeriesAt
  have h2 := hb.hasFPowerSeriesAt
  have e := congr_arg (FormalMultilinearSeries.coeff · n) (h1.eq_formalMultilinearSeries h2)
  simp only [FormalMultilinearSeries.coeff_ofScalars] at e
  show (qExpansion 1 (qs a)).coeff n = a n
  rw [qExpansion_coeff, e, div_eq_inv_mul]

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedQExpansionDouble
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eis_norm_le (j : ℕ) (c : ℂ) (a b : ℤ → ℂ) (Ca Cb : ℝ) (ha : ∀ x, ‖a x‖ ≤ Ca)
    (hb : ∀ x, ‖b x‖ ≤ Cb) (n : ℕ) (hn : n ≠ 0) :
    ‖eis j c a b n‖ ≤ Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1) := by
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  simp only [eis, if_neg hn]
  refine (norm_sum_le _ _).trans ?_
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  have key : ∀ p ∈ n.divisorsAntidiagonal,
      ‖a p.1 * (p.1 : ℂ) ^ (j - 1) * b p.2‖ ≤ Ca * Cb * (n : ℝ) ^ (j - 1) := by
    intro p hp
    have hle : p.1 ≤ n := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have h1 : (p.1 : ℝ) ^ (j - 1) ≤ (n : ℝ) ^ (j - 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) _
    calc ‖a p.1‖ * (p.1 : ℝ) ^ (j - 1) * ‖b p.2‖ ≤ Ca * (n : ℝ) ^ (j - 1) * Cb :=
          mul_le_mul (mul_le_mul (ha _) h1 (by positivity) hCa) (hb _) (norm_nonneg _) (by positivity)
      _ = Ca * Cb * (n : ℝ) ^ (j - 1) := by ring
  refine (Finset.sum_le_sum key).trans (le_of_eq ?_)
  rw [Finset.sum_const, hcard, nsmul_eq_mul]
  ring

theorem eis_qseries : ∀ (j : ℕ) (c : ℂ) (a b : ℤ → ℂ), (∃ C : ℝ, ∀ x, ‖a x‖ ≤ C) → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → PolyB (eis j c a b) ∧ (∃ C : ℝ, ∀ n, n ≠ 0 → ‖eis j c a b n‖ ≤ C * n.divisors.card * (n : ℝ) ^ (j - 1)) ∧ ∀ τ : ℍ, HasSum (fun y : ℕ => b (y + 1 : ℕ) * ∑' x : ℕ, ((x + 1 : ℕ) : ℂ) ^ (j - 1) * a (x + 1 : ℕ) * cexp (2 * π * Complex.I * (x + 1 : ℕ) * ((y + 1 : ℕ) * τ))) (qs (eis j c a b) τ - c) := by
  intro j c a b ⟨Ca, ha⟩ ⟨Cb, hb⟩
  have hCa : 0 ≤ Ca := (norm_nonneg _).trans (ha 0)
  have hCb : 0 ≤ Cb := (norm_nonneg _).trans (hb 0)
  have hB := eis_norm_le j c a b Ca Cb ha hb
  refine ⟨?_, ⟨Ca * Cb, hB⟩, ?_⟩
  · refine ⟨max ‖c‖ (Ca * Cb), j + 1, fun n => ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [eis]
    · refine (hB n hn).trans ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h1 : (n.divisors.card : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.card_divisors_le_self n
        have : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast this
        linarith
      have h2 : (n : ℝ) ^ (j - 1) ≤ ((n : ℝ) + 1) ^ j :=
        (pow_le_pow_left₀ hn0 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (Nat.sub_le j 1))
      have h3 : Ca * Cb ≤ max ‖c‖ (Ca * Cb) := le_max_right _ _
      have h4 : 0 ≤ Ca * Cb := mul_nonneg hCa hCb
      calc Ca * Cb * n.divisors.card * (n : ℝ) ^ (j - 1)
          ≤ max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) * ((n : ℝ) + 1) ^ j := by
            apply mul_le_mul (mul_le_mul h3 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)
        _ = max ‖c‖ (Ca * Cb) * ((n : ℝ) + 1) ^ (j + 1) := by ring
  · intro τ
    set q : ℂ := cexp (2 * π * Complex.I * τ) with hqdef
    have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
    have hE : ∀ m : ℕ, cexp (2 * π * Complex.I * m * τ) = q ^ m := fun m => by
      rw [hqdef, ← Complex.exp_nat_mul]; ring_nf
    have hE2 : ∀ m l : ℕ, cexp (2 * π * Complex.I * (m : ℂ) * ((l : ℂ) * τ)) = q ^ (m * l) := fun m l => by
      rw [hqdef, ← Complex.exp_nat_mul]; push_cast; ring_nf
    set H : ℕ+ × ℕ+ → ℂ := fun d => a ((d.1 : ℕ) : ℤ) * (((d.1 : ℕ) : ℂ)) ^ (j - 1) * b ((d.2 : ℕ) : ℤ) *
      q ^ ((d.1 : ℕ) * (d.2 : ℕ)) with hHdef
    have hHs : Summable H := by
      refine Summable.of_norm_bounded ((summable_prod_mul_pow (j - 1) hq).prod_symm.norm.mul_left (Ca * Cb)) fun d => ?_
      simp only [hHdef, norm_mul, norm_pow, Complex.norm_natCast, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm ((d.2 : ℕ)) (d.1 : ℕ)]
      refine (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right (ha _) (by positivity)) (hb _)
        (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)).trans (le_of_eq ?_)
      ring
    have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hHs.hasSum
    have h3 : HasSum (fun n : ℕ+ => eis j c a b n * q ^ (n : ℕ)) (∑' d, H d) := by
      refine h2.sigma fun n => ?_
      refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
      simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe,
        Equiv.coe_fn_mk, Finset.univ_eq_attach, hHdef]
      rw [(n : ℕ).divisorsAntidiagonal.sum_attach (fun y : ℕ × ℕ => a (y.1 : ℤ) * ((y.1 : ℕ) : ℂ) ^ (j - 1) * b (y.2 : ℤ) * q ^ (y.1 * y.2))]
      simp only [eis, if_neg n.ne_zero, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Nat.mem_divisorsAntidiagonal.1 hp).1]
    have h4 : HasSum (fun n : ℕ => eis j c a b n * q ^ n) (c + ∑' d, H d) := by
      have h5 := (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ => eis j c a b n * q ^ n)).1 h3
      have h6 := HasSum.zero_add (f := fun n : ℕ => eis j c a b n * q ^ n) h5
      have h7 : eis j c a b 0 * q ^ 0 = c := by simp [eis]
      rw [h7] at h6
      exact h6
    have hqs : qs (eis j c a b) τ = c + ∑' d, H d := by
      unfold qs
      rw [← h4.tsum_eq]
      exact tsum_congr fun n => by rw [hE]
    rw [hqs, add_sub_cancel_left]
    let e : ℕ × ℕ ≃ ℕ+ × ℕ+ := (Equiv.prodComm ℕ ℕ).trans (Equiv.pnatEquivNat.symm.prodCongr Equiv.pnatEquivNat.symm)
    set F : ℕ × ℕ → ℂ := fun p => b (p.1 + 1 : ℕ) * (((p.2 + 1 : ℕ) : ℂ) ^ (j - 1) * a (p.2 + 1 : ℕ) *
      cexp (2 * π * Complex.I * (p.2 + 1 : ℕ) * ((p.1 + 1 : ℕ) * τ))) with hFdef
    have hFe : F = H ∘ e := by
      funext p
      simp only [hFdef, hHdef, Function.comp, e, Equiv.trans_apply, Equiv.prodComm_apply, Prod.fst_swap,
        Prod.snd_swap, Equiv.prodCongr_apply, Prod.map, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Nat.succ_eq_add_one]
      rw [hE2, mul_comm (p.2 + 1) (p.1 + 1)]
      ring
    have hFs : Summable F := by rw [hFe]; exact e.summable_iff.2 hHs
    have hF : HasSum F (∑' d, H d) := by rw [hFe]; exact e.hasSum_iff.2 hHs.hasSum
    refine hF.prod_fiberwise fun y => ?_
    rw [← tsum_mul_left]
    exact (hFs.prod_factor y).hasSum

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUVCauchyProductIdentities
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.FormalId

variable {R : Type} [CommRing R]

theorem uo_mul_vo (l : ℕ) (hl : 0 < l) (a b : ℕ → R) : Uo l (mul a (Vo l b)) = mul (Uo l a) b := by
  funext n
  simp only [Uo, mul, Vo, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun p => (l * p.1, l * p.2)) (fun p => (p.1 / l, p.2 / l))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    exact ⟨by rw [← mul_add, hp], dvd_mul_right _ _⟩
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    rw [← Nat.add_div_of_dvd_right h3, h1, Nat.mul_div_cancel_left _ hl]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨h1, h2⟩ := hp
    have h3 : l ∣ p.1 := by
      have : l ∣ p.1 + p.2 := by rw [h1]; exact dvd_mul_right _ _
      exact (Nat.dvd_add_left h2).mp this
    ext <;> simp [Nat.mul_div_cancel' h3, Nat.mul_div_cancel' h2]
  · intro p _
    simp [Nat.mul_div_cancel_left _ hl]

theorem mul_comm' (a b : ℕ → R) : mul a b = mul b a := by
  funext n
  simp only [mul]
  conv_lhs => rw [← Finset.Nat.sum_antidiagonal_swap]
  simp [_root_.mul_comm]

theorem mul_add_right' (a b b' : ℕ → R) : mul a (b + b') = mul a b + mul a b' := by
  funext n
  simp [mul, _root_.mul_add, Finset.sum_add_distrib]

theorem mul_add_left' (a a' b : ℕ → R) : mul (a + a') b = mul a b + mul a' b := by
  rw [mul_comm', mul_add_right', mul_comm' b, mul_comm' b]

theorem mul_lin (a b b' : ℕ → R) (c c' : R) :
    mul a (c • b + c' • b') = c • mul a b + c' • mul a b' := by
  funext n
  simp only [mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

theorem zero_mul' (b : ℕ → R) : mul 0 b = 0 := by
  funext n; simp [mul]

theorem uo_dep (l : ℕ) (a : ℕ → R) : Uo l (dep l a) = 0 := by
  funext n; simp [Uo, dep]

theorem uo_vo (l : ℕ) (hl : 0 < l) (a : ℕ → R) : Uo l (Vo l a) = a := by
  funext n; simp [Uo, Vo, Nat.mul_div_cancel_left _ hl]

theorem dep_add (l : ℕ) (hl : 0 < l) (a : ℕ → R) : a = dep l a + Vo l (Uo l a) := by
  funext n
  by_cases h : l ∣ n
  · simp [dep, Vo, Uo, h, Nat.mul_div_cancel' h]
  · simp [dep, Vo, Uo, h]

theorem uo_add (l : ℕ) (x y : ℕ → R) : Uo l (x + y) = Uo l x + Uo l y := rfl

theorem uo_mul_dep (l : ℕ) (hl : 0 < l) (a b : ℕ → R) :
    Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b) := by
  have e : Uo l (mul a b) = Uo l (mul (dep l a) (dep l b)) + mul (Uo l a) (Uo l b) := by
    conv_lhs => rw [dep_add l hl a, dep_add l hl b]
    rw [mul_add_left', mul_add_right', mul_add_right', uo_add, uo_add, uo_add,
      uo_mul_vo l hl, uo_dep, zero_mul', mul_comm' (Vo l (Uo l a)) (dep l b), uo_mul_vo l hl, uo_dep,
      zero_mul', uo_mul_vo l hl, uo_vo l hl]
    abel
  rw [e]; abel

theorem to_vo (l k q : ℕ) (c : R) (a : ℕ → R) (hq : q.Coprime l) (hq0 : 0 < q) :
    To k c q (Vo l a) = Vo l (To k c q a) := by
  funext n
  simp only [To, Vo]
  by_cases hn : l ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl; simp
    have h1 : l ∣ q * (l * m) := ⟨q * m, by ring⟩
    rw [if_pos h1, if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl,
      show q * (l * m) = l * (q * m) by ring, Nat.mul_div_cancel_left _ hl]
    congr 1
    by_cases hqm : q ∣ m
    · obtain ⟨t, rfl⟩ := hqm
      rw [if_pos ⟨l * t, by ring⟩, if_pos (dvd_mul_right _ _),
        show l * (q * t) = q * (l * t) by ring, Nat.mul_div_cancel_left _ hq0, Nat.mul_div_cancel_left _ hq0,
        if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ hl]
    · rw [if_neg hqm, if_neg]
      intro h
      exact hqm ((Nat.Coprime.dvd_of_dvd_mul_left hq h))
  · have h1 : ¬ l ∣ q * n := fun h => hn (Nat.Coprime.dvd_of_dvd_mul_left hq.symm h)
    rw [if_neg h1, if_neg hn]
    by_cases hqn : q ∣ n
    · rw [if_pos hqn, if_neg]
      · simp
      · intro h
        obtain ⟨t, ht⟩ := hqn
        apply hn
        rw [ht, Nat.mul_div_cancel_left _ hq0] at h
        exact Dvd.dvd.mul_left h q |> fun h' => by rw [ht]; exact h'
    · simp [hqn]

theorem lam_lin (B : ℕ) (c a b : ℕ → R) (x y : R) :
    lam B c (x • a + y • b) = x * lam B c a + y * lam B c b := by
  simp only [lam, Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.EisM.FormalId

theorem GlobalTheory.EisM.formal_identities : ∀ (R : Type) [CommRing R] (l : ℕ), 0 < l → (∀ a b : ℕ → R, Uo l (mul a (Vo l b)) = mul (Uo l a) b) ∧ (∀ a b : ℕ → R, Uo l (mul (dep l a) (dep l b)) = Uo l (mul a b) - mul (Uo l a) (Uo l b)) ∧ (∀ a b : ℕ → R, mul a b = mul b a) ∧ (∀ (a b b' : ℕ → R) (c c' : R), mul a (c • b + c' • b') = c • mul a b + c' • mul a b') ∧ (∀ (k q : ℕ) (c : R) (a : ℕ → R), q.Coprime l → 0 < q → To k c q (Vo l a) = Vo l (To k c q a)) ∧ (∀ (B : ℕ) (c a b : ℕ → R) (x y : R), lam B c (x • a + y • b) = x * lam B c a + y * lam B c b) := by
  intro R _ l hl
  exact ⟨FormalId.uo_mul_vo l hl, FormalId.uo_mul_dep l hl, FormalId.mul_comm', FormalId.mul_lin,
    fun k q c a hq hq0 => FormalId.to_vo l k q c a hq hq0, FormalId.lam_lin⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorPolynomialGrowthQExpansion
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem Vo_polyB_qs : ∀ (l : ℕ) (a : ℕ → ℂ), 0 < l → PolyB a →
    PolyB (Vo l a) ∧ ∀ τ σ : ℍ, (σ : ℂ) = l * τ → qs (Vo l a) τ = qs a σ := by
  intro l a hl ha
  refine ⟨?_, ?_⟩
  · obtain ⟨C, A, h⟩ := ha
    have hC : 0 ≤ C := by
      have := h 0
      simp at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, A, fun n => ?_⟩
    unfold Vo
    split_ifs with hd
    · refine (h (n / l)).trans ?_
      gcongr
      exact_mod_cast Nat.div_le_self n l
    · simp only [norm_zero]; positivity
  · intro τ σ hσ
    unfold qs
    have hinj : Function.Injective (fun m : ℕ => l * m) :=
      fun x y hxy => Nat.eq_of_mul_eq_mul_left hl hxy
    have hsupp : Function.support (fun n : ℕ => Vo l a n * cexp (2 * π * Complex.I * n * τ)) ⊆
        Set.range (fun m : ℕ => l * m) := by
      intro n hn
      by_contra hr
      apply hn
      have : ¬ l ∣ n := by
        rintro ⟨m, rfl⟩
        exact hr ⟨m, rfl⟩
      simp [Vo, this]
    rw [← hinj.tsum_eq hsupp]
    congr 1
    ext m
    have hl' : l ≠ 0 := hl.ne'
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl, hσ]
    congr 2
    push_cast
    ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixMulCommModGamma1CapGamma0
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem isDiam_mul_comm_mod_Gam (N l d d' : ℕ) (σ σ' : SL(2, ℤ)) (h : IsDiam N l d σ) (h' : IsDiam N l d' σ') :
    ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  obtain ⟨⟨h0, h1⟩, -⟩ := h
  obtain ⟨⟨h0', h1'⟩, -⟩ := h'
  refine ⟨σ' * σ * (σ * σ')⁻¹, ⟨?_, ?_⟩, by group⟩
  · set a : CongruenceSubgroup.Gamma0 N := ⟨σ, h0⟩ with ha
    set b : CongruenceSubgroup.Gamma0 N := ⟨σ', h0'⟩ with hb
    have hu : (CongruenceSubgroup.Gamma0Map N).toHomUnits (b * a * (a * b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm ((CongruenceSubgroup.Gamma0Map N).toHomUnits b), mul_inv_cancel]
    have h3 : b * a * (a * b)⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
      rw [CongruenceSubgroup.Gamma1_mem', ← MonoidHom.coe_toHomUnits, hu, Units.val_one]
    exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1' h1) (Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h1'))

end GlobalTheory.KZ
end

