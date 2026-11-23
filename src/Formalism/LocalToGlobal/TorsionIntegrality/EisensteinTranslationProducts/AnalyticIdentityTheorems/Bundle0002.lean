module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
section
noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real

namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion

lemma e2Summand_succ (z : ℍ) (a : ℕ) : e2Summand ((a : ℤ) + 1) z =
    -4 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((a + 1) * n : ℕ) := by
  have hw : 0 < (((a : ℂ) + 1) * (z : ℂ)).im := by
    have e : (((a : ℂ) + 1) * (z : ℂ)).im = ((a : ℝ) + 1) * (z : ℂ).im := by
      simp [Complex.mul_im]
    rw [e]
    exact mul_pos (by positivity) z.im_pos
  have H := EisensteinSeries.qExpansion_identity_pnat (k := 1) le_rfl ⟨((a : ℂ) + 1) * (z : ℂ), hw⟩
  have hc : ((⟨((a : ℂ) + 1) * (z : ℂ), hw⟩ : ℍ) : ℂ) = ((a : ℂ) + 1) * (z : ℂ) := rfl
  rw [hc] at H
  unfold EisensteinSeries.e2Summand
  have e1 : ∀ n : ℤ, eisSummand 2 ![(a : ℤ) + 1, n] z
      = 1 / (((a : ℂ) + 1) * (z : ℂ) + n) ^ (1 + 1) := by
    intro n
    simp [eisSummand, zpow_neg]
  have hq : ∀ n : ℕ+, cexp (2 * π * I * (((a : ℂ) + 1) * (z : ℂ))) ^ (n : ℕ)
      = cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ)) := by
    intro n
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [e1]
  rw [H]
  simp only [hq, pow_one]
  set S := ∑' n : ℕ+, ((n : ℕ) : ℂ) * cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))
  simp only [Nat.factorial, Nat.cast_one, div_one, Nat.mul_one, Nat.succ_eq_add_one, zero_add]
  linear_combination (4 * (π : ℂ) ^ 2 * S) * Complex.I_sq

lemma summable_e2Summand_succ (z : ℍ) : Summable fun a : ℕ => e2Summand ((a : ℤ) + 1) z := by
  set r := cexp (2 * π * I * (z : ℂ)) with hr
  set ρ := ‖r‖ with hρdef
  have hρ : ρ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hρ0])
  have hsumP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) := by
    have := hsum.comp_injective PNat.coe_injective
    simp only [pow_one] at this
    exact this
  set C := ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ)
  have hpt : ∀ (a : ℕ) (n : ℕ+), ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
      ≤ ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a := by
    intro a n
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc, ← pow_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply pow_le_pow_of_le_one hρ0 hρ.le
    have := n.pos
    nlinarith
  have hb : ∀ a : ℕ, ‖e2Summand ((a : ℤ) + 1) z‖ ≤ 4 * π ^ 2 * C * ρ ^ a := by
    intro a
    rw [e2Summand_succ, norm_mul]
    have h4 : ‖(-4 * (π : ℂ) ^ 2)‖ = 4 * π ^ 2 := by
      rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h4, mul_assoc (4 * π ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs : Summable fun n : ℕ+ => ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hpt a) (hsumP.mul_right _)
    calc ‖∑' n : ℕ+, ((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a :=
          Summable.tsum_le_tsum (hpt a) hs (hsumP.mul_right _)
      _ = C * ρ ^ a := tsum_mul_right
  exact Summable.of_norm_bounded (g := fun a : ℕ => 4 * π ^ 2 * C * ρ ^ a)
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left _) hb

lemma summable_e2Summand (z : ℍ) : Summable fun n : ℤ => e2Summand n z := by
  have hev := EisensteinSeries.e2Summand_even z
  have h0 : Summable fun n : ℕ => e2Summand (n : ℤ) z := by
    rw [← summable_nat_add_iff 1]
    refine (summable_e2Summand_succ z).congr ?_
    intro a
    push_cast
    rfl
  refine Summable.of_nat_of_neg h0 ?_
  refine h0.congr ?_
  intro n
  exact (hev (n : ℤ)).symm

lemma tsum_e2Summand (z : ℍ) : ∑' n : ℤ, e2Summand n z = G2 z := by
  unfold EisensteinSeries.G2
  exact (tsum_eq_of_summable_unconditional (summable_e2Summand z)).symm

private lemma one_div_sq_eq_of_eq_mul (X Y c : ℂ) (h : X = c * Y) :
    1 / X ^ 2 = (c ^ 2)⁻¹ * Y ^ (-2 : ℤ) := by
  subst h
  rw [mul_pow, one_div, mul_inv, zpow_neg]
  norm_cast

lemma sumA (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (u ^ 2)⁻¹ * G2 ⟨v / u, h⟩ := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext n
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [eisSummand, Matrix.cons_val, hc]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  ring

lemma sumB (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (v ^ 2)⁻¹ * G2 (S • ⟨v / u, h⟩) := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  have hw : ((S • (⟨v / u, h⟩ : ℍ) : ℍ) : ℂ) = -(u / v) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(v / u))⁻¹ = -(u / v)
    rw [inv_neg, inv_div]
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext m
  have he : e2Summand (-m) (S • (⟨v / u, h⟩ : ℍ)) = e2Summand m (S • (⟨v / u, h⟩ : ℍ)) :=
    EisensteinSeries.e2Summand_even _ m
  rw [← he]
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [eisSummand, Matrix.cons_val, hw]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  push_cast
  ring

lemma key (u v : ℂ) (h : 0 < (v / u).im) :
    (u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * v
      - (v * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * u = 2 * π * I := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  rw [sumA u v h, sumB u v h]
  have hT := EisensteinSeries.G2_S_transform ⟨v / u, h⟩
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [hc] at hT
  rw [hT]
  field_simp
  ring

end Formalism.L2.Th1.F.LegendreModelEllipticTorsion

namespace Formalism.L2.Th1.F

lemma LegendreModelEllipticTorsion.im_pos_of_not (L : PeriodPair) (h : ¬ 0 < (L.ω₂ / L.ω₁).im) :
    0 < (L.ω₁ / L.ω₂).im := by
  have hind := L.indep
  have ha : L.ω₁ ≠ 0 := by simpa using hind.ne_zero 0
  have hb : L.ω₂ ≠ 0 := by simpa using hind.ne_zero 1
  have hne : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro him
    have hr : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hbr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
      rw [← hr]
      field_simp
    have h2 := (LinearIndependent.pair_iff.mp hind) (L.ω₂ / L.ω₁).re (-1) (by
      rw [Complex.real_smul, Complex.real_smul]
      nth_rewrite 2 [hbr]
      push_cast
      ring)
    norm_num at h2
  have hlt : (L.ω₂ / L.ω₁).im < 0 := lt_of_le_of_ne (not_lt.mp h) hne
  rw [show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div _ _).symm, Complex.inv_im]
  exact div_pos (neg_pos.mpr hlt) (Complex.normSq_pos.mpr (div_ne_zero hb ha))

theorem legendre_of (h : EtaEisenstein) : Legendre := by
  intro L
  obtain ⟨h1, h2⟩ := h L
  rw [h1, h2]
  split_ifs with hp
  · rw [one_mul]
    exact LegendreModelEllipticTorsion.key L.ω₁ L.ω₂ hp
  · have hp' := LegendreModelEllipticTorsion.im_pos_of_not L hp
    have k := LegendreModelEllipticTorsion.key L.ω₂ L.ω₁ hp'
    have e1 : (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    have e2 : (∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    rw [e1, e2] at k
    linear_combination -k

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaBasic

lemma differentiable_wFactor (l : ℂ) : Differentiable ℂ (wFactor l) := by
  unfold wFactor
  fun_prop

lemma wFactor_zero_right (l : ℂ) : wFactor l 0 = 1 := by
  simp [wFactor]

lemma wFactor_neg_neg (l z : ℂ) : wFactor (-l) (-z) = wFactor l z := by
  simp only [wFactor, neg_div_neg_eq, neg_sq]

lemma wFactor_eq_zero_iff {l : ℂ} (hl : l ≠ 0) (z : ℂ) : wFactor l z = 0 ↔ z = l := by
  unfold wFactor
  rw [mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), sub_eq_zero, eq_comm, div_eq_one_iff_eq hl]

lemma wFactor_zero_left (z : ℂ) : wFactor 0 z = 1 := by
  simp [wFactor]

lemma differentiable_tprod (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ
  refine Eventually.of_forall fun s => ?_
  refine Differentiable.differentiableOn ?_
  intro x
  exact DifferentiableAt.fun_finsetProd fun l _ => differentiable_wFactor _ x

end SigmaBasic

open SigmaBasic

theorem sigmaEntire_of (h : SigmaProdLU) : SigmaEntire := by
  intro L
  unfold wSigma
  exact differentiable_id.mul (differentiable_tprod h L)

theorem sigma_odd : SigmaOdd := by
  intro L z
  have hP : ∏' l : L.lattice, wFactor (l : ℂ) (-z) = ∏' l : L.lattice, wFactor (l : ℂ) z := by
    have e := (Equiv.neg L.lattice).tprod_eq (fun l : L.lattice => wFactor (l : ℂ) (-z))
    rw [← e]
    congr 1
    ext l
    simp [wFactor_neg_neg]
  unfold wSigma
  rw [hP]
  ring

theorem sigmaZero_of (h : SigmaSummable) : SigmaZero := by
  intro L z
  unfold wSigma
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hz | hp
    · rw [hz]
      exact zero_mem _
    · by_contra hz
      have hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0 := by
        intro l hl
        by_cases hl0 : (l : ℂ) = 0
        · rw [hl0, wFactor_zero_left] at hl
          exact one_ne_zero hl
        · rw [wFactor_eq_zero_iff hl0] at hl
          exact hz (by rw [hl]; exact l.2)
      have hs : Summable (fun l : L.lattice => Complex.log (wFactor (l : ℂ) z)) := by
        have := Complex.summable_log_one_add_of_summable (Summable.of_norm (h L z))
        simpa only [add_sub_cancel] using this
      rw [← Complex.cexp_tsum_eq_tprod hne hs] at hp
      exact Complex.exp_ne_zero _ hp
  · intro hz
    by_cases hz0 : z = 0
    · rw [hz0, zero_mul]
    · rw [tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]

theorem sigmaDerivZero_of (h : SigmaProdLU) : ∀ L : PeriodPair, deriv (wSigma L) 0 = 1 := by
  intro L
  have hP := differentiable_tprod h L 0
  unfold wSigma
  rw [deriv_fun_mul (by fun_prop) hP]
  simp [wFactor_zero_right]

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter

namespace Formalism.L2.Th1.F

namespace SigmaConv

lemma norm_factor_sub_one_le (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    ‖(1 - w) * Complex.exp (w + w ^ 2 / 2) - 1‖ ≤ 2 * ‖w‖ ^ 3 := by
  set f : ℂ → ℂ := fun x => (1 - x) * Complex.exp (x + x ^ 2 / 2) with hf
  have hder : ∀ x : ℂ, HasDerivAt f (-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℂ => x + x ^ 2 / 2) (1 + x) x := by
      have h0 := (hasDerivAt_id x).add ((hasDerivAt_pow 2 x).div_const 2)
      exact h0.congr_deriv (by first | (norm_num; done) | (norm_num; ring) | ring)
    have h2 := ((hasDerivAt_id x).const_sub (1 : ℂ)).mul h1.cexp
    exact h2.congr_deriv (by simp only [id]; ring)
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖w‖,
      ‖-(x ^ 2) * Complex.exp (x + x ^ 2 / 2)‖ ≤ 2 * ‖w‖ ^ 2 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    have hx2 : ‖x‖ ≤ 1 / 2 := hx.trans hw
    rw [norm_mul, norm_neg, norm_pow, Complex.norm_exp]
    have h3 : ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x‖ ^ 2 / 2 := by
      calc ‖x + x ^ 2 / 2‖ ≤ ‖x‖ + ‖x ^ 2 / 2‖ := norm_add_le _ _
        _ = ‖x‖ + ‖x‖ ^ 2 / 2 := by rw [norm_div, norm_pow]; norm_num
    have hre : (x + x ^ 2 / 2).re ≤ 5 / 8 := by
      have := Complex.re_le_norm (x + x ^ 2 / 2)
      nlinarith [norm_nonneg x]
    have he : Real.exp ((x + x ^ 2 / 2).re) ≤ 2 := by
      calc Real.exp ((x + x ^ 2 / 2).re) ≤ Real.exp (5 / 8) := Real.exp_le_exp.mpr hre
        _ ≤ 2 := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9
          norm_num at this ⊢
          linarith
    have hx2' : ‖x‖ ^ 2 ≤ ‖w‖ ^ 2 := by gcongr
    calc ‖x‖ ^ 2 * Real.exp ((x + x ^ 2 / 2).re) ≤ ‖w‖ ^ 2 * 2 :=
          mul_le_mul hx2' he (Real.exp_pos _).le (sq_nonneg _)
      _ = 2 * ‖w‖ ^ 2 := by ring
  have hw0 : w ∈ Metric.closedBall (0 : ℂ) ‖w‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
  have key := (convex_closedBall (0 : ℂ) ‖w‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hder x).hasDerivWithinAt) hbound (Metric.mem_closedBall_self (norm_nonneg w)) hw0
  have f0 : f 0 = 1 := by simp [f]
  rw [f0, sub_zero] at key
  calc ‖f w - 1‖ ≤ 2 * ‖w‖ ^ 2 * ‖w‖ := key
    _ = 2 * ‖w‖ ^ 3 := by ring

lemma wFactor_eq (l z : ℂ) :
    wFactor l z = (1 - z / l) * Complex.exp (z / l + (z / l) ^ 2 / 2) := by
  unfold wFactor
  congr 2
  ring

lemma norm_wFactor_sub_one_le (r : ℝ) (l z : ℂ) (hz : ‖z‖ ≤ r) (hl : 2 * r ≤ ‖l‖) :
    ‖wFactor l z - 1‖ ≤ 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hrp : ‖l‖ ^ (-3 : ℝ) = (‖l‖ ^ 3)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg _)]
    norm_cast
  rcases eq_or_ne l 0 with rfl | hl0
  · have h1 : wFactor 0 z = 1 := by simp [wFactor]
    rw [h1, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hr 3)) (Real.rpow_nonneg le_rfl _)
  have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
  have hw : ‖z / l‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hlpos]
    linarith
  calc ‖wFactor l z - 1‖ ≤ 2 * ‖z / l‖ ^ 3 := by
        rw [wFactor_eq]
        exact norm_factor_sub_one_le _ hw
    _ = 2 * ‖z‖ ^ 3 * (‖l‖ ^ 3)⁻¹ := by rw [norm_div, div_pow]; ring
    _ ≤ 2 * r ^ 3 * (‖l‖ ^ 3)⁻¹ := by gcongr
    _ = 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ) := by rw [hrp]

private lemma summable_norm_lattice_rpow_neg_three (L : PeriodPair) :
    Summable (fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ)) := by
  have hfin : Module.finrank ℤ L.lattice = 2 := by
    rw [ZLattice.rank ℝ L.lattice, Complex.finrank_real_complex]
  exact ZLattice.summable_norm_rpow L.lattice (-3) (by rw [hfin]; norm_num)

lemma summable_majorant (L : PeriodPair) (r : ℝ) :
    Summable (fun l : L.lattice => 2 * r ^ 3 * ‖l‖ ^ (-3 : ℝ)) :=
  (summable_norm_lattice_rpow_neg_three L).mul_left _

lemma eventually_large (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  rcases le_or_gt R 0 with hR | hR
  · exact Eventually.of_forall fun l => hR.trans (norm_nonneg _)
  have ht := (summable_norm_lattice_rpow_neg_three L).tendsto_cofinite_zero
  have hε : (0 : ℝ) < R ^ (-3 : ℝ) := Real.rpow_pos_of_pos hR _
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_cofinite_ne 0] with l hl hl0
  have hpos : 0 < ‖(l : ℂ)‖ := by
    rw [norm_pos_iff]
    exact fun h => hl0 (Subtype.ext h)
  by_contra hlt
  push_neg at hlt
  have := Real.rpow_le_rpow_of_nonpos hpos hlt.le (by norm_num : (-3 : ℝ) ≤ 0)
  linarith

lemma continuous_wFactor (l : ℂ) : Continuous (wFactor l) := by
  unfold wFactor
  fun_prop

end SigmaConv

open SigmaConv

theorem sigma_summable : SigmaSummable := by
  intro L z
  refine Summable.of_norm_bounded_eventually (summable_majorant L ‖z‖) ?_
  filter_upwards [eventually_large L (2 * ‖z‖)] with l hl
  rw [norm_norm]
  exact norm_wFactor_sub_one_le ‖z‖ l z le_rfl hl

theorem sigma_product_locally_uniform : SigmaProdLU := by
  intro L
  have key : HasProdLocallyUniformlyOn (fun (l : L.lattice) (z : ℂ) => 1 + (wFactor (l : ℂ) z - 1))
      (fun z => ∏' l : L.lattice, (1 + (wFactor (l : ℂ) z - 1))) Set.univ := by
    rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine HasProdUniformlyOn.tendstoUniformlyOn <| Summable.hasProdUniformlyOn_one_add (f := fun (l : L.lattice) (z : ℂ) => wFactor (l : ℂ) z - 1)
      hK (summable_majorant L r) ?_ ?_
    · filter_upwards [eventually_large L (2 * r)] with l hl x hx
      exact norm_wFactor_sub_one_le r l x (by simpa using hr hx) hl
    · intro l
      exact ((continuous_wFactor _).sub continuous_const).continuousOn
  simpa only [add_sub_cancel] using key

end Formalism.L2.Th1.F
end
end

