module

public import Formalism.UnipotentAdelicQuotients.Bundle0003

@[expose] public section

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.Moments
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem moments_integrable_of_nrm {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by
  set m : ℕ := n + (d + 1) with hm
  let A : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2
  let B : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)
  have hAm : Continuous A := by
    have : Continuous fun v : E d => (1 + ‖v‖ ^ 2) := by fun_prop
    exact (this.pow m).mul ((continuous_norm.comp hF).pow 2)
  have hA : Integrable A := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hs := h m
    unfold nrm om at hs
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs
    have ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    congr 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
      Real.rpow_zero, mul_one]
    rw [← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hB : Integrable B := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  refine (hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  have ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by linarith
  have hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹ := by
    simp only [B]
    rw [show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
  have hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2 := by
    rw [hBv]
    simp only [A, hm, pow_add]
    field_simp
  have hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v := by
    rw [hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    linarith
  have hA0 : 0 ≤ A v := by positivity
  have hB0 : 0 ≤ B v := by simp only [B]; positivity
  have hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖ := by positivity
  rw [Real.norm_of_nonneg hx0]
  show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v
  nlinarith [sq_nonneg (A v - B v), mul_nonneg hA0 hB0]

theorem smoothOfSobolevAll : MomentsSmooth := by
  intro d g hg hgc hs
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ (E d)) Real.continuous_fourierChar
      (by simpa using continuous_inner) hgi
  have hmom := moments_integrable_of_nrm (𝓕 g) hFc hs
  have hFi : Integrable (𝓕 g) := by
    have h0 := hmom 0
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff hFc.aestronglyMeasurable).mp h0
  have hinv := hg.fourierInv_fourier_eq hgi hFi
  have hsm : ContDiff ℝ ∞ (𝓕 (𝓕 g)) :=
    VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) (μ := volume) (N := ⊤) (f := 𝓕 g)
      (fun n _ => hmom n)
  have hg' : g = fun w => 𝓕 (𝓕 g) (-w) := by
    conv_lhs => rw [← hinv]
    ext w
    exact Real.fourierInv_eq_fourier_neg _ w
  rw [hg']
  exact hsm.comp contDiff_neg

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.SmoothOfLocallySmooth
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem integralFourierChar : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring

theorem existsBump : Bump := by
  intro d x0 r hr
  let f : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball (show r / 2 < r by linarith)
  · filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy
    exact f.one_of_mem_closedBall (ball_subset_closedBall hy)

theorem cutoffContinuous : CutCont := by
  intro d U u χ hU hu hχs hχc hχt
  have hχ' : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχs.continuous
  have hsub : tsupport (cut χ u) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra h0
    apply hx
    have h0' : χ x = 0 := by simpa using h0
    simp [cut, h0']
  have hcont : ContinuousOn (cut χ u) U := hχ'.continuousOn.mul hu
  exact ⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt),
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩

theorem smoothOfLocallySmooth : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.SymbLower
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

private theorem symb_smul_covector_eq_pow_ord_mul {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x ξ : E d) (t : ℝ) :
    P.symb i x (t • ξ) = (t : ℂ) ^ (P.ord i) * P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ l, (((t • ξ) (w l) : ℝ) : ℂ) = (t : ℂ) * ((ξ (w l) : ℝ) : ℂ) := fun l => by simp
  simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem continuous_symb_covector {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x : E d) : Continuous fun ξ : E d => P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  fun_prop

theorem symbolLowerBound : SymbLower := by
  intro d ι _ P x0 k hk hell
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ,
      f = fun ξ => ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := ⟨_, rfl⟩
  have hfξ : ∀ ξ, f ξ = ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := by
    intro ξ; rw [hf]
  have hcont : Continuous f := by
    rw [hf]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_norm.pow _).mul
      ((continuous_symb_covector P i x0).norm.pow 2)
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ ξ : E d, f (t • ξ) = t ^ (2 * k) * f ξ := by
    intro t ht ξ
    rw [hfξ, hfξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
    have h2 : ‖(t : ℂ) ^ (P.ord i) * P.symb i x0 ξ‖
        = t ^ (P.ord i) * ‖P.symb i x0 ξ‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht]
    rw [symb_smul_covector_eq_pow_ord_mul, h1, h2]
    have hk' : 2 * k = 2 * (k - P.ord i) + 2 * P.ord i := by have := hk i; omega
    rw [hk', pow_add]
    ring
  rcases (sphere (0 : E d) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun ξ hξ => ?_⟩
    exfalso
    have hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
    rw [hS] at hmem
    exact hmem
  · obtain ⟨η0, hη0S, hmin⟩ := (isCompact_sphere (0 : E d) 1).exists_isMinOn hS hcont.continuousOn
    have hη0n : ‖η0‖ = 1 := mem_sphere_zero_iff_norm.mp hη0S
    have hne : η0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hη0n
      exact zero_ne_one hη0n
    obtain ⟨i, hi⟩ := hell η0 hne
    have hpos : 0 < f η0 := by
      have hle : ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 ≤ f η0 := by
        rw [hfξ]
        exact Finset.single_le_sum
          (f := fun j => ‖η0‖ ^ (2 * (k - P.ord j)) * ‖P.symb j x0 η0‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      have hlt : 0 < ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 := by
        rw [hη0n, one_pow, one_mul]
        exact pow_pos (norm_pos_iff.mpr hi) 2
      linarith
    refine ⟨f η0, hpos, fun ξ hξ => ?_⟩
    have ht : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hηS : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
    have hξη : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hle : f η0 ≤ f (‖ξ‖⁻¹ • ξ) := hmin hηS
    have hfx : f ξ = ‖ξ‖ ^ (2 * k) * f (‖ξ‖⁻¹ • ξ) := by
      conv_lhs => rw [hξη]
      exact hhom _ ht.le _
    rw [← hfξ, hfx, mul_comm]
    exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end ZetaZeros.D.EllReg
end

-- bundled from Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightDiff
section
namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable section

namespace WD

variable {d : ℕ}

lemma pow_cmp {X Y K : ℝ} (p : ℝ) (hX : 0 < X) (hY : 0 < Y) (hK : 1 ≤ K)
    (h1 : X ≤ K * Y) (h2 : Y ≤ K * X) : X ^ p ≤ K ^ |p| * Y ^ p := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp, ← Real.mul_rpow hK0.le hY.le]
    exact Real.rpow_le_rpow hX.le h1 hp
  · rw [abs_of_neg hp]
    have h3 : K⁻¹ * Y ≤ X := by
      calc K⁻¹ * Y ≤ K⁻¹ * (K * X) := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hK0.le)
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]
    have hKY : 0 < K⁻¹ * Y := mul_pos (inv_pos.2 hK0) hY
    have h4 : X ^ p ≤ (K⁻¹ * Y) ^ p := by
      exact Real.rpow_le_rpow_of_nonpos hKY h3 hp.le
    calc X ^ p ≤ (K⁻¹ * Y) ^ p := h4
      _ = K ^ (-p) * Y ^ p := by
        rw [Real.mul_rpow (inv_nonneg.2 hK0.le) hY.le, Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le]

lemma base (c : ℝ) (x y : E d) :
    1 + c ^ 2 * ‖x‖ ^ 2 ≤ 2 * (1 + c ^ 2 * ‖x - y‖ ^ 2) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
  have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have ha := norm_nonneg (x - y)
  have hb := norm_nonneg y
  have hx := norm_nonneg x
  have hc := sq_nonneg c
  have hsq : ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x - y‖ - ‖y‖), mul_le_mul h1 h1 hx (add_nonneg ha hb)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hc,
    mul_nonneg (mul_nonneg hc hc) (mul_nonneg (sq_nonneg ‖x - y‖) (sq_nonneg ‖y‖))]

lemma cmp1 (c : ℝ) (hc : c ^ 2 ≤ 1) (x y v : E d) (hv : ‖x - y‖ ≤ ‖v‖) :
    1 + c ^ 2 * ‖x‖ ^ 2 ≤ (2 * (1 + ‖v‖ ^ 2)) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
  have h := base c x y
  have ha := norm_nonneg (x - y)
  have hv2 : ‖x - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [mul_le_mul hv hv ha (norm_nonneg v)]
  have h3 : c ^ 2 * ‖x - y‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc) (sq_nonneg ‖x - y‖)]
  have hy : 0 ≤ 1 + c ^ 2 * ‖y‖ ^ 2 := by positivity
  calc 1 + c ^ 2 * ‖x‖ ^ 2 ≤ 2 * (1 + c ^ 2 * ‖x - y‖ ^ 2) * (1 + c ^ 2 * ‖y‖ ^ 2) := h
    _ ≤ (2 * (1 + ‖v‖ ^ 2)) * (1 + c ^ 2 * ‖y‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hy
      linarith

lemma om_shift (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ζ η v : E d)
    (hv : ‖ζ - η‖ ≤ ‖v‖) :
    om s M ε ζ ≤ (2 * (1 + ‖v‖ ^ 2)) ^ (|s / 2| + M / 2) * om s M ε η := by
  have hA1 : (1 : ℝ) ≤ 2 * (1 + ‖v‖ ^ 2) := by nlinarith [sq_nonneg ‖v‖]
  have hA0 : (0 : ℝ) < 2 * (1 + ‖v‖ ^ 2) := by linarith
  have hv' : ‖η - ζ‖ ≤ ‖v‖ := by rw [norm_sub_rev]; exact hv
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hone : (1 : ℝ) ^ 2 ≤ 1 := by norm_num
  have P1 := cmp1 1 hone ζ η v hv
  have P2 := cmp1 1 hone η ζ v hv'
  have Q1 := cmp1 ε hε2 ζ η v hv
  have Q2 := cmp1 ε hε2 η ζ v hv'
  simp only [one_pow, one_mul] at P1 P2
  have hζ : (0 : ℝ) < 1 + ‖ζ‖ ^ 2 := by positivity
  have hη : (0 : ℝ) < 1 + ‖η‖ ^ 2 := by positivity
  have hζε : (0 : ℝ) < 1 + ε ^ 2 * ‖ζ‖ ^ 2 := by positivity
  have hηε : (0 : ℝ) < 1 + ε ^ 2 * ‖η‖ ^ 2 := by positivity
  have F1 := pow_cmp (s / 2) hζ hη hA1 P1 P2
  have F2 := pow_cmp (-(M / 2)) hζε hηε hA1 Q1 Q2
  rw [abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ M / 2)] at F2
  unfold ZetaZeros.D.EllReg.om
  calc _ ≤ ((2 * (1 + ‖v‖ ^ 2)) ^ |s / 2| * (1 + ‖η‖ ^ 2) ^ (s / 2)) *
        ((2 * (1 + ‖v‖ ^ 2)) ^ (M / 2) * (1 + ε ^ 2 * ‖η‖ ^ 2) ^ (-(M / 2))) :=
        mul_le_mul F1 F2 (by positivity) (by positivity)
    _ = _ := by rw [Real.rpow_add hA0]; ring

private theorem abs_mul_sub_le_of_sq_eq_one_add_sq (g t s M e r b V : ℝ) (hg : 0 ≤ g) (hV : 0 ≤ V) (ht : |t| ≤ g * V)
    (hM : 0 ≤ M) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr0 : 0 < r) (hr2 : r ^ 2 = 1 + g ^ 2)
    (hb : b = 1 + e * g ^ 2) :
    |t * (s * r⁻¹ - M * e * r * b⁻¹)| ≤ (|s| + M) * V := by
  subst hb
  have hb0 : 0 < 1 + e * g ^ 2 := add_pos_of_pos_of_nonneg one_pos (mul_nonneg he0 (sq_nonneg g))
  have hgr : g ≤ r := by
    by_contra hcon
    have hlt := not_le.mp hcon
    nlinarith [mul_lt_mul'' hlt hlt hr0.le hr0.le]
  have hgr' : g * r⁻¹ ≤ 1 := by
    calc g * r⁻¹ ≤ r * r⁻¹ := mul_le_mul_of_nonneg_right hgr (inv_nonneg.2 hr0.le)
      _ = 1 := mul_inv_cancel₀ hr0.ne'
  have hsq : (g * e * r) ^ 2 ≤ (1 + e * g ^ 2) ^ 2 := by
    have h := mul_nonneg (mul_nonneg he0 (sq_nonneg g)) (by linarith : (0 : ℝ) ≤ 2 - e)
    have h' : (g * e * r) ^ 2 = g ^ 2 * e ^ 2 * r ^ 2 := by ring
    rw [h', hr2]
    nlinarith
  have hX : g * e * r ≤ 1 + e * g ^ 2 := by
    by_contra hcon
    have hlt := not_le.mp hcon
    nlinarith [mul_lt_mul'' hlt hlt hb0.le hb0.le]
  have hgb : g * (e * r * (1 + e * g ^ 2)⁻¹) ≤ 1 := by
    calc g * (e * r * (1 + e * g ^ 2)⁻¹) = (g * e * r) * (1 + e * g ^ 2)⁻¹ := by ring
      _ ≤ (1 + e * g ^ 2) * (1 + e * g ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hX (inv_nonneg.2 hb0.le)
      _ = 1 := mul_inv_cancel₀ hb0.ne'
  have hpos : 0 ≤ M * e * r * (1 + e * g ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hM he0) hr0.le) (inv_nonneg.2 hb0.le)
  have h1 : |s * r⁻¹ - M * e * r * (1 + e * g ^ 2)⁻¹| ≤ |s| * r⁻¹ + M * (e * r * (1 + e * g ^ 2)⁻¹) := by
    have h := norm_sub_le (s * r⁻¹) (M * e * r * (1 + e * g ^ 2)⁻¹)
    simp only [Real.norm_eq_abs] at h
    rw [abs_mul, abs_of_pos (inv_pos.2 hr0), abs_of_nonneg hpos] at h
    have e' : M * e * r * (1 + e * g ^ 2)⁻¹ = M * (e * r * (1 + e * g ^ 2)⁻¹) := by ring
    linarith
  have hsum : |s| * (g * r⁻¹) + M * (g * (e * r * (1 + e * g ^ 2)⁻¹)) ≤ |s| + M := by
    nlinarith [mul_le_mul_of_nonneg_left hgr' (abs_nonneg s), mul_le_mul_of_nonneg_left hgb hM]
  rw [abs_mul]
  calc |t| * |s * r⁻¹ - M * e * r * (1 + e * g ^ 2)⁻¹|
      ≤ (g * V) * (|s| * r⁻¹ + M * (e * r * (1 + e * g ^ 2)⁻¹)) :=
        mul_le_mul ht h1 (abs_nonneg _) (mul_nonneg hg hV)
    _ = V * (|s| * (g * r⁻¹) + M * (g * (e * r * (1 + e * g ^ 2)⁻¹))) := by ring
    _ ≤ V * (|s| + M) := mul_le_mul_of_nonneg_left hsum hV
    _ = (|s| + M) * V := by ring

lemma deriv_bound (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (γ v : E d) :
    |(2 * inner ℝ γ v) * (s / 2) * (1 + ‖γ‖ ^ 2) ^ (s / 2 - 1) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) +
      (1 + ‖γ‖ ^ 2) ^ (s / 2) *
        ((ε ^ 2 * (2 * inner ℝ γ v)) * (-(M / 2)) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2) - 1))|
    ≤ (|s| + M) * ‖v‖ * om (s - 1) M ε γ := by
  have ha : (0 : ℝ) < 1 + ‖γ‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + ε ^ 2 * ‖γ‖ ^ 2 := by positivity
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (1 + ‖γ‖ ^ 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 ha
  have hr2 : r ^ 2 = 1 + ‖γ‖ ^ 2 := by rw [hr]; exact Real.sq_sqrt ha.le
  have e1 : (1 + ‖γ‖ ^ 2) ^ (s / 2 - 1) = (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * r⁻¹ := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
    congr 1
    ring
  have e2 : (1 + ‖γ‖ ^ 2) ^ (s / 2) = (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * r := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    congr 1
    ring
  have e3 : (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2) - 1) =
      (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 1
  have hP : 0 < (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) := by positivity
  have hQ : 0 < (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) := by positivity
  have key := abs_mul_sub_le_of_sq_eq_one_add_sq ‖γ‖ (inner ℝ γ v) s M (ε ^ 2) r (1 + ε ^ 2 * ‖γ‖ ^ 2) ‖v‖
    (norm_nonneg _) (norm_nonneg _) (abs_real_inner_le_norm γ v) hM (sq_nonneg ε) hε2 hr0 hr2 rfl
  rw [e1, e2, e3]
  unfold ZetaZeros.D.EllReg.om
  calc _ = |((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) *
        (inner ℝ γ v * (s * r⁻¹ - M * ε ^ 2 * r * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹))| := by
          congr 1
          ring
    _ = ((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) *
        |inner ℝ γ v * (s * r⁻¹ - M * ε ^ 2 * r * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹)| := by
          rw [abs_mul, abs_of_pos (mul_pos hP hQ)]
    _ ≤ ((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) * ((|s| + M) * ‖v‖) :=
          mul_le_mul_of_nonneg_left key (mul_pos hP hQ).le
    _ = _ := by ring

end WD

open WD in
theorem sobolevWeightLipschitz : WeightDiff := by
  intro d s M hM
  have hN0 : 0 ≤ |(s - 1) / 2| + M / 2 := add_nonneg (abs_nonneg _) (by linarith)
  refine ⟨(|s| + M) * 2 ^ (|(s - 1) / 2| + M / 2), 2 * (|(s - 1) / 2| + M / 2),
    mul_nonneg (add_nonneg (abs_nonneg s) hM) (Real.rpow_nonneg (by norm_num) _), by linarith, ?_⟩
  intro ε hε0 hε1 ξ η
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => om s M ε (η + t • (ξ - η)))
      ((2 * inner ℝ (η + t • (ξ - η)) (ξ - η)) * (s / 2) * (1 + ‖η + t • (ξ - η)‖ ^ 2) ^ (s / 2 - 1) *
          (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ^ (-(M / 2)) +
        (1 + ‖η + t • (ξ - η)‖ ^ 2) ^ (s / 2) *
          ((ε ^ 2 * (2 * inner ℝ (η + t • (ξ - η)) (ξ - η))) * (-(M / 2)) *
            (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ^ (-(M / 2) - 1))) t := by
    intro t
    have hγ : HasDerivAt (fun t : ℝ => η + t • (ξ - η)) (ξ - η) t := by
      have := ((hasDerivAt_id' t).smul_const (ξ - η)).const_add η
      rwa [one_smul] at this
    have h1 : HasDerivAt (fun t : ℝ => 1 + ‖η + t • (ξ - η)‖ ^ 2)
        (2 * inner ℝ (η + t • (ξ - η)) (ξ - η)) t :=
      hγ.norm_sq.const_add 1
    have h2 : HasDerivAt (fun t : ℝ => 1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2)
        (ε ^ 2 * (2 * inner ℝ (η + t • (ξ - η)) (ξ - η))) t :=
      (hγ.norm_sq.const_mul (ε ^ 2)).const_add 1
    have hp1 : (1 + ‖η + t • (ξ - η)‖ ^ 2) ≠ 0 := by positivity
    have hp2 : (1 + ε ^ 2 * ‖η + t • (ξ - η)‖ ^ 2) ≠ 0 := by positivity
    exact (h1.rpow_const (Or.inl hp1)).mul (h2.rpow_const (Or.inl hp2))
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ, ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => om s M ε (η + t • (ξ - η))) (D t) t ∧
      |D t| ≤ (|s| + M) * ‖ξ - η‖ * om (s - 1) M ε (η + t • (ξ - η)) :=
    ⟨_, fun t => ⟨hderiv t, ZetaZeros.D.EllReg.WD.deriv_bound s M ε hM hε0 hε1 _ _⟩⟩
  have hW : ∀ t ∈ Set.Icc (0 : ℝ) 1, om (s - 1) M ε (η + t • (ξ - η)) ≤
      (2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η := by
    intro t ht
    apply ZetaZeros.D.EllReg.WD.om_shift (s - 1) M ε hM hε0 hε1
    have e : η + t • (ξ - η) - η = t • (ξ - η) := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hcoef : 0 ≤ (|s| + M) * ‖ξ - η‖ := mul_nonneg (add_nonneg (abs_nonneg s) hM) (norm_nonneg _)
  have hbd : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖D t‖ ≤ (|s| + M) * ‖ξ - η‖ *
      ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) := by
    intro t ht
    rw [Real.norm_eq_abs]
    exact (hD t).2.trans (mul_le_mul_of_nonneg_left (hW t (Set.Ico_subset_Icc_self ht)) hcoef)
  have hmvt : ‖om s M ε (η + (1 : ℝ) • (ξ - η)) - om s M ε (η + (0 : ℝ) • (ξ - η))‖ ≤
      (|s| + M) * ‖ξ - η‖ *
        ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) * (1 - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun t _ => (hD t).1.hasDerivWithinAt) hbd 1
      (Set.right_mem_Icc.2 zero_le_one)
  have e1 : η + (1 : ℝ) • (ξ - η) = ξ := by rw [one_smul]; abel
  have e0 : η + (0 : ℝ) • (ξ - η) = η := by rw [zero_smul, add_zero]
  rw [e1, e0, Real.norm_eq_abs, sub_zero, mul_one] at hmvt
  have hx := norm_nonneg (ξ - η)
  have hA : (2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) ≤
      2 ^ (|(s - 1) / 2| + M / 2) * (1 + ‖ξ - η‖) ^ (2 * (|(s - 1) / 2| + M / 2)) := by
    rw [Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + ‖ξ - η‖), Real.rpow_two,
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ (1 + ‖ξ - η‖) ^ 2)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) hN0
  have hW0 : 0 ≤ om (s - 1) M ε η := by unfold om; positivity
  calc |om s M ε ξ - om s M ε η|
      ≤ (|s| + M) * ‖ξ - η‖ *
        ((2 * (1 + ‖ξ - η‖ ^ 2)) ^ (|(s - 1) / 2| + M / 2) * om (s - 1) M ε η) := hmvt
    _ ≤ (|s| + M) * ‖ξ - η‖ *
        ((2 ^ (|(s - 1) / 2| + M / 2) * (1 + ‖ξ - η‖) ^ (2 * (|(s - 1) / 2| + M / 2))) *
          om (s - 1) M ε η) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA hW0) hcoef
    _ = _ := by ring

end

end ZetaZeros.D.EllReg
end

