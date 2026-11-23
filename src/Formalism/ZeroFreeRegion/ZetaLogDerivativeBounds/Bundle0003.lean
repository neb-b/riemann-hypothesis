module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos

@[expose] public section

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeightLogDeriv
section
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

lemma shld_identity {s : ℂ} (hs : s ≠ 1) (h1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, riemannZeta_eq_inv_sub_mul hs]
  field_simp
  ring

lemma riemannZeta₁_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta₁ s ≠ 0 := by
  intro h
  by_cases hs1 : s = 1
  · subst hs1
    simp at h
  · have hz := riemannZeta_ne_zero_of_one_le_re hs
    rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero] at hz
    exact hz rfl

theorem logDerivBoundedHeight : SmallHeightLogDeriv := by
  intro T
  have hK : IsCompact (Icc (1 : ℝ) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hU : IsOpen {s : ℂ | riemannZeta₁ s ≠ 0} :=
    isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const
  have hKU : Icc (1 : ℝ) 3 ×ℂ Icc (-T) T ⊆ {s : ℂ | riemannZeta₁ s ≠ 0} := fun s hs =>
    riemannZeta₁_ne_zero_of_one_le_re (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  have hne : ∀ s : ℂ, |s.im| ≤ T → 1 - δ / 2 ≤ s.re → s.re ≤ 3 → riemannZeta₁ s ≠ 0 := by
    intro s him hre hre3
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta₁_ne_zero_of_one_le_re h1
    · apply hδU
      rw [Metric.mem_thickening_iff]
      refine ⟨1 + s.im * I, ?_, ?_⟩
      · rw [Complex.mem_reProdIm]
        obtain ⟨h3, h4⟩ := abs_le.mp him
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp <;> linarith
      · rw [Complex.dist_eq]
        have hd : s - (1 + s.im * I) = ((s.re - 1 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
  refine ⟨δ / 2, ?_⟩
  have hKc : IsCompact (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (fun s => deriv riemannZeta₁ s / riemannZeta₁ s)
      (Icc (1 - δ / 2) 3 ×ℂ Icc (-T) T) := by
    apply ContinuousOn.div
    · exact ((differentiable_riemannZeta₁.differentiableOn.deriv isOpen_univ).continuousOn).mono
        (subset_univ _)
    · exact differentiable_riemannZeta₁.continuous.continuousOn
    · intro s hs
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hs
      exact hne s (abs_le.mpr ⟨h3, h4⟩) h1 h2
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, half_pos hδ, ?_⟩
  intro s hs him hre hre3
  rw [shld_identity hs (hne s him hre hre3)]
  exact hC s (Complex.mem_reProdIm.mpr ⟨⟨hre, hre3⟩, abs_le.mp him⟩)

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
section
open Complex ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace VonMangoldtMertensInequality

lemma re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, Complex.re_ofReal_mul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), Complex.exp_re]
  have hre : (Complex.log (n : ℂ)).re = Real.log n := by
    rw [Complex.log_re, Complex.norm_natCast]
  have him : (Complex.log (n : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.natCast_arg]
  simp only [Complex.mul_re, Complex.mul_im, hre, him, Complex.neg_re, Complex.neg_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [mul_assoc]
  congr 2
  · congr 1
    ring
  · rw [← Real.cos_neg]
    congr 1
    ring

lemma hasSum_re_L {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by
  have hs : 1 < ((σ : ℂ) + y * I).re := by simp [hσ]
  have h1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).LSeriesHasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div] at h1
  simpa only [Complex.reCLM_apply] using Complex.reCLM.hasSum h1

lemma comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
    0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [mul_nonneg ha (sq_nonneg (1 + Real.cos θ))]

end VonMangoldtMertensInequality

open VonMangoldtMertensInequality in
theorem mertensInequality : ThreeFourOne := by
  intro σ t hσ
  have h0 := hasSum_re_L hσ 0
  have h1 := hasSum_re_L hσ t
  have h2 := hasSum_re_L hσ (2 * t)
  have hs := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  have key := HasSum.nonneg (fun n => ?_) hs
  · have e0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = σ := by simp
    have e2 : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = σ + 2 * t * I := by push_cast; ring
    rw [e0, e2] at key
    exact key
  · by_cases hn : n = 0
    · subst hn
      simp [LSeries.term_zero]
    · rw [re_term_vonMangoldt hn, re_term_vonMangoldt hn, re_term_vonMangoldt hn]
      have ha : 0 ≤ Λ n * Real.exp (-σ * Real.log n) :=
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
      have hc := comb_nonneg _ (t * Real.log n) ha
      rw [zero_mul, Real.cos_zero, mul_one, show 2 * t * Real.log n = 2 * (t * Real.log n) by ring]
      linarith

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
section
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

private theorem closedBall_mem_nhds_of_mem_closedBall_lt {z₀ z : ℂ} {r R₁ : ℝ} (hR : R₁ < r)
    (hz : z ∈ Metric.closedBall z₀ R₁) : Metric.closedBall z₀ r ∈ 𝓝 z :=
  Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hR hz))
    Metric.ball_subset_closedBall

private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h

theorem exists_factorization_of_sum_order (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf hZ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, ?_, ?_⟩
    · intro z hz hfz
      have hzZ := hzero z hz hfz
      have han : AnalyticAt ℂ f z := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hz)
      have hord : analyticOrderAt f z = 0 := by
        rw [← natCast_analyticOrderNatAt_of_ne_top (htop z hzZ)]
        simp [h0 z hzZ]
      exact (han.analyticOrderAt_eq_zero.mp hord) hfz
    · intro z _
      rw [Finset.prod_eq_one (fun ρ hρ => by rw [h0 ρ hρ, pow_zero]), one_mul]
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hanρ₀ : AnalyticAt ℂ f ρ₀ := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := by
      by_contra hne
      apply hρ₀
      have h0 : analyticOrderAt f ρ₀ = 0 := hanρ₀.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0]
    obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = dslope f ρ₀ := ⟨_, rfl⟩
    have hfg : ∀ z, f z = (z - ρ₀) * g z := by
      intro z
      have h := sub_smul_dslope f ρ₀ z
      rw [hfρ₀, sub_zero, smul_eq_mul, ← hg] at h
      exact h.symm
    have hgd : DifferentiableOn ℂ g (Metric.closedBall z₀ r) := by
      rw [hg]
      exact (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)).mpr hf
    have hfeq : f = (fun z : ℂ => z - ρ₀) * g := funext fun z => hfg z
    have key : ∀ ρ ∈ Z,
        analyticOrderAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderAt g ρ := by
      intro ρ hρ
      have hB := hZ ρ hρ
      have hga : AnalyticAt ℂ g ρ := hgd.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hB)
      have hla : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ := analyticAt_id.sub analyticAt_const
      rw [hfeq, analyticOrderAt_mul hla hga]
      congr 1
      split_ifs with hρρ₀
      · rw [hρρ₀]
        have hl : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
        have h1 := (hl.analyticOrderAt_eq_natCast (n := 1)).mpr
          ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
        simpa using h1
      · exact hla.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρρ₀)
    have keyN : ∀ ρ ∈ Z,
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := by
      intro ρ hρ
      have hk := key ρ hρ
      have ht := htop ρ hρ
      have hgt : analyticOrderAt g ρ ≠ ⊤ := by
        intro h
        apply ht
        rw [hk, h]
        simp
      refine ⟨?_, hgt⟩
      have h1 : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
          (((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ : ℕ) : ℕ∞) := by
        rw [natCast_analyticOrderNatAt_of_ne_top ht, hk, Nat.cast_add,
          natCast_analyticOrderNatAt_of_ne_top hgt]
        split_ifs <;> simp
      exact_mod_cast h1
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, ((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ) :=
        Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', hρ₀Z, if_true] at hsum
      omega
    have hzg : ∀ z ∈ Metric.closedBall z₀ R₁, g z = 0 → z ∈ Z :=
      fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero])
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ hzg (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hone : ∏ ρ ∈ Z, (z - ρ) ^ (if ρ = ρ₀ then 1 else 0) = z - ρ₀ := by
      rw [Finset.prod_eq_single ρ₀ (fun b _ hb => by simp [hb]) (fun h => absurd hρ₀Z h)]
      simp
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      calc ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
          = ∏ ρ ∈ Z, ((z - ρ) ^ (if ρ = ρ₀ then 1 else 0) * (z - ρ) ^ analyticOrderNatAt g ρ) :=
            Finset.prod_congr rfl fun ρ hρ => by rw [(keyN ρ hρ).1, pow_add]
        _ = (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
            rw [Finset.prod_mul_distrib, hone]
    rw [hfg z, hhf z hz, hprod, mul_assoc]

theorem zeroFactorization : ZeroFactor := by
  intro f z₀ r R₁ hR₁ hR hf hf0
  have hr : 0 < r := hR₁.trans hR
  have hU : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hpre : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have hnotzero : ∀ x ∈ Metric.ball z₀ r, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := by
    intro x hx hev
    have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hev
    exact hf0 (hEq hz₀)
  have hisol : ∀ x ∈ Metric.ball z₀ r, ∀ᶠ w in 𝓝[≠] x, f w ≠ 0 := fun x hx =>
    ((hU x hx).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hnotzero x hx)
  have htop : ∀ x ∈ Metric.ball z₀ r, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hSsub : Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} ⊆ Metric.ball z₀ r :=
    fun x hx => Metric.closedBall_subset_ball hR hx.1
  have hScpt : IsCompact (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}) :=
    (isCompact_closedBall z₀ R₁).of_isClosed_subset
      ((hf.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_singleton)
      Set.inter_subset_left
  have hSdisc : DiscreteTopology (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} : Set ℂ) := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    refine Filter.inf_principal_eq_bot.mpr ?_
    filter_upwards [hisol x (hSsub hx)] with w hw hwS
    exact hw hwS.2
  have hfin : (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}).Finite := by
    exact hScpt.finite ⟨hSdisc⟩
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ r R₁ hR _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (Metric.closedBall_subset_ball hR ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, analyticOrderNatAt f, h, hmem, ?_, hhd, hh0, hhf⟩
  intro ρ hρ
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball : ρ ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hR hB
  have hne : analyticOrderAt f ρ ≠ 0 := fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp h0) hfρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← natCast_analyticOrderNatAt_of_ne_top (htop ρ hball)]
  simp [h0]

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
section
open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

open ComplexPowerDifferenceIntegral in
lemma norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  set σ := s.re with hσ

  have hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + 1 := by linarith
    have hA : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
    have hB : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hq : 0 < (x + 1) / x := div_pos hy0 hx0
    have hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ := Real.div_rpow hy0.le hx0.le σ
    have hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ := by
      rw [← hr, Real.rpow_def_of_pos hq]
      have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)
      have h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog hs.le
      linarith
    rw [Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    have e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹ := by ring
    have e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹ := by
      field_simp
    rw [mul_div_assoc', e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)
  have hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1)
      ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk := hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
      have hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      have e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ
          = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        field_simp
        ring
      linarith
  have hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
    intro n
    rcases n with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine (hS N).trans ?_
      have h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
  have hC : 0 ≤ ‖s - 1‖ * ‖s‖ := by positivity
  show ‖∑' n, dz s n‖ ≤ _
  calc ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := by
      refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_
      calc ∑ i ∈ Finset.range n, ‖dz s i‖
          ≤ ∑ i ∈ Finset.range n, ‖s - 1‖ * ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) :=
            Finset.sum_le_sum fun i _ => norm_dz_le hs i
        _ = ‖s - 1‖ * ‖s‖ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) := by
            rw [Finset.mul_sum]
        _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC

theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]
    ring
  have hD := norm_Dz_le hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 hne
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]
    field_simp
  rw [hz, norm_div, div_le_iff₀ hpos]
  have hs' : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa using norm_add_le (s - 1) 1
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := add_le_add hs' hD
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by
        field_simp

end Formalism.ZF
end
end

-- bundled from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoTermReNonneg
section
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_zero_re_lt {ρ : ℂ} {σ : ℝ} (hσ : 1 < σ) (h : riemannZeta ρ = 0) : ρ.re < σ := by
  by_contra hc
  push_neg at hc
  exact riemannZeta_ne_zero_of_one_lt_re (lt_of_lt_of_le hσ hc) h

lemma zfo_term_re_nonneg {z ρ : ℂ} (n : ℕ) (h : ρ.re < z.re) :
    0 ≤ ((n : ℂ) / (z - ρ)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (Complex.normSq_nonneg _)

lemma zfo_landau (hLL : LandauLocal) {σ τ M : ℝ} (hσ : 1 < σ) (hM : 1 ≤ M)
    (hdiff : DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)))
    (hbd : ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ M * ‖riemannZeta ((σ : ℂ) + τ * I)‖) :
    ∃ S : ℝ, 0 ≤ S ∧
      (-(deriv riemannZeta ((σ : ℂ) + τ * I) / riemannZeta ((σ : ℂ) + τ * I))).re
        ≤ 144 * Real.log M - S ∧
      ∀ β : ℝ, riemannZeta ((β : ℂ) + τ * I) = 0 → σ - β ≤ 1 / 6 → 1 / (σ - β) ≤ S := by
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; exact hσ)
  obtain ⟨Z, m, hZ, hm, -, hbound⟩ := hLL riemannZeta s (1 / 2) M (by norm_num) hM hdiff hs0 hbd
  have hZre : ∀ ρ ∈ Z, ρ.re < s.re := fun ρ hρ => by
    rw [hsre]; exact zfo_zero_re_lt hσ ((hZ ρ).1 hρ).2
  refine ⟨∑ ρ ∈ Z, ((m ρ : ℂ) / (s - ρ)).re,
    Finset.sum_nonneg (fun ρ hρ => zfo_term_re_nonneg _ (hZre ρ hρ)), ?_, ?_⟩
  · have hb := hbound s (Metric.mem_closedBall_self (by norm_num)) hs0
    have hw := (abs_le.1 ((Complex.abs_re_le_norm _).trans hb)).1
    rw [Complex.sub_re, Complex.re_sum] at hw
    rw [Complex.neg_re]
    have h72 : 72 * Real.log M / (1 / 2) = 144 * Real.log M := by ring
    linarith
  · intro β hβ hβσ
    set ρ : ℂ := (β : ℂ) + τ * I with hρ
    have hρre : ρ.re = β := by simp [hρ]
    have hβlt : β < σ := by
      have := zfo_zero_re_lt hσ hβ
      rwa [hρre] at this
    have hdiff' : s - ρ = ((σ - β : ℝ) : ℂ) := by
      rw [hs, hρ]; push_cast; ring
    have hρZ : ρ ∈ Z := by
      rw [hZ]
      refine ⟨?_, hβ⟩
      rw [Metric.mem_closedBall, dist_eq_norm, ← neg_sub, norm_neg, hdiff', Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hterm : ((m ρ : ℂ) / (s - ρ)).re = (m ρ : ℝ) / (σ - β) := by
      rw [hdiff', ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    calc 1 / (σ - β) ≤ (m ρ : ℝ) / (σ - β) :=
          (div_le_div_iff_of_pos_right (by linarith)).2 (by exact_mod_cast hm ρ hρZ)
      _ = ((m ρ : ℂ) / (s - ρ)).re := hterm.symm
      _ ≤ ∑ ρ' ∈ Z, ((m ρ' : ℂ) / (s - ρ')).re :=
          Finset.single_le_sum (f := fun ρ' => ((m ρ' : ℂ) / (s - ρ')).re)
            (fun ρ' hρ' => zfo_term_re_nonneg _ (hZre ρ' hρ')) hρZ

end Formalism.ZF
end
end

