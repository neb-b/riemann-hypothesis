module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogGaussNormSupportFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

section General

variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

def gaussNormOf (f : MvPolynomial ι R) : ℝ :=
  let s : NNReal := f.support.sup fun m => ⟨w (f.coeff m), w.nonneg _⟩
  (s : ℝ)

theorem gaussNormOf_def (f : MvPolynomial ι R) :
    gaussNormOf w f = (((f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) : NNReal) : ℝ) :=
  rfl

theorem gaussNormOf_nonneg (f : MvPolynomial ι R) : 0 ≤ gaussNormOf w f := NNReal.coe_nonneg _

theorem le_gaussNormOf (f : MvPolynomial ι R) (m : ι →₀ ℕ) : w (f.coeff m) ≤ gaussNormOf w f := by
  by_cases hm : m ∈ f.support
  · have h : (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) ≤
        f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal) :=
      Finset.le_sup (f := fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) hm
    rw [gaussNormOf_def]
    exact NNReal.coe_le_coe.mpr h
  · rw [notMem_support_iff.mp hm, map_zero]
    exact gaussNormOf_nonneg w f

theorem gaussNormOf_le {f : MvPolynomial ι R} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, w (f.coeff m) ≤ r) : gaussNormOf w f ≤ r := by
  have h' : (f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) ≤ ⟨r, hr⟩ :=
    Finset.sup_le fun m _ => h m
  rw [gaussNormOf_def]
  exact NNReal.coe_le_coe.mpr h'

theorem exists_gaussNormOf_eq {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ m ∈ f.support, gaussNormOf w f = w (f.coeff m) := by
  obtain ⟨m, hm, h⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf)
    (fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal))
  refine ⟨m, hm, ?_⟩
  rw [gaussNormOf_def]
  exact congrArg Subtype.val h

theorem gaussNormOf_pos {f : MvPolynomial ι R} (hf : f ≠ 0) : 0 < gaussNormOf w f := by
  obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
  rw [h]
  exact w.pos (mem_support_iff.mp hm)

theorem gaussNormOf_zero : gaussNormOf w (0 : MvPolynomial ι R) = 0 :=
  le_antisymm (gaussNormOf_le w le_rfl fun m => by simp) (gaussNormOf_nonneg w 0)

theorem gaussNormOf_C (c : R) : gaussNormOf w (C c : MvPolynomial ι R) = w c := by
  classical
  apply le_antisymm
  · refine gaussNormOf_le w (w.nonneg c) fun m => ?_
    rw [coeff_C]
    split_ifs
    · exact le_rfl
    · rw [map_zero]
      exact w.nonneg c
  · simpa using le_gaussNormOf w (C c : MvPolynomial ι R) 0

variable {w}

theorem gaussNormOf_mul_le (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) ≤ gaussNormOf w f * gaussNormOf w g := by
  classical
  refine gaussNormOf_le w (mul_nonneg (gaussNormOf_nonneg w f) (gaussNormOf_nonneg w g)) fun m => ?_
  rw [coeff_mul]
  refine (hna.apply_sum_le_sup (s := Finset.HasAntidiagonal.antidiagonal m) ⟨(0, m), by simp⟩).trans ?_
  refine Finset.sup'_le _ _ fun p _ => ?_
  rw [map_mul]
  exact mul_le_mul (le_gaussNormOf w f _) (le_gaussNormOf w g _) (w.nonneg _)
    (gaussNormOf_nonneg w f)

theorem le_gaussNormOf_mul (hna : IsNonarchimedean w) {f g : MvPolynomial ι R} (hf : f ≠ 0)
    (hg : g ≠ 0) : gaussNormOf w f * gaussNormOf w g ≤ gaussNormOf w (f * g) := by
  classical
  let _ : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  have hNf := gaussNormOf_pos w hf
  have hNg := gaussNormOf_pos w hg
  obtain ⟨i, hi, hmin_i⟩ :=
    (f.support.filter fun a => w (f.coeff a) = gaussNormOf w f).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hf
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  obtain ⟨j, hj, hmin_j⟩ :=
    (g.support.filter fun a => w (g.coeff a) = gaussNormOf w g).exists_min_image toLex (by
      obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq w hg
      exact ⟨m, Finset.mem_filter.mpr ⟨hm, h.symm⟩⟩)
  have hi' : w (f.coeff i) = gaussNormOf w f := (Finset.mem_filter.mp hi).2
  have hj' : w (g.coeff j) = gaussNormOf w g := (Finset.mem_filter.mp hj).2
  have ltf : ∀ a, toLex a < toLex i → w (f.coeff a) < gaussNormOf w f := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w f a) fun h => ?_
    have ha' : a ∈ f.support.filter fun a => w (f.coeff a) = gaussNormOf w f := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNf.ne h
    exact absurd (hmin_i a ha') (not_le.mpr ha)
  have ltg : ∀ a, toLex a < toLex j → w (g.coeff a) < gaussNormOf w g := by
    intro a ha
    refine lt_of_le_of_ne (le_gaussNormOf w g a) fun h => ?_
    have ha' : a ∈ g.support.filter fun a => w (g.coeff a) = gaussNormOf w g := by
      refine Finset.mem_filter.mpr ⟨mem_support_iff.mpr fun h0 => ?_, h⟩
      rw [h0, map_zero] at h
      exact hNg.ne h
    exact absurd (hmin_j a ha') (not_le.mpr ha)
  have key : w ((f * g).coeff (i + j)) = gaussNormOf w f * gaussNormOf w g := by
    rw [coeff_mul]
    have hk : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [hna.apply_sum_eq_of_lt _ (fun a => w.map_neg a) hk ?_, map_mul, hi', hj']
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [map_mul, map_mul, hi', hj']
    rcases lt_trichotomy (toLex p.1) (toLex i) with h | h | h
    · calc w (f.coeff p.1) * w (g.coeff p.2) ≤ w (f.coeff p.1) * gaussNormOf w g :=
            mul_le_mul_of_nonneg_left (le_gaussNormOf w g _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_right (ltf _ h) hNg
    · have h1 : p.1 = i := toLex.injective h
      have h2 : p.2 = j := by
        rw [h1] at hp
        exact add_left_cancel hp
      exact absurd (Prod.ext h1 h2) hne
    · have h2 : toLex p.2 < toLex j := by
        by_contra hc
        rw [not_lt] at hc
        have hlt : toLex i + toLex j < toLex p.1 + toLex p.2 := add_lt_add_of_lt_of_le h hc
        have e : toLex p.1 + toLex p.2 = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hp]
        rw [e] at hlt
        exact lt_irrefl _ hlt
      calc w (f.coeff p.1) * w (g.coeff p.2) ≤ gaussNormOf w f * w (g.coeff p.2) :=
            mul_le_mul_of_nonneg_right (le_gaussNormOf w f _) (w.nonneg _)
        _ < gaussNormOf w f * gaussNormOf w g := mul_lt_mul_of_pos_left (ltg _ h2) hNf
  rw [← key]
  exact le_gaussNormOf w _ _

theorem gaussNormOf_mul (hna : IsNonarchimedean w) (f g : MvPolynomial ι R) :
    gaussNormOf w (f * g) = gaussNormOf w f * gaussNormOf w g := by
  by_cases hf : f = 0
  · simp [hf, gaussNormOf_zero]
  by_cases hg : g = 0
  · simp [hg, gaussNormOf_zero]
  exact le_antisymm (gaussNormOf_mul_le hna f g) (le_gaussNormOf_mul hna hf hg)

end General

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_eq_gaussNormOf (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) :
    gaussNorm v f = gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) f := rfl

theorem gaussNorm_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f g : MvPolynomial ι K) : gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g :=
  gaussNormOf_mul (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v) f g

theorem gaussNorm_C (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K) :
    gaussNorm v (C c : MvPolynomial ι K) = NumberField.HeightOneSpectrum.adicAbv K v c :=
  gaussNormOf_C _ c

theorem gaussNorm_C_mul (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K)
    (f : MvPolynomial ι K) :
    gaussNorm v (C c * f) = NumberField.HeightOneSpectrum.adicAbv K v c * gaussNorm v f := by
  rw [gaussNorm_mul, gaussNorm_C]

theorem gaussNorm_nonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) : 0 ≤ gaussNorm v f := gaussNormOf_nonneg _ f

theorem gaussNorm_pos (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    {f : MvPolynomial ι K} (hf : f ≠ 0) : 0 < gaussNorm v f := gaussNormOf_pos _ hf

theorem adicAbv_mulSupport_finite {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x).Finite := by
  have h := FinitePlace.hasFiniteMulSupport hx
  have e : (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x) =
      FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        (Function.mulSupport fun w : FinitePlace K => w x) := by
    ext v
    simp only [Function.mem_mulSupport, Set.mem_preimage,
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e]
  exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h

theorem log_gaussNorm_support_finite {ι : Type*} {f : MvPolynomial ι K} (hf : f ≠ 0) :
    (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (gaussNorm v f)).Finite := by
  classical
  refine (Set.Finite.biUnion (s := (f.support : Set (ι →₀ ℕ))) f.support.finite_toSet
    fun m hm => adicAbv_mulSupport_finite (K := K) (mem_support_iff.mp hm)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  by_contra hc
  simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hc
  apply hv
  have h1 : gaussNorm v f = 1 := by
    apply le_antisymm
    · refine gaussNormOf_le _ zero_le_one fun m => ?_
      by_cases hm : m ∈ f.support
      · exact (hc m hm).le
      · rw [notMem_support_iff.mp hm, map_zero]
        exact zero_le_one
    · obtain ⟨m, hm, h⟩ := exists_gaussNormOf_eq (NumberField.HeightOneSpectrum.adicAbv K v) hf
      rw [gaussNorm_eq_gaussNormOf, h, hc m hm]
  rw [h1, Real.log_one]

end NumberField

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntCircle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace LogInt

theorem lintegral_abs_log_circle_le (P : Polynomial ℂ) (D d0 : ℕ) (M : ℝ)
    (hD : P.natDegree ≤ D) (hd0 : P.coeff d0 ≠ 0)
    (hM : ∀ θ : ℝ, ‖P.eval (circleMap 0 1 θ)‖ ≤ M) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖P.eval (circleMap 0 1 θ)‖‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 +
        2 * Real.pi * |Real.log ‖P.coeff d0‖|) := by
  set G : ℝ → ℝ := fun θ => Real.log ‖P.eval (circleMap 0 1 θ)‖ with hGdef
  have hP : P ≠ 0 := fun h => hd0 (by simp [h])
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hii : IntervalIntegrable G volume 0 (2 * Real.pi) := Polynomial.intervalIntegrable_mahlerMeasure P
  have hint : IntegrableOn G (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi).mp hii
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  apply ENNReal.ofReal_le_ofReal
  set L := Real.log (max M 1) with hL
  have hpos : ∀ θ, G θ ≤ L := by
    intro θ
    by_cases h0 : ‖P.eval (circleMap 0 1 θ)‖ = 0
    · simp only [hGdef, h0, Real.log_zero]; exact Real.log_nonneg (le_max_right _ _)
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        ((hM θ).trans (le_max_left _ _))
  have hnorm : ∀ θ, ‖G θ‖ = 2 * max (G θ) 0 - G θ := by
    intro θ; rw [Real.norm_eq_abs]; rcases le_total (G θ) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  have hmaxint : IntegrableOn (fun θ => max (G θ) 0) (Ioc 0 (2 * Real.pi)) := hint.pos_part
  have e1 : ∫ θ in Ioc 0 (2 * Real.pi), ‖G θ‖ =
      2 * (∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0) - ∫ θ in Ioc 0 (2 * Real.pi), G θ := by
    rw [show (fun θ => ‖G θ‖) = fun θ => 2 * max (G θ) 0 - G θ from funext hnorm]
    rw [integral_sub (hmaxint.const_mul 2) hint, integral_const_mul]
  have e2 : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ 2 * Real.pi * L := by
    have : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ ∫ θ in Ioc 0 (2 * Real.pi), L := by
      refine setIntegral_mono_on hmaxint (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_
      intro θ _
      exact max_le (hpos θ) (Real.log_nonneg (le_max_right _ _))
    refine this.trans (le_of_eq ?_)
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, Real.pi_pos.le, smul_eq_mul]
  have e3 : ∫ θ in Ioc 0 (2 * Real.pi), G θ = 2 * Real.pi * P.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, ← intervalIntegral.integral_of_le h2pi]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have e4 : Real.log ‖P.coeff d0‖ - D * Real.log 2 ≤ P.logMahlerMeasure := by
    have hc := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d0 P
    have hm := Polynomial.mahlerMeasure_pos_of_ne_zero hP
    have hch : ((P.natDegree.choose d0 : ℕ) : ℝ) ≤ 2 ^ D := by
      have := (Nat.choose_le_two_pow P.natDegree d0).trans (Nat.pow_le_pow_right (by norm_num) hD)
      exact_mod_cast this
    have h1 : ‖P.coeff d0‖ ≤ 2 ^ D * P.mahlerMeasure :=
      hc.trans (mul_le_mul_of_nonneg_right hch hm.le)
    have h2 := Real.log_le_log (norm_pos_iff.mpr hd0) h1
    rw [Real.log_mul (by positivity) hm.ne', Real.log_pow] at h2
    rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
    linarith
  rw [e1, e3]
  have h5 := neg_abs_le (Real.log ‖P.coeff d0‖)
  have h6 := mul_le_mul_of_nonneg_left e4 h2pi
  have h7 := mul_le_mul_of_nonneg_left h5 h2pi
  linarith [e2, h6, h7]

theorem countable_circleMap_eq (ρ : ℂ) : {θ : ℝ | circleMap 0 1 θ = ρ}.Countable := by
  by_cases h : ∃ θ0, circleMap 0 1 θ0 = ρ
  · obtain ⟨θ0, h0⟩ := h
    refine (Set.countable_range (fun n : ℤ => θ0 + n * (2 * Real.pi))).mono ?_
    intro θ hθ
    simp only [mem_ofPred_eq, circleMap_zero, Complex.ofReal_one, one_mul] at hθ h0
    rw [← h0, Complex.exp_eq_exp_iff_exists_int] at hθ
    obtain ⟨n, hn⟩ := hθ
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    simp only
    linarith
  · push Not at h
    simp [h]

theorem countable_eval_circleMap_eq_zero (P : Polynomial ℂ) (hP : P ≠ 0) :
    {θ : ℝ | P.eval (circleMap 0 1 θ) = 0}.Countable := by
  have hsub : {θ : ℝ | P.eval (circleMap 0 1 θ) = 0} ⊆
      ⋃ ρ ∈ P.roots.toFinset, {θ : ℝ | circleMap 0 1 θ = ρ} := by
    intro θ hθ
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨circleMap 0 1 θ, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]; exact hθ, rfl⟩
  exact ((P.roots.toFinset.countable_toSet).biUnion fun ρ _ => countable_circleMap_eq ρ).mono hsub

theorem setLIntegral_rot {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (G : V → ENNReal) (hG : Measurable G) :
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ u in S, G u ∂μ =
      ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), G (R θ u)) ∂μ := by
  have h1 : ∀ θ, ∫⁻ u in S, G (R θ u) ∂μ = ∫⁻ u in S, G u ∂μ := by
    intro θ
    have := (hpres θ).setLIntegral_comp_preimage hS hG
    rwa [hinv θ] at this
  rw [lintegral_lintegral_swap]
  · simp_rw [h1]
    rw [setLIntegral_const]
    simp [Real.volume_Ioc, mul_comm]
  · exact (hG.comp (hR.comp measurable_swap)).aemeasurable

theorem circle_lemma {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (F : V → ℂ) (hF : Measurable F) (c : ℕ → V → ℂ) (D d0 : ℕ) (hd0 : d0 ≤ D)
    (hexp : ∀ θ u, F (R θ u) = ∑ d ∈ Finset.range (D + 1), c d u * circleMap 0 1 θ ^ d)
    (hint : IntegrableOn (fun u => Real.log ‖c d0 u‖) S μ)
    (hnz : ∀ᵐ u ∂(μ.restrict S), c d0 u ≠ 0)
    (M : ℝ) (hM : ∀ u ∈ S, ‖F u‖ ≤ M) :
    IntegrableOn (fun u => Real.log ‖F u‖) S μ ∧ ∀ᵐ u ∂(μ.restrict S), F u ≠ 0 := by
  classical

  set P : V → Polynomial ℂ := fun u =>
    ∑ d ∈ Finset.range (D + 1), Polynomial.C (c d u) * Polynomial.X ^ d with hPdef
  have hPeval : ∀ θ u, (P u).eval (circleMap 0 1 θ) = F (R θ u) := by
    intro θ u
    rw [hexp, hPdef, Polynomial.eval_finsetSum]
    simp
  have hPcoeff : ∀ u, (P u).coeff d0 = c d0 u := by
    intro u
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single d0]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd0)) h
  have hPdeg : ∀ u, (P u).natDegree ≤ D := by
    intro u
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
  have hRS : ∀ θ u, u ∈ S → R θ u ∈ S := by
    intro θ u hu
    have : u ∈ R θ ⁻¹' S := by rw [hinv θ]; exact hu
    exact this
  have hFm : Measurable fun u => Real.log ‖F u‖ := Real.measurable_log.comp hF.norm
  refine ⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩
  ·
    set K : ℝ := 4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 with hK
    have hbound : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ ≤
          ENNReal.ofReal (K + 2 * Real.pi * |Real.log ‖c d0 u‖|) := by
      filter_upwards [hnz, ae_restrict_mem hS] with u hu huS
      have := lintegral_abs_log_circle_le (P u) D d0 M (hPdeg u) (by rw [hPcoeff]; exact hu)
        (fun θ => by rw [hPeval]; exact hM _ (hRS θ u huS))
      have e : (fun θ => ‖Real.log ‖F (R θ u)‖‖ₑ) =
          fun θ => ‖Real.log ‖(P u).eval (circleMap 0 1 θ)‖‖ₑ := by
        funext θ; rw [hPeval]
      rw [e, ← hPcoeff u]
      exact this
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv (fun u => ‖Real.log ‖F u‖‖ₑ)
      (hFm.enorm)
    have hKint : Integrable (fun u => K + 2 * Real.pi * |Real.log ‖c d0 u‖|) (μ.restrict S) := by
      have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSfin
      exact (integrable_const K).add (hint.abs.const_mul _)
    have hlt : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ) ∂μ < ⊤ :=
      (lintegral_mono_ae hbound).trans_lt hKint.lintegral_lt_top
    rw [← hrot] at hlt
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have := (ENNReal.mul_lt_top_iff.mp hlt)
    rcases this with ⟨-, h⟩ | h | h
    · exact h
    · exact absurd h h2
    · change ∫⁻ u in S, ‖Real.log ‖F u‖‖ₑ ∂μ < ⊤
      rw [h]; exact ENNReal.zero_lt_top
  ·
    have hZ : MeasurableSet {u | F u = 0} := hF (measurableSet_singleton 0)
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv ({u | F u = 0}.indicator 1)
      (measurable_one.indicator hZ)
    have hinner : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u) = 0 := by
      filter_upwards [hnz] with u hu
      have hPu : P u ≠ 0 := fun h => hu (by rw [← hPcoeff, h]; simp)
      have hc := countable_eval_circleMap_eq_zero (P u) hPu
      have : (fun θ => {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) =
          {θ : ℝ | (P u).eval (circleMap 0 1 θ) = 0}.indicator 1 := by
        funext θ
        simp only [Set.indicator, mem_ofPred_eq, hPeval, Pi.one_apply]
      rw [this, lintegral_indicator_one hc.measurableSet]
      exact hc.measure_zero _
    have h0 : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi),
        {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) ∂μ = 0 := by
      rw [lintegral_congr_ae hinner, lintegral_zero]
    rw [h0, lintegral_indicator_one hZ] at hrot
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have h3 := (mul_eq_zero.mp hrot).resolve_left h2
    rw [ae_iff]
    simpa using h3

end LogInt

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInj.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F) (g : F → ℝ≥0∞),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A → Measurable g →
        ∫⁻ y in f '' A, g y ∂(μH[(k : ℝ)]) =
          ∫⁻ x in A, g (f x) * ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F))
            ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsAreaFormulaInjSet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

def AreaFormulaInjSet.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k →
    ∀ (U A : Set E) (f : E → F),
      IsOpen U → ContDiffOn ℝ 1 f U → A ⊆ U → MeasurableSet A → Set.InjOn f A →
        μH[(k : ℝ)] (f '' A) =
          ∫⁻ x in A, ENNReal.ofReal (areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)])

end GroundTheory.Heights₂.Heights
end
end

