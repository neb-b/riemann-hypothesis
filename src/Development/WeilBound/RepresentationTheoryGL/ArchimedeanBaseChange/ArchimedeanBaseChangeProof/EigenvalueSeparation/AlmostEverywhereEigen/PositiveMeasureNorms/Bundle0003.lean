module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Specmeas
section
noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Specmeas

variable {X : Type} [TopologicalSpace X]

def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩

@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl

lemma ofR_add (g h : C(X, ℝ)) : ofR (g + h) = ofR g + ofR h := by
  ext x; simp

lemma ofR_sub (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x; simp

lemma ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by
  ext x; simp

def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

lemma eq_ofR_re_add_im (f : C(X, ℂ)) : f = ofR (reC f) + Complex.I • ofR (imC f) := by
  ext x
  simp [reC, imC, mul_comm Complex.I, Complex.re_add_im]

section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

lemma nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  let s : C(X, ℝ) := ⟨fun x => Real.sqrt (g x), by fun_prop⟩
  have : ofR g = star (ofR s) * ofR s := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, s,
      ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [this]; exact hΛ _

lemma im_ofR (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  let p : C(X, ℝ) := ⟨fun x => max (g x) 0, by fun_prop⟩
  let n : C(X, ℝ) := ⟨fun x => max (-g x) 0, by fun_prop⟩
  have hg : g = p - n := by
    ext x
    simp only [p, n, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp := nonneg_ofR Λ hΛ (g := p) (fun x => le_max_right _ _)
  have hn := nonneg_ofR Λ hΛ (g := n) (fun x => le_max_right _ _)
  rw [Complex.le_def] at hp hn
  rw [hg, ofR_sub, map_sub, Complex.sub_im, ← hp.2, ← hn.2]; simp

lemma ofR_eq_re (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  apply Complex.ext <;> simp [im_ofR Λ hΛ g]

end

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem exists_measure_of_positive (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.Regular ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let Λr : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := (Λ (ofR g.toContinuousMap)).re
    map_add' g g' := by
      have : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := rfl
      rw [this, ofR_add, map_add (f := _), Complex.add_re]
    map_smul' c g := by
      have : (c • g).toContinuousMap = c • g.toContinuousMap := rfl
      rw [this, ofR_smul, map_smul]; simp
    monotone' g g' hgg' := by
      have h := nonneg_ofR Λ hΛ (g := g'.toContinuousMap - g.toContinuousMap)
        (fun x => sub_nonneg.2 (hgg' x))
      rw [ofR_sub, map_sub, Complex.le_def] at h
      have := h.1
      simp only [Complex.zero_re, Complex.sub_re] at this
      linarith }
  refine ⟨RealRMK.rieszMeasure Λr, inferInstance, inferInstance, fun f => ?_⟩
  have key : ∀ g : C(X, ℝ), Λ (ofR g) = ((∫ x, g x ∂(RealRMK.rieszMeasure Λr) : ℝ) : ℂ) := by
    intro g
    have := RealRMK.integral_rieszMeasure Λr (CompactlySupportedContinuousMap.continuousMapEquiv g)
    rw [ofR_eq_re Λ hΛ g]
    congr 1
    exact this.symm
  have hint : Integrable (fun x => f x) (RealRMK.rieszMeasure Λr) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add (f := _), map_smul, key, key, ← integral_re_add_im hint, smul_eq_mul, mul_comm]
  rfl

end PositivityTheory.Rg.BcB.E2.P.Specmeas

namespace PositivityTheory.Rg.BcB.E2.P

theorem specmeas : SpecMeas := by
  intro K _ _ _ S _ _ _ _ _ π v
  let Λ : C(S, ℂ) →ₗ[ℂ] ℂ :=
  { toFun f := inner ℂ v (π f v)
    map_add' f g := by simp [map_add (f := _)]
    map_smul' c f := by simp }
  have hΛ : ∀ f : C(S, ℂ), 0 ≤ Λ (star f * f) := by
    intro f
    show 0 ≤ inner ℂ v (π (star f * f) v)
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (π f v))) 2
  obtain ⟨ν, h1, h2, h3⟩ := Specmeas.exists_measure_of_positive Λ hΛ
  exact ⟨ν, h1, h2, fun f => (h3 f).symm⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Tonelli
section
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Tonelli

theorem enorm_sq {S : Type} [MeasurableSpace S] {ν : Measure S} (g : Lp ℂ 2 ν) :
    ‖g‖ₑ ^ 2 = ∫⁻ s, ‖(g : S → ℂ) s‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  · norm_num
  · exact Lp.aestronglyMeasurable g

end PositivityTheory.Rg.BcB.E2.P.Tonelli

namespace PositivityTheory.Rg.BcB.E2.P

theorem tonelli : Tonelli := by
  intro Y S _ _ m _ ν _ F f W hf hW hfin
  have hmeas : Measurable (Function.uncurry fun y s => W y * ‖f y s‖ₑ ^ 2) :=
    (hW.comp measurable_fst).mul (hf.1.enorm.pow_const 2)
  refine ae_lt_top hmeas.lintegral_prod_left' ?_
  rw [← lintegral_lintegral_swap hmeas.aemeasurable]
  refine ne_of_eq_of_ne (lintegral_congr fun y => ?_) hfin
  have hy : Measurable fun s => f y s := hf.1.comp measurable_prodMk_left
  rw [lintegral_const_mul _ (hy.enorm.pow_const 2), Tonelli.enorm_sq]
  congr 1
  exact lintegral_congr_ae ((hf.2 y).mono fun s hs => by simp only [hs])

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Unfold
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P.Unfold

theorem unfolded (hk : KerBasic) (X : Ctx) (φ u : X.G → ℂ) (hφ : Tst φ) (hu : Continuous u)
    (hinv : ∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) (x : X.G) :
    ∫ y, ker X.Γ φ x y * u y ∂X.ν = ∫ y, φ y * u (x * y) ∂X.μ := by
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set g : X.G → ℂ := fun z => φ (x⁻¹ * z) * u z with hg
  have hgc : Continuous g := (hφ.1.comp (continuous_const.mul continuous_id)).mul hu
  have hgs : HasCompactSupport g :=
    HasCompactSupport.mul_right (hφ.2.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hgi : Integrable g X.μ := hgc.integrable_of_hasCompactSupport hgs
  have hpt : ∀ z, ker X.Γ φ x z * u z = ∑' γ : X.Γ, g (γ • z) := by
    intro z
    have h1 : ∀ γ : X.Γ, g (γ • z) = φ (x⁻¹ * (γ : X.G) * z) * u z := by
      intro γ
      have h2 : γ • z = (γ : X.G) * z := rfl
      simp only [hg, h2, hinv γ γ.2 z, mul_assoc]
    simp only [h1]
    rw [tsum_mul_right, ker, tsum_eq_finsum ((hk X φ hφ).1 x z)]
  have hmeas : ∀ γ : X.Γ, Continuous fun z => g (γ • z) := fun γ =>
    hgc.comp (continuous_const.mul continuous_id)
  have hfin : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν ≠ ⊤ := by
    have h3 : ∑' γ : X.Γ, ∫⁻ z, ‖g (γ • z)‖ₑ ∂X.ν = ∫⁻ z, ‖g z‖ₑ ∂X.μ :=
      (X.fd.lintegral_eq_tsum'' fun z => ‖g z‖ₑ).symm
    rw [h3]
    exact hgi.2.ne
  simp only [hpt]
  rw [integral_tsum (fun γ => (hmeas γ).aestronglyMeasurable) hfin]
  refine (X.fd.integral_eq_tsum'' g hgi).symm.trans ?_
  rw [← integral_mul_left_eq_self g x]
  simp [hg]

end PositivityTheory.Rg.BcB.E2.P.Unfold

namespace PositivityTheory.Rg.BcB.E2.P

theorem unfold : KerBasic → ConvCont → Unfold := by
  intro hk hc X φ u hφ hu hinv
  exact ⟨fun x => Unfold.unfolded hk X φ u hφ hu hinv x, hc X φ u hφ hu.locallyIntegrable⟩

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Weakae
section
open MeasureTheory
open scoped ENNReal ComplexConjugate

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Weakae

variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]

theorem lint_slice (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F) :
    ∫⁻ s, ‖f s‖ₑ ∂ν ≤ ‖F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_one_eq_lintegral_eNorm ((Lp.aestronglyMeasurable F).congr hf.symm),
    eLpNorm_congr_ae hf, Lp.enorm_def]
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν) (f := (F : S → ℂ))
    (by norm_num) (Lp.aestronglyMeasurable F)
  convert this using 3
  norm_num

theorem integrable_k (m : Measure Y) [SFinite m] (ν : Measure S) [IsFiniteMeasure ν]
    (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (c : Y → ℂ) (hf : IsRep F f) (hc : AEStronglyMeasurable c m)
    (hint : ∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m ≠ ⊤) :
    Integrable (fun p : Y × S => c p.1 * conj (f p.1 p.2)) (m.prod ν) := by
  have hcm : AEStronglyMeasurable (fun p : Y × S => c p.1) (m.prod ν) := hc.comp_fst
  have hfm : AEStronglyMeasurable (fun p : Y × S => conj (f p.1 p.2)) (m.prod ν) :=
    (Complex.continuous_conj.measurable.comp hf.1).aestronglyMeasurable
  refine ⟨hcm.mul hfm, ?_⟩
  show ∫⁻ p, ‖c p.1 * conj (f p.1 p.2)‖ₑ ∂(m.prod ν) < ⊤
  have hm : AEMeasurable (fun p : Y × S => ‖c p.1 * conj (f p.1 p.2)‖ₑ) (m.prod ν) :=
    (hcm.mul hfm).enorm
  rw [lintegral_prod _ hm]
  have hC : ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _)
  calc ∫⁻ y, ∫⁻ s, ‖c (y, s).1 * conj (f (y, s).1 (y, s).2)‖ₑ ∂ν ∂m
      = ∫⁻ y, ‖c y‖ₑ * ∫⁻ s, ‖f y s‖ₑ ∂ν ∂m := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun s => ?_
        simp [enorm_mul]
    _ ≤ ∫⁻ y, ‖c y‖ₑ * (‖F y‖ₑ * ν Set.univ ^ (1 / 2 : ℝ)) ∂m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact lint_slice ν (F y) (f y) (hf.2 y)
    _ = (∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m) * ν Set.univ ^ (1 / 2 : ℝ) := by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hint) (lt_top_iff_ne_top.2 hC)

theorem inner_ind (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F)
    (A : Set S) (hA : MeasurableSet A) (hνA : ν A ≠ ⊤) :
    inner ℂ F (indicatorConstLp 2 hA hνA (1 : ℂ)) = ∫ s in A, conj (f s) ∂ν := by
  rw [← inner_conj_symm, L2.inner_indicatorConstLp_one, integral_conj]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (hf.mono fun s hs => hs.symm))

end Weakae

open Weakae in
theorem weakae : WeakAE := by
  intro Y S ι _ _ _ m _ ν _ F f c q hf hc hint hq hw
  classical
  have hki : ∀ j, Integrable (fun p : Y × S => c j p.1 * conj (f j p.1 p.2)) (m.prod ν) := fun j =>
    integrable_k m ν (F j) (f j) (c j) (hf j) (hc j) (hint j)
  have hGj : ∀ j, Integrable (fun s => ∫ y, c j y * conj (f j y s) ∂m) ν := fun j =>
    (hki j).integral_prod_right
  have hG : Integrable (fun s => ∑ j, ∫ y, c j y * conj (f j y s) ∂m) ν :=
    integrable_finsetSum _ fun j _ => hGj j
  have hq' : Integrable q ν := hq.integrable (by norm_num)
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hq' fun A hA hνA => ?_
  have hR : ∫ s, q s * (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) s ∂ν = ∫ s in A, q s ∂ν := by
    rw [← integral_indicator hA]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hνA.ne) (c := (1 : ℂ))] with s hs
    rw [hs]
    by_cases h : s ∈ A <;> simp [h]
  rw [← hR, ← hw, integral_finsetSum _ fun j _ => (hGj j).integrableOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hres : m.prod (ν.restrict A) = (m.prod ν).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hkA : Integrable (Function.uncurry fun y s => c j y * conj (f j y s)) (m.prod (ν.restrict A)) := by
    rw [hres]; exact (hki j).restrict
  symm
  calc ∫ y, c j y * inner ℂ (F j y) (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) ∂m
      = ∫ y, ∫ s in A, c j y * conj (f j y s) ∂ν ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [inner_ind ν (F j y) (f j y) ((hf j).2 y) A hA hνA.ne, integral_const_mul]
    _ = ∫ s in A, ∫ y, c j y * conj (f j y s) ∂m ∂ν := integral_integral_swap hkA

end PositivityTheory.Rg.BcB.E2.P
end

