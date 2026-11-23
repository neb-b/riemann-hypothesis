module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.Fub3
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp
open scoped Classical

private theorem fub3 {X Y Z : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [Countable Z]
    [MeasurableSingletonClass Z] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y × Z → ℂ)
    (hf : Integrable f (μ.prod (ν.prod Measure.count))) :
    ∫ p, f p ∂(μ.prod (ν.prod Measure.count)) = ∫ x, ∫ y, ∑' z, f (x, y, z) ∂ν ∂μ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  rw [integral_prod _ hx]
  refine integral_congr_ae ?_
  filter_upwards [hx.prod_right_ae] with y hy
  rw [integral_countable hy]
  simp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yEq :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.YEq := by
  intro E _ _ _ D W M N P φ hφ ph hph
  haveI := N.haar
  haveI : SigmaFinite N.μ := inferInstance
  obtain ⟨hp, hw, hint⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.yInt E D W M N P φ hφ
  obtain ⟨hc, K, hK, hB⟩ := UpperTheory.ConvolutionTheory.R2.Ff.wtBound ℚ ph
  obtain ⟨n, hn⟩ := hint K hK
  obtain ⟨B, hB⟩ := hB n
  obtain ⟨-, -, h1, h2, -⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.szLaws E D
  have hI : Integrable (fun y => ph.1 (pY D y) * φ.1 (el D y)) (mY D.δ N) := by
    refine (hn.norm.const_mul B).mono' ((hc.measurable.comp hp).mul hw).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ wt K n (pY D y) := by
      unfold wt
      split_ifs
      · positivity
      · exact le_rfl
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hB () trivial _) (norm_nonneg _)
  unfold mY at hI ⊢
  rw [fub3 _ _ _ hI]
  unfold fOn J1 UI mean ThOn
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  have hnu : nu ℚ (gl h * sZ D (z : IdeleGroup E)) = 1 := by
    have a := h1 (z : IdeleGroup E)
    have b := h2 h
    unfold nu at a b ⊢
    rw [map_mul, map_mul, a, b, one_mul]
  have hab : ab (1 : (A ℚ)ˣ) = 1 := by
    unfold ab
    have : IdeleGroup.ideleModule ℚ (1 : (A ℚ)ˣ) = 1 := map_one _
    rw [this]
    rfl
  simp only [el, pY]
  rw [tsum_mul_right]
  congr 1
  refine tsum_congr fun ξ => ?_
  rw [map_one, Module.End.one_apply, W.L_apply, hnu, hab]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.SwapInt
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem int_prod {Z P : Type} [MeasurableSpace Z] [MeasurableSpace P] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure P) [SFinite n] {F : Z × P → ℂ} (hF : Measurable F) {K : ℝ≥0∞} (hK : K < ⊤)
    (h : ∀ᵐ z ∂m, ∫⁻ p, ‖F (z, p)‖ₑ ∂n ≤ K) : Integrable F (m.prod n) := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hF.enorm.aemeasurable]
  refine (lintegral_mono_ae h).trans_lt ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top hK (measure_lt_top _ _)

private theorem swap_int {Z X T : Type} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace T] (m : Measure Z) [IsFiniteMeasure m]
    (n : Measure X) [SFinite n] (l : Measure T) [IsFiniteMeasure l] {c : X → ℂ} (hcm : Measurable c) (hc : Integrable c n)
    {G : (Z × X) × T → ℂ} (hG : Measurable G) {S : Set Z} (hS : ∀ᵐ z ∂m, z ∈ S) {B : ℝ}
    (hB : ∀ z ∈ S, ∀ y, c y ≠ 0 → ∀ g, ‖G ((z, y), g)‖ ≤ B) :
    ∫ z, ∫ y, c y * ∫ g, G ((z, y), g) ∂l ∂n ∂m = ∫ y, c y * ∫ z, ∫ g, G ((z, y), g) ∂l ∂m ∂n := by
  have h1 : StronglyMeasurable fun p : Z × X => ∫ g, G (p, g) ∂l := hG.stronglyMeasurable.integral_prod_right'
  have h2 : Integrable (fun p : Z × X => B * l.real Set.univ * ‖c p.2‖) (m.prod n) :=
    (hc.norm.comp_snd m).const_mul _
  have h3 : ∀ᵐ p : Z × X ∂(m.prod n), p.1 ∈ S :=
    Measure.QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst hS
  rw [integral_integral_swap]
  · refine integral_congr_ae (ae_of_all _ fun y => ?_)
    exact integral_const_mul _ _
  · refine h2.mono' (((hcm.comp measurable_snd).mul h1.measurable).aestronglyMeasurable) ?_
    filter_upwards [h3] with p hp
    by_cases h0 : c p.2 = 0
    · simp [Function.uncurry, h0]
    · simp only [Function.uncurry, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right
        (norm_integral_le_of_norm_le_const (ae_of_all _ fun g => hB p.1 hp p.2 h0 g)) (norm_nonneg _)

private theorem cont_em {E : Type} [Field E] [NumberField E] : Continuous (em E) := by
  have hM : Continuous ((AdeleBaseChange.adeleMap ℚ E).mapMatrix.toMonoidHom :
      Matrix (Fin 2) (Fin 2) (A ℚ) → Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap
  exact Continuous.units_map _ hM

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zAll :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZAll := by
  intro E _ _ _ D W M N P φ hφ j hj c hc hcs Ψ hΨ hΨc
  obtain ⟨hfin, hS, C, hC, hSC⟩ := zDom E
  obtain ⟨hm1, hm2, -⟩ := yInt E D W M N P φ hφ
  have hsZ : Continuous (sZ D) := (szLaws E D).2.1
  have hφc : Continuous φ.1 := (decE E P φ hφ).1.1
  have hone := zOne E D W M N P φ hφ j hj c hc hcs Ψ hΨc
  haveI := N.haar
  haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD ℚ M⟩
  haveI : IsFiniteMeasure ((normOneMeasure E).restrict (normOneFundamentalDomain E)) := ⟨by simpa using hfin⟩
  haveI : Countable (Orb D.δ) := inferInstance
  have hci : Integrable c N.μ := hc.integrable_of_hasCompactSupport hcs
  obtain ⟨B, hB⟩ := bddE E P φ hφ _ (hC.image hsZ)
  obtain ⟨B', hB'⟩ := bddE E P φ hφ _
    ((hC.prod hcs.isCompact).image (f := fun p : (A E)ˣ × G1 E => sZ D p.1 * gl p.2)
      ((hsZ.comp continuous_fst).mul (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)))
  have hI : Integrable (fun y => Ψ (pY D y) * φ.1 (el D y)) (mY D.δ N) := by
    refine int_prod _ _ ((hΨ.comp hm1).mul hm2) (K := ENNReal.ofReal B * M.μ M.D * ∫⁻ y, ‖c y‖ₑ ∂N.μ) ?_ ?_
    · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (UpperTheory.ConvolutionTheory.R2.M.volD ℚ M)) hci.2
    · filter_upwards [ae_restrict_mem hS] with z hz
      exact (hone z).1 B fun h => hB h _ ⟨_, hSC z hz, rfl⟩
  refine ⟨hI, ?_⟩
  have hG : Continuous fun p : (↥(IdeleGroup.normOneSubgroup E) × G1 E) × G1 ℚ =>
      φ.1 (em E (gl p.2) * sZ D (p.1.1 : IdeleGroup E) * gl p.1.2) :=
    hφc.comp (((cont_em.comp (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp continuous_snd)).mul
      (hsZ.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)))).mul
      (UpperTheory.ConvolutionTheory.R2.M.continuous_gl.comp (continuous_snd.comp continuous_fst)))
  have hsw := swap_int ((normOneMeasure E).restrict (normOneFundamentalDomain E)) N.μ (M.μ.restrict M.D) hc.measurable hci
    hG.measurable (ae_restrict_mem hS) (B := B') (fun z hz y hy g => by
      have h := hB' (j g) _ ⟨((z : IdeleGroup E), y), ⟨hSC z hz, subset_tsupport _ hy⟩, rfl⟩
      rwa [hj, ← mul_assoc] at h)
  unfold mY at hI ⊢
  rw [integral_prod _ hI]
  simp only [fun z => (hone z).2]
  exact hsw

end
end

