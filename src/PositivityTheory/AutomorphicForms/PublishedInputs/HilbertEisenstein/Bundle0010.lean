module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0006
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
public import GroundTheory.GlobalFields.TateThesis.Bundle0005
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import GroundTheory.GlobalFields.TateThesis.Bundle0002

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IsFiniteMeasureRestrictFd
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem integral_count_Xi (f : Xi F → ℂ) : ∫ ξ, f ξ ∂(Measure.count : Measure (Xi F)) = ∑' ξ, f ξ := by
  by_cases hf : Summable f
  · have hi : Integrable f (Measure.count : Measure (Xi F)) := by
      rw [integrable_count_iff]
      exact summable_norm_iff.mpr hf
    rw [integral_countable hi]
    simp [count_real_singleton]
  · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
    intro hi
    rw [integrable_count_iff] at hi
    exact hf (summable_norm_iff.mp hi)

theorem integral_iter_eq (S : Set {r : ℝ // 0 < r}) (hS : MeasurableSet S) {h : Pp F × Xi F → ℂ}
    (hh : Integrable h (μS F S)) :
    IntegrableOn (fun t => ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F)
        S posRealMeasure ∧
      ∫ t in S, ∫ u in normOneFundamentalDomain F, ∑' ξ : Xi F, h ((t, u), ξ) ∂normOneMeasure F
          ∂posRealMeasure = ∫ q, h q ∂μS F S := by
  have e1 : ∀ p : Pp F, ∫ ξ, h (p, ξ) ∂(Measure.count : Measure (Xi F)) = ∑' ξ : Xi F, h (p, ξ) :=
    fun p => integral_count_Xi _
  have hG : Integrable (fun p : Pp F => ∑' ξ : Xi F, h (p, ξ))
      ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))) := by
    have := hh.integral_prod_left
    simp only [e1] at this
    exact this
  refine ⟨?_, ?_⟩
  · have := hG.integral_prod_left
    exact this
  · rw [μS, integral_prod _ hh]
    simp only [e1]
    rw [integral_prod _ hG]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.KernelMeasureBoundAndMeasurability
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding WithZero

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem finId_val' (yf : (Af F)ˣ) : ((finId F yf : (Ad F)ˣ) : Ad F) = (1, (yf : Af F)) := by
  change 1 - sFin F 1 + sFin F yf.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : Af F) - 1 + (yf : Af F) = _
    rw [sub_self, zero_add]

theorem exists_m {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      w.intValuation m ≤ exp (-((c w : ℤ) + dd w)) := by
  classical
  have hπ : ∀ w : HeightOneSpectrum (𝓞 F), ∃ x ∈ w.asIdeal, x ≠ 0 := fun w =>
    Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  choose π hπmem hπ0 using hπ
  obtain ⟨δ, hδmem, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  set S := hc.toFinset
  set p : 𝓞 F := ∏ w ∈ S, π w ^ c w
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hπ0 w)
  refine ⟨δ * p, mul_ne_zero hδ0 hp0, fun w => ?_⟩
  have hδv : w.intValuation δ ≤ exp (-dd w) := by
    have h := intValuation_le_of_mem_ideal w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) hδmem
    rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))] at h
    exact h
  have hpv : w.intValuation p ≤ exp (-(c w : ℤ)) := by
    refine (w.intValuation_le_pow_iff_mem p (c w)).2 ?_
    by_cases hw : w ∈ S
    · obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun w => π w ^ c w) hw
      rw [show p = π w ^ c w * q from hq]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hπmem w) _)
    · have : c w = 0 := by
        by_contra h
        exact hw (hc.mem_toFinset.2 h)
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  rw [map_mul, neg_add, add_comm (-(c w : ℤ)), exp_add]
  exact mul_le_mul' hδv hpv

theorem exp_neg_mul_le_one_iff (n : ℤ) (a : ℤᵐ⁰) : exp (-n) * a ≤ 1 ↔ a ≤ exp n := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [← exp_log ha, ← exp_add, ← exp_zero, exp_le_exp, exp_le_exp]
  omega

theorem isClosed_le_exp (w : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    IsClosed {z : w.adicCompletion F | Valued.v z ≤ exp n} := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer F
  have hπ0 : (π : w.adicCompletion F) ≠ 0 := by
    intro h
    have h' : Valued.v ((π : F) : w.adicCompletion F) = 0 := by rw [h, map_zero]
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ] at h'
    exact exp_ne_zero h'
  set u : w.adicCompletion F := (π : w.adicCompletion F) ^ n
  have hu : Valued.v u = exp (-n) := by
    rw [map_zpow₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ, ← exp_zsmul]
    congr 1
    simp
  have heq : {z : w.adicCompletion F | Valued.v z ≤ exp n} =
      (fun z => u * z) ⁻¹' {z : w.adicCompletion F | Valued.v z ≤ 1} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, hu, exp_neg_mul_le_one_iff]
  rw [heq]
  exact (Valued.isClopen_integer (w.adicCompletion F)).isClosed.preimage (continuous_const.mul continuous_id)

theorem continuous_pInf_apply (v : InfinitePlace F) : Continuous fun x : Ad F => UpperTheory.V.TR.pInf F x v := by
  simp only [L2.pInf_apply_eq]
  exact ((continuous_apply _).comp continuous_fst).comp ((homeomorphMixedSpace F).continuous.comp continuous_fst)

theorem isClosed_cond {X : Type*} [TopologicalSpace X] {f : X → Ad F} (hf : Continuous f) (n : HeightOneSpectrum (𝓞 F) → ℤ) :
    IsClosed {p | ∀ w, Valued.v (pLoc F w (pFin F (f p))) ≤ exp (n w)} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun w => (isClosed_le_exp w (n w)).preimage ?_
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp hf)

theorem measurable_kernF_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (c : HeightOneSpectrum (𝓞 F) → ℕ) {A Z : X → Ad F} (hA : Continuous A) (hZ : Continuous Z) :
    Measurable fun p => kernF c (A p) (Z p) := by
  classical
  unfold kernF
  refine Measurable.mul (Continuous.measurable ?_) (Measurable.ite ?_ (Continuous.measurable ?_) measurable_const)
  · refine continuous_finsetProd _ fun v _ => ?_
    have h1 : Continuous fun p => (UpperTheory.V.TR.pInf F (A p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hA)
    have h2 : Continuous fun p => (UpperTheory.V.TR.pInf F (Z p) v : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_pInf_apply v).comp hZ)
    exact (h1.add h2).mul (Complex.continuous_exp.comp (continuous_const.mul ((h1.pow 2).add (h2.pow 2))))
  · refine ((isClosed_cond hA fun w => -(c w : ℤ)).inter (isClosed_cond hZ fun w => (c w : ℤ) + dd w)).measurableSet
  · exact continuous_subtype_val.comp (continuous_finiteAdelicChar.comp (continuous_snd.comp hZ))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.VanishingLemma

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open VanishingLemma

theorem measure_bound_holds : P5mu := by
  intro F _ _ _ c hc
  obtain ⟨m, hm0, hmv⟩ := exists_m hc
  have hmF : ((m : 𝓞 F) : F) ≠ 0 := by
    simpa using hm0
  set mu : (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 _ hmF)
  refine ⟨finId F mu, fun Z => ?_, fun Z hZ => ?_⟩
  · rw [Units.smul_def, finId_val']
    change (1 : InfiniteAdeleRing F) * Z.1 = Z.1
    rw [one_mul]
  · rw [Units.smul_def, finId_val', mem_idealFiniteAdeles]
    intro w
    rw [Units.val_one, FractionalIdeal.count_one, neg_zero, exp_zero]
    change Valued.v ((((algebraMap (𝓞 F) F m : F)) : w.adicCompletion F) * Z.2 w) ≤ 1
    rw [map_mul, valued_coe_algebraMap]
    have h1 := hmv w
    have h2 := hZ w
    change Valued.v (Z.2 w) ≤ _ at h2
    calc w.intValuation m * Valued.v (Z.2 w) ≤ exp (-((c w : ℤ) + dd w)) * exp ((c w : ℤ) + dd w) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]

theorem measurability_holds : P5meas := by
  intro F _ _ _ c κ hκ Y ξ
  unfold coefK
  refine Measurable.tsum fun a => ?_
  have hτ : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 * diagonal F a :=
    (((continuous_moduleSection (w0 F)).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const
  simp only [kern, hκ]
  refine Measurable.mul (Continuous.measurable ?_) (measurable_const.mul ?_)
  · have hm : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
        ((IdeleGroup.ideleModule F (tau p.1 p.2 * diagonal F a) : {r : ℝ // 0 < r}) : ℝ) :=
      continuous_subtype_val.comp ((IdeleGroup.continuous_ideleModule (K := F)).comp hτ)
    exact (Complex.continuous_ofReal.comp hm).inv₀ fun p => Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule F _).2.ne'
  · refine measurable_kernF_comp c ?_ ?_
    · exact (Units.continuous_val.comp hτ).mul continuous_const
    · simp only [Units.smul_def]
      exact (Units.continuous_val.comp hτ.inv).mul continuous_const

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.MixedFourierArchSchwartz
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem mem_units_of_isUnitAt (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    x ∈ (Submonoid.ofClass (w.adicCompletionIntegers F)).units := by
  rw [Submonoid.mem_units_iff]
  have hx' : Valued.v (x : w.adicCompletion F) = 1 := hx
  refine ⟨?_, ?_⟩
  · change (x : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx']
  · change ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]

theorem integral_arch_one (a y : ℝ) :
    ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
        (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      ((a : ℂ) + (y : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) := by
  set c1 : ℂ := (a : ℂ) * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  set c2 : ℂ := Complex.I * Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2)
  have hpt : ∀ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) *
      (((a : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2))) =
      c1 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t) +
        c2 * (((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t) := by
    intro t
    simp only [c1, c2, realGaussian, realGaussianOdd]
    have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (t : ℂ) ^ 2)) =
        Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (t : ℂ) ^ 2) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this]
    ring
  have hce : Continuous fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))
  have hg : Continuous realGaussian := by unfold realGaussian; fun_prop
  have hgo : Continuous realGaussianOdd := by unfold realGaussianOdd; fun_prop
  have hi1 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t :=
    integrable_realGaussian.norm.mono' (hce.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hi2 : Integrable fun t : ℝ => ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t :=
    integrable_realGaussianOdd.norm.mono' (hce.mul hgo).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by rw [norm_mul, Circle.norm_coe, one_mul])
  have hf1 : 𝓕 realGaussian y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussian t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  have hf2 : 𝓕 realGaussianOdd y = ∫ t : ℝ, ((𝐞 (-(t * y)) : Circle) : ℂ) * realGaussianOdd t := by
    rw [Real.fourier_real_eq]; simp only [Circle.smul_def, smul_eq_mul]
  simp only [hpt]
  rw [integral_add (hi1.const_mul c1) (hi2.const_mul c2), integral_const_mul, integral_const_mul, ← hf1, ← hf2,
    fourier_realGaussian, fourier_realGaussianOdd]
  simp only [c1, c2, realGaussian, realGaussianOdd]
  have : Complex.exp (-(π : ℂ) * ((a : ℂ) ^ 2 + (y : ℂ) ^ 2)) =
      Complex.exp (-(π : ℂ) * (a : ℂ) ^ 2) * Complex.exp (-(π : ℂ) * (y : ℂ) ^ 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem mixedFourier_archSchwartz (a : InfinitePlace F → ℝ) (Z : Ad F) :
    mixedFourier F (archSchwartz a) (homeomorphMixedSpace F Z.1) =
      ∏ v, (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  set m := homeomorphMixedSpace F Z.1
  set A : ∀ w : {w : InfinitePlace F // IsReal w}, ℝ → ℂ := fun w t => ((𝐞 (-(t * m.1 w)) : Circle) : ℂ) *
    ((((a w.1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + (t : ℂ) ^ 2)))
  set B : ∀ w : {w : InfinitePlace F // IsComplex w}, ℂ → ℂ := fun _ _ => 1
  have hint : ∀ x : mixedSpace F, 𝐞 (-mixedTraceForm F x m) • archSchwartz a x =
      (∏ w, A w (x.1 w)) * ∏ w, B w (x.2 w) := by
    intro x
    rw [Circle.smul_def, smul_eq_mul, HeckeCharacter.fourierChar_neg_mixedTraceForm, archSchwartz_eq_prod]
    simp only [A, B, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty,
      mul_one, Finset.prod_mul_distrib]
  have hA : ∀ w : {w : InfinitePlace F // IsReal w}, ∫ t, A w t =
      (((a w.1 : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z w.1 : ℝ) : ℂ) ^ 2)) :=
    fun w => integral_arch_one (a w.1) (m.1 w)
  rw [mixedFourier_apply, selfDualMeasure, integral_smul_measure, Measure.volume_eq_prod]
  simp only [hint]
  rw [integral_prod_mul (f := fun x : {w : InfinitePlace F // IsReal w} → ℝ ↦ ∏ w, A w (x w))
    (g := fun z : {w : InfinitePlace F // IsComplex w} → ℂ ↦ ∏ w, B w (z w)),
    integral_fintype_prod_volume_eq_prod, integral_fintype_prod_volume_eq_prod]
  simp only [hA, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}), Finset.prod_empty, mul_one,
    IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, ENNReal.toReal_one, one_smul]
  exact prod_real (fun v => (((a v : ℝ) : ℂ) + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F Z v : ℝ) : ℂ) ^ 2)))

theorem adelicFourier_slice {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A Z : Ad F) :
    adelicFourier F (slice c A) Z =
      ((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ) * kernF c A Z := by
  classical
  rw [slice_eq hc A, adelicFourier_smul, Pi.smul_apply, adelicFourier_schwartzBruhatTensor, schwartzBruhatTensor,
    mixedFourierSchwartz_apply, finiteFourier_cosetIndicator, mixedFourier_archSchwartz, smul_eq_mul, one_mul]
  unfold kernF
  rw [Set.indicator_apply]
  simp only [SetLike.mem_coe, Pi.one_apply]
  rw [mem_dual_iff hc]
  have hZ : Z.2 = pFin F Z := rfl
  rw [hZ]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)
    · simp only [h1, h2, and_self, implies_true, ↓reduceIte]; ring
    · simp only [h1, h2, implies_true, true_and, ↓reduceIte]; ring
  · simp only [h1, false_and, ↓reduceIte]; ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

theorem finite_expansion_holds : SFin := by
  intro F _ _ _ ω c H
  set χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* ℂˣ := ω.1.comp IdeleGroup.ofFinite with hχdef
  have hχ : Continuous χ := ω.2.1.comp IdeleGroup.continuous_ofFinite
  refine (IdeleGroup.finite_support_conductorExponentAt Complex.units_noSmallSubgroups χ hχ).subset ?_
  intro w hw
  rw [Function.mem_support]
  intro h0
  apply hw
  have hk := (IdeleGroup.conductorExponentAt_eq_zero_iff Complex.units_noSmallSubgroups χ hχ w).1 h0
  have hmem : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
    intro x hx _
    have h1 := hk (mem_units_of_isUnitAt w x hx)
    rw [MonoidHom.mem_ker] at h1
    exact h1
  exact Nat.le_zero.1 ((H.cond w).2 hmem)

theorem kernel_expansion_holds : SKern := by
  intro F _ _ _ c hc
  refine ⟨((finiteAdeleMeasure F (idealFiniteAdeles (levelIdeal c))).toReal : ℂ), ?_,
    fun A Z => adelicFourier_slice hc A Z⟩
  rw [Complex.ofReal_ne_zero, finiteAdeleMeasure_idealFiniteAdeles_toReal]
  refine mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact (levelIdeal c).ne_zero
  · rw [NNReal.coe_ne_zero, Ne, NNReal.sqrt_eq_zero, nnnorm_eq_zero]
    exact_mod_cast NumberField.discr_ne_zero F

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

