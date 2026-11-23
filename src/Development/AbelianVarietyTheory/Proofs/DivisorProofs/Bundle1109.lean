module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import GroundTheory.AutomorphicForms.MeasuresModulus
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SymmetricPowerMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinityTypeUnitaryHeckeCharCMRestrictingToEta
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.MuInfType

theorem char_eq_zpow (χ : ℂˣ →* ℂˣ) (hc : Continuous χ) (hu : ∀ z, ‖(χ z : ℂ)‖ = 1)
    (hp : ∀ z : ℂˣ, (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χ z = 1) :
    ∃ n : ℤ, ∀ z : ℂˣ, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ n := by
  have hmem : ∀ z, (χ (Circle.toUnits z) : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere, mem_sphere_zero_iff_norm] using hu _
  let f : Circle →* Circle :=
    { toFun := fun z => (⟨(χ (Circle.toUnits z) : ℂ), hmem z⟩ : Circle)
      map_one' := Circle.ext (by simp)
      map_mul' := fun a b => Circle.ext (by
        change ((χ (Circle.toUnits (a * b))) : ℂ) = (χ (Circle.toUnits a) : ℂ) * (χ (Circle.toUnits b) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcu : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · exact continuous_subtype_val
    · have : (fun x : Circle => ((Circle.toUnits x)⁻¹ : ℂˣ).val) = fun x : Circle => (x : ℂ)⁻¹ := by
        funext x; simp
      rw [this]
      exact (continuous_subtype_val).inv₀ fun x => Circle.coe_ne_zero x
  have hf : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact Units.continuous_val.comp (hc.comp hcu)
  obtain ⟨n, hn⟩ := GlobalTheory.circle_hom_eq_zpow f hf
  refine ⟨n, fun z => ?_⟩
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hn0 : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz0
  have hw : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
    simp [Submonoid.unitSphere, mem_sphere_zero_iff_norm, norm_div, hz0]
  let w : Circle := (⟨_, hw⟩ : Circle)
  let r : ℂˣ := Units.mk0 (‖(z : ℂ)‖ : ℂ) hn0
  have hzr : z = Circle.toUnits w * r := Units.ext (by
    change (z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) * (‖(z : ℂ)‖ : ℂ)
    field_simp)
  have hr : χ r = 1 := hp r (by simp [r])
  have h1 := congrArg (fun c : Circle => (c : ℂ)) (hn w)
  have hχ : χ z = χ (Circle.toUnits w) := by rw [hzr, map_mul, hr, mul_one]
  rw [hχ]
  change ((f w : Circle) : ℂ) = _
  rw [h1, Circle.coe_zpow]

end GlobalTheory.MuInfType

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def single (v : InfinitePlace E) : ℂˣ →* (Cinf E)ˣ := Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℂ) v)

theorem continuous_single (v : InfinitePlace E) : Continuous (single v) :=
  Continuous.units_map _ (by
    show Continuous (fun z : ℂ => (Pi.mulSingle v z : InfinitePlace E → ℂ))
    exact continuous_mulSingle (A := fun _ : InfinitePlace E => ℂ) v)


variable (E) in
abbrev below (v : InfinitePlace E) : InfinitePlace (maximalRealSubfield E) := v.comap (algebraMap (maximalRealSubfield E) E)

def iota (v : InfinitePlace E) : (below E v).Completion →+* ℂ :=
  (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).toRingHom.comp
    (AbsoluteValue.Completion.map (below E v).1 v.1)

theorem ideleMap_infIdele (v : InfinitePlace E) (x : ((below E v).Completion)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) =
      infId E (single v (Units.map (iota v).toMonoidHom x)) := by
  classical
  refine Units.ext (ad_ext ?_ ?_)
  · funext w
    have h1 : ∀ u : (Cinf E)ˣ, pInf E (infId E u).val = u.val := fun u => by
      change (infEq E).symm (1 - infEq E 1 + infEq E u.val) = _
      simp
    rw [h1]
    show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
      (AbsoluteValue.Completion.map (below E w).1 w.1
        (Pi.mulSingle (below E v) ((x : (below E v).Completion)) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      simp [single, iota]
    · have h' : w.comap (algebraMap (maximalRealSubfield E) E) ≠ below E v := fun e =>
        h ((IsCMField.equivInfinitePlace E).injective e)
      rw [Pi.mulSingle_eq_of_ne h']
      simp [single, Pi.mulSingle_eq_of_ne h]
  · change pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ (below E v) x) : Ad E) =
      pFin E (infId E _).val
    refine (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)).trans ?_
    change (1 : Af E) = 1 - 0 + 0
    simp

theorem iota_real (v : InfinitePlace E) (s : ℝ) :
    iota v ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s) = s := by
  let ψ : ℝ →+* ℂ := (iota v).comp
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.toRingHom
  have hψ : Continuous ψ :=
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      (AbsoluteValue.Completion.continuous_map (below E v).1 v.1)).comp
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm.continuous
  have := map_real_smul ψ hψ s 1
  simpa [ψ] using this

end GlobalTheory.MuInfType

end

noncomputable section

open ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.MuInfType

theorem infType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E), μ.IsUnitary →
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    ∃ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  intro E _ _ _ μ hU hη
  let χv : InfinitePlace E → ℂˣ →* ℂˣ := fun v => (chiInf μ).comp (single v)
  have hcont : ∀ v, Continuous (χv v) := fun v => (continuous_chiInf μ).comp (continuous_single v)
  have hunit : ∀ v z, ‖(χv v z : ℂ)‖ = 1 := fun v z => hU _
  have hval : ∀ v (x : ((below E v).Completion)ˣ),
      χv v (Units.map (iota v).toMonoidHom x) = (GlobalTheory.GalOfCusp.quadChar E).1 (infIdele _ (below E v) x) := by
    intro v x
    change μ.1 (infId E (single v _)) = _
    rw [← ideleMap_infIdele, hη]
  have hneg : ∀ v, χv v (-1) = -1 := by
    intro v
    have e : Units.map (iota v).toMonoidHom (-1) = -1 := Units.ext (by simp)
    have h := hval v (-1)
    rw [e] at h
    rw [h]
    exact GlobalTheory.GalOfCusp.quadChar_locInf E (below E v)
  have hpos : ∀ v (z : ℂˣ), (((‖(z : ℂ)‖ : ℝ) : ℂ)) = z → χv v z = 1 := by
    intro v z hz
    set s : ℝ := Real.sqrt ‖(z : ℂ)‖ with hs
    have hs0 : s ≠ 0 := by
      rw [hs]
      exact (Real.sqrt_pos.2 (norm_pos_iff.2 z.ne_zero)).ne'
    have hx0 : (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (below E v))).symm s ≠ 0 := by
      simpa using hs0
    let x : ((below E v).Completion)ˣ := Units.mk0 _ hx0
    have hx : Units.map (iota v).toMonoidHom x ^ 2 = z := Units.ext (by
      simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, x,
        Units.val_mk0, iota_real]
      rw [← Complex.ofReal_pow, hs, Real.sq_sqrt (norm_nonneg _), hz])
    rw [← hx, map_pow, hval]
    change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E _)) ^ 2 = 1
    rw [← map_pow, Int.units_sq, map_one]
  choose e he using fun v => GlobalTheory.MuInfType.char_eq_zpow (χv v) (hcont v) (hunit v) (hpos v)
  refine ⟨e, fun v => ?_, fun z => ?_⟩
  · have h := he v (-1)
    rw [hneg] at h
    simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, div_one] at h
    rcases Int.even_or_odd (e v) with h' | h'
    · rw [h'.neg_one_zpow] at h
      norm_num at h
    · exact h'
  · let zv : InfinitePlace E → ℂˣ := fun v => Units.map (Pi.evalMonoidHom (fun _ : InfinitePlace E => ℂ) v) z
    have hz : z = ∏ v, single v (zv v) := Units.ext (by
      rw [Units.coe_prod]
      simp only [single, zv, Units.coe_map, MonoidHom.coe_coe, MonoidHom.mulSingle_apply, Pi.evalMonoidHom_apply]
      exact (Finset.univ_prod_mulSingle z.val).symm)
    conv_lhs => rw [hz]
    rw [map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun v _ => he v (zv v)

end GlobalTheory.MuInfType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZero
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousAt_inv_log_zero : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) 0 := by
  unfold ContinuousAt
  simp only [Real.log_zero, inv_zero]
  refine Tendsto.mono_left (x := 𝓝[≠] (0:ℝ) ⊔ pure 0) ?_ (nhdsNE_sup_pure (0:ℝ)).ge
  refine Tendsto.sup ?_ ?_
  · exact tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero
  · rw [tendsto_pure_left]
    intro s hs
    simpa using mem_of_mem_nhds hs

theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Set.Icc 0 (1 / 2)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact (continuousAt_inv_log_zero.neg).continuousWithinAt
    · have hlog : Real.log t ≠ 0 := by
        have : Real.log t < 0 := Real.log_neg h (by linarith [ht.2])
        exact this.ne
      exact ((Real.continuousAt_log h.ne').inv₀ hlog).neg.continuousWithinAt
  refine intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hlogneg : Real.log t < 0 := Real.log_neg ht0 (by linarith [ht.2])
    have hlog : Real.log t ≠ 0 := hlogneg.ne
    have h1 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t :=
      ((Real.hasDerivAt_log ht0.ne').inv hlog).neg
    convert h1 using 1
    rw [abs_of_neg hlogneg]
    field_simp
  · intro t ht
    have := ht.1
    positivity

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicDerivCompactSupportEqZero
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop

theorem integral_dbar_eq_zero_of_hasCompactSupport {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem setIntegral_dbar_eq_zero {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (h0 : ∀ v ∈ U, v ∉ K → g v = 0) :
    IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  classical
  set G : V n → ℂ := U.indicator g with hGdef
  have hin : ∀ v ∈ U, G =ᶠ[𝓝 v] g := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx
    exact Set.indicator_of_mem hx g
  have hz : ∀ x, x ∉ K → G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hGdef, Set.indicator_of_mem hxU, h0 x hxU hx]
    · rw [hGdef, Set.indicator_of_notMem hxU]
  have hout : ∀ v, v ∉ K → G =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with x hx
    exact hz x hx
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hin v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v fun h => hv (hKU h))
  have hc : HasCompactSupport G := HasCompactSupport.intro hK hz
  obtain ⟨hI, hE⟩ := integral_dbar_eq_zero_of_hasCompactSupport hG hc ξ
  have heq : Set.EqOn (fun v => dbar G v ξ) (fun v => dbar g v ξ) U := fun v hv => by
    simp only [dbar_congr (hin v hv)]
  refine ⟨hI.integrableOn.congr_fun heq hU.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hU.measurableSet heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hE]
  intro v hv
  rw [dbar_congr (hout v fun h => hv (hKU h))]
  simp [dbar_apply]

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompLinearMapMatrixNonarchLocalField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open MeasureTheory
open scoped NNReal Pointwise

namespace GlobalTheory.DetScale

theorem integral_comp_linearEquiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [TopologicalSpace V] [IsModuleTopology k V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : V ≃ₗ[k] V) (f : V → ℂ) :
    ∫ y, f (L y) ∂μ = (((distribHaarChar k (LinearEquiv.det L) : ℝ≥0) : ℝ) : ℂ)⁻¹ * ∫ y, f y ∂μ := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup k V
  let n := Module.finrank k V
  let e0 : V ≃ₗ[k] (Fin n → k) := (Module.finBasis k V).equivFun
  let e : V ≃L[k] (Fin n → k) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  borelize (Fin n → k)
  let ν : Measure (Fin n → k) := μ.map e
  haveI : ν.IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let L' : (Fin n → k) ≃ₗ[k] (Fin n → k) := (e0.symm.trans L).trans e0
  set c : ℝ≥0 := distribHaarChar k (LinearEquiv.det L) with hc
  have hd : distribHaarChar (Fin n → k) L' = c := by
    rw [GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq, LinearEquiv.det_conj]
  have hc0 : c ≠ 0 := (distribHaarChar_pos (A := k) (g := LinearEquiv.det L)).ne'
  let Lh : V ≃ₜ V :=
    { L.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap }
  have hν : ∀ s : Set V, ν (e '' s) = μ s := fun s => by
    have h := e.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (e '' s)
    refine h.trans ?_
    congr 1
    exact Set.preimage_image_eq s e.injective
  have hm : μ.map Lh.toMeasurableEquiv = c⁻¹ • μ := by
    ext s _
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, ← hν, ← hν s]
    have h := distribHaarChar_mul ν L' (e '' (Lh ⁻¹' s))
    have hs : L' • (e '' (Lh ⁻¹' s)) = e '' s := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨L y, hy, ?_⟩
        simp [L', e, LinearEquiv.smul_def]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨e (L.symm y), ⟨L.symm y, ?_, rfl⟩, ?_⟩
        · simpa [Lh] using hy
        · simp [L', e, LinearEquiv.smul_def]
    rw [hs, hd] at h
    rw [← h, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hc0,
      ENNReal.coe_one, one_mul]
    rfl
  have e1 : ∫ y, f (L y) ∂μ = ∫ y, f (Lh.toMeasurableEquiv y) ∂μ := rfl
  rw [e1, ← integral_map_equiv, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  rfl

theorem integral_comp_matrix : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (a b : ℕ) (L : Matrix (Fin a) (Fin b) F →ₗ[F] Matrix (Fin a) (Fin b) F) (hL : LinearMap.det L ≠ 0)
    (φ : Matrix (Fin a) (Fin b) F → ℂ) (μ : @MeasureTheory.Measure (Matrix (Fin a) (Fin b) F) (borel _)),
    @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∫ x, φ (L x) ∂μ = ((((MeasureTheory.distribHaarChar F (Units.mk0 _ hL) : NNReal) : ℝ) : ℂ))⁻¹ * ∫ x, φ x ∂μ := by
  intro F _ _ _ _ a b L hL φ μ hμ
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) F) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) F) := ⟨rfl⟩
  haveI : IsModuleTopology F (Matrix (Fin a) (Fin b) F) :=
    show IsModuleTopology F (Fin a → Fin b → F) from inferInstance
  let Le := LinearMap.equivOfDetNeZero L hL
  have hdet : LinearEquiv.det Le = Units.mk0 _ hL := by
    ext
    rw [LinearEquiv.coe_det, Units.val_mk0]
    rfl
  have h := integral_comp_linearEquiv (k := F) μ Le φ
  rw [hdet] at h
  exact h

end GlobalTheory.DetScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionDivisorEqSelfIntersectionPresented
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernDegree

theorem inter_const_eq_topSelf_of_presents :
    ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ), L.IsLB → Presents Δ L r → Y.inter (fun _ => Δ) = topSelfIntersection ℂ L Y.dim :=
  fun _ _ _ _ hL h => Var.inter_eq_of_toPic_eq (fun _ => hL) fun _ => h.toPic_eq

end GlobalTheory.ChernDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIntegralMatrixCharpolyRootStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_integral_matrix_charpoly_root : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (u : B.A) (Q : (w.adicCompletion E)[X]), Q.Monic → aeval u (Q.map e.symm.toRingHom) = 0 → ∀ y : GLw m w, y ∈ GlobalTheory.LFun.KGL w (n := m) → y.val.charpoly = Q → IsIntegral K.O u := by
  first | exact @GlobalTheory.TwLat.isIntegral_of_charpoly_intGL | exact GlobalTheory.TwLat.isIntegral_of_charpoly_intGL | (intros; apply GlobalTheory.TwLat.isIntegral_of_charpoly_intGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRep
section
open Matrix
open Formalism.REAL (inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin)
open scoped InnerProductSpace

namespace GlobalTheory.HdSmooth

theorem kFinite_smoothVec : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  intro n ε H _ _ _ _ σ hU hI v hv
  have hAnalytic :=
    CompanionTheory.D.gk.HC.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hU hI v hv
  have h := hAnalytic.smoothVec (P := 1) (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  simpa [inG] using h

end GlobalTheory.HdSmooth
end

