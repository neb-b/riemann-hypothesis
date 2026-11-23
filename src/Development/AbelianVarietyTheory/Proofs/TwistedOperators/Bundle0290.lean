module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GroupConvolutionNormalizedIndicatorSelf
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section
namespace GlobalTheory.TrIdem

theorem conv_normInd_self (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hHo : IsOpen (H : Set G)) (hHc : IsCompact (H : Set G)) :
    conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  have hm : MeasurableSet (H : Set G) := hHo.measurableSet
  have hpos : μ (H : Set G) ≠ 0 := (hHo.measure_pos μ ⟨1, H.one_mem⟩).ne'
  have hfin : μ (H : Set G) ≠ ⊤ := hHc.measure_lt_top.ne
  have hr : (μ.real (H : Set G) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact (ENNReal.toReal_pos hpos hfin).ne'
  funext y
  simp only [conv, normInd]
  set c : ℂ := (μ.real (H : Set G) : ℂ)⁻¹ with hc
  by_cases hy : y ∈ H
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = (H : Set G).indicator (fun _ => c * c) := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hx) hy
        simp [Set.indicator_of_mem (show x ∈ (H : Set G) from hx),
          Set.indicator_of_mem (show x⁻¹ * y ∈ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_indicator_const _ hm]
    simp only [Pi.smul_apply, Set.indicator_of_mem (show y ∈ (H : Set G) from hy), Pi.one_apply, smul_eq_mul, mul_one]
    rw [Complex.real_smul, hc]
    field_simp
  · have key : (fun x => (c • (H : Set G).indicator (1 : G → ℂ)) x * (c • (H : Set G).indicator (1 : G → ℂ)) (x⁻¹ * y))
        = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ H
      · have : x⁻¹ * y ∉ H := fun h => hy (by simpa using H.mul_mem hx h)
        simp [Set.indicator_of_notMem (show x⁻¹ * y ∉ (H : Set G) from this)]
      · simp [Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
    rw [key, integral_zero]
    simp [Set.indicator_of_notMem (show y ∉ (H : Set G) from hy)]

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarEqRestrictedProductMeasureUnitaryFiniteAdeli
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
namespace GlobalTheory.FinMeasEq

variable {D : D7}

theorem locallyCompactSpace_GfC (V : HSp D) : LocallyCompactSpace (GfC V) :=
  locallyCompactSpace_finPts D.sp.cm.sig V.gram

theorem tensorFin_unitLoc (V : HSp D) (g : GFin D.sp.cm.sig V.gram) :
    tensorFin D.sp.cm.sig V.gram (unitLoc D.sp.cm.sig V.gram (frameLat V)) g =
      (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram)).indicator 1 g := by
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  by_cases hg : g ∈ levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅
  · rw [Set.indicator_of_mem hg]
    have hv := (mem_levelOffFin.1 hg).2
    unfold tensorFin
    rw [Pi.one_apply]
    refine (finprod_congr fun v => ?_).trans finprod_one
    simp [unitLoc, hv v (Finset.notMem_empty v)]
  · rw [Set.indicator_of_notMem hg]
    by_contra hne
    refine hg (mem_levelOffFin.2 ⟨fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => ?_⟩)
    have := (isFinFamily_unit.tensorFin_ne_zero_iff g).1 hne v
    by_contra hv
    exact this (by simp [unitLoc, hv])

theorem finMeas_eq : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v))
    (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF →
    ∀ (ν : Measure (GfC V)), IsFinMeas V μf ν → ∀ s : Set (GfC V), IsCompact (closure s) →
      ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := by
  intro D V μf νF hF ν hν s hs
  letI : Submodule.IsFullLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  haveI := locallyCompactSpace_GfC V
  haveI : ν.IsHaarMeasure := hν.1
  set e := finPtsEquiv D.sp.cm.sig V.gram
  set ν' : Measure (GfC V) := νF.map e with hν'
  have hmap : ∀ t : Set (GfC V), ν' t = νF (e ⁻¹' t) := fun t =>
    e.toHomeomorph.toMeasurableEquiv.map_apply t
  haveI : ν'.IsHaarMeasure := (isRestrictedProdFinPts_iff.1 hF.map_finPts).2.1

  set Kf : Set (GFin D.sp.cm.sig V.gram) := (levelOffFin D.sp.cm.sig V.gram (frameLat V) ∅ : Set (GFin D.sp.cm.sig V.gram))
  set K : Set (GfC V) := e.symm ⁻¹' Kf with hK
  have hKo : IsOpen K := (isOpen_levelOffFin_empty _ _ _).preimage e.symm.continuous
  have hKf_closed : IsClosed Kf :=
    Subgroup.isClosed_of_isOpen _ (isOpen_levelOffFin_empty _ _ _)
  have hKc : IsClosed K := hKf_closed.preimage e.symm.continuous
  have hKcpt : IsCompact K := by
    have : K = e '' Kf := (e.toHomeomorph.image_eq_preimage_symm Kf).symm
    rw [this]
    exact (isCompact_levelOffFin _ _ _ ∅).image e.continuous
  have hKne : K.Nonempty := ⟨1, by
    change e.symm 1 ∈ Kf
    rw [map_one]
    exact Subgroup.one_mem _⟩

  have h1 : ν' K = ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    rw [hmap]
    refine (congrArg νF (Set.ext fun x => ?_)).trans hF.measure_level
    change e.symm (e x) ∈ Kf ↔ _
    rw [e.symm_apply_apply]
  have hfin : (Function.mulSupport fun v => μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v)).Finite :=
    Filter.eventually_cofinite.1 (isRestrictedProdFin_iff.1 hF).2.2.1
  have h2 : ν.real K = ∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) := by
    have hi := hν.2 _ isFinFamily_unit
    have hfn : finFn V (unitLoc D.sp.cm.sig V.gram (frameLat V)) = K.indicator (fun _ => (1 : ℂ)) := by
      funext y
      rw [GlobalTheory.TrConv.finFn_eq_tensorFin, tensorFin_unitLoc]
      rfl
    rw [hfn, integral_indicator_const _ hKo.measurableSet] at hi
    have hloc : ∀ v, ∫ x, unitLoc D.sp.cm.sig V.gram (frameLat V) v x ∂μf v =
        (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) := fun v => by
      have := (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v).measurableSet
      rw [unitLoc, show (1 : GLoc D.sp.cm.sig V.gram v → ℂ) = fun _ => 1 from rfl,
        integral_indicator_const _ this]
      simp
    simp_rw [hloc] at hi
    have hc : (∏ᶠ v, (((μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ)) =
        ((∏ᶠ v, (μf v).real (stabLoc D.sp.cm.sig V.gram (frameLat V) v) : ℝ) : ℂ) :=
      (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [Complex.real_smul, mul_one, hc] at hi
    exact_mod_cast hi
  have h3 : ν K = ν' K := by
    rw [h1]
    have hK' : ν K ≠ ⊤ := hKcpt.measure_lt_top.ne
    have hP : ∏ᶠ v, μf v (stabLoc D.sp.cm.sig V.gram (frameLat V) v) ≠ ⊤ := by
      rw [← h1]; exact hKcpt.measure_lt_top.ne
    rw [← ENNReal.toReal_eq_toReal_iff' hK' hP]
    rw [show (ν K).toReal = ν.real K from rfl, h2]
    exact (ENNReal.toRealHom.map_finprod hfin).symm
  have hc := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' (s := K)
    (by rw [hKc.closure_eq]; exact hKcpt)
  have hc1 : Measure.haarScalarFactor ν ν' = 1 := by
    have hpos : ν' K ≠ 0 := hKo.measure_ne_zero ν' hKne
    have htop : ν' K ≠ ⊤ := hKcpt.measure_lt_top.ne
    rw [h3, ENNReal.smul_def, smul_eq_mul] at hc
    have := (ENNReal.mul_left_inj hpos htop).1 ((one_mul _).trans hc)
    exact_mod_cast this.symm
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ν ν' hs, hc1, one_smul, hmap]

end GlobalTheory.FinMeasEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.HalfModTorus

open GlobalTheory.Doubling

theorem compFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (y : AE D) (h : finPart D y = 1) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v y = 1 := by
  have h' : Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y = 1 := h
  have e : GlobalTheory.AdelicU.compFin D.host.F D.host.E v y =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e, h', map_one]

theorem unitFin_eq_one {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : (AE D)ˣ) (h : finPart D (x : AE D) = 1) :
    unitFin D.host.F D.host.E v x = 1 :=
  Units.ext (compFin_eq_one v (x : AE D) h)

theorem compInf_eq {D : D7} (w : InfinitePlace D.host.F) (t' : GlobalTheory.AdelicU.EmbOver D.host.E w) (y : AE D) :
    GlobalTheory.AdelicU.infEmb t' (GlobalTheory.AdelicU.compInf D.host.F D.host.E w y) = GlobalTheory.AdelicU.infProj t' (infPart D y) := by
  have e : GlobalTheory.AdelicU.compInf D.host.F D.host.E w y =
      Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) y) := by
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e]
  rfl

theorem absE_of_components {D : D7} (x : (AE D)ˣ) (c : NNReal)
    (hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x) = 1)
    (hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) (unitInf D.host.F D.host.E _ x) = c) :
    absE D.host.F D.host.E x = c ^ Fintype.card D.what₂.Tau := by
  have e1 : (∏ᶠ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v x)) = 1 :=
    finprod_eq_one_of_forall_eq_one hf
  have e2 : (∏ w, absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x)) = c ^ Fintype.card D.what₂.Tau := by
    rw [← (GlobalTheory.CMTypePlaces.places_bijective D).prod_comp
      (fun w => absEw D.host.F D.host.E w (unitInf D.host.F D.host.E w x))]
    simp only [hw, Finset.prod_const, Finset.card_univ]
  rw [absE_apply, e1, e2, mul_one]

theorem halfMod_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  intro D θ hθ r n t ht α hfin hinf
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).1
  haveI := hcm.1
  have hxv : ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = α.1.det := rfl
  have h1 : finPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D) = 1 := by
    rw [hxv, RingHom.map_det, RingHom.mapMatrix_apply, hfin, Matrix.det_one]
  have hf : ∀ v, absEv D.host.F D.host.E v (unitFin D.host.F D.host.E v (Matrix.GeneralLinearGroup.det α)) = 1 :=
    fun v => by rw [unitFin_eq_one v _ h1, map_one]
  have hdet : ∀ τ, θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = ((∏ i, t i : ℝ) : ℂ) := by
    intro τ
    have e : θ τ (infPart D ((Matrix.GeneralLinearGroup.det α : (AE D)ˣ) : AE D)) = (compAt θ τ α.1).det := by
      rw [hxv, ← RingHom.comp_apply, RingHom.map_det]
      rfl
    rw [e, hinf τ, Matrix.det_diagonal, Complex.ofReal_prod]
  have hw : ∀ τ : D.what₂.Tau, absEw D.host.F D.host.E
      (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
      (unitInf D.host.F D.host.E _ (Matrix.GeneralLinearGroup.det α)) = ‖((∏ i, t i : ℝ) : ℂ)‖₊ ^ 2 := by
    intro τ
    let t' : GlobalTheory.AdelicU.EmbOver D.host.E (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))) :=
      ⟨tauE D τ, (InfinitePlace.embedding_mk_eq_of_isReal
        (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm⟩
    rw [absEw_eq_sq hcm t', ← hdet τ,
      GlobalTheory.AutFunCompare.isInfEmb_unique _ _ _ (hθ τ) (GlobalTheory.AdelicU.isInfEmb_infProj t')]
    exact congrArg (fun z : ℂ => ‖z‖₊ ^ 2) (compInf_eq _ t' _)
  have hcard : Fintype.card D.what₂.Tau = Module.finrank ℚ D.host.F := by
    rw [Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D), IsTotallyReal.finrank,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  have hP : 0 < ∏ i, t i := Finset.prod_pos fun i _ => ht i
  have habs : ((absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det α) : NNReal) : ℝ) =
      (∏ i, t i) ^ (2 * Module.finrank ℚ D.host.F) := by
    rw [absE_of_components _ _ hf hw, hcard, NNReal.coe_pow, NNReal.coe_pow, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hP, ← pow_mul]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod
  rw [habs, Finset.prod_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  push_cast
  ring

end GlobalTheory.HalfModTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

section LA

variable {ι Q : Type} [AddCommGroup Q] [Module ℂ Q]

def IsStab (ρ : ι → Module.End ℂ Q) (N : Submodule ℂ Q) : Prop := ∀ i, ∀ x ∈ N, ρ i x ∈ N

def HoweCond (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ Q), StrictMono N → (∀ k, IsStab ρ (N k) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ Q, IsStab ρ N → C ≤ N → N ≠ ⊤ → IsStab ρ N' → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

def rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Submodule ℂ Q :=
  sSup {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}

theorem isStab_rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : IsStab ρ (rad ρ C) := by
  intro i
  have h : rad ρ C ≤ (rad ρ C).comap (ρ i) := by
    refine sSup_le fun N hN => ?_
    intro x hx
    exact le_sSup hN (hN.1 i x hx)
  exact fun x hx => h hx

def radAct (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) : Module.End ℂ (Q ⧸ rad ρ C) :=
  (rad ρ C).mapQ (rad ρ C) (ρ i) fun x hx => isStab_rad ρ C i x hx

theorem radAct_mk (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) (x : Q) :
    radAct ρ C i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ i x) := rfl

end LA

section Fock

variable {D : D7}

def actT (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) + ((eS τ : ℂ) * Y.trace) • 1

def actS (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin M.rank) (Fin M.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) -
    ((eT τ : ℂ) * Z.trace) • 1

def coinv (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) : Submodule ℂ (PolF D X.rank M.rank) :=
  Submodule.span ℂ {P | ∃ τ, ∃ Z ∈ lieAt M τ, ∃ P₀, P = actS ε A B eT τ Z P₀}

abbrev LieIx (X : HSp D) : Type := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}

end Fock

section LALemmas

theorem isStab_sup {ι Q : Type} [AddCommGroup Q] [Module ℂ Q] {ρ : ι → Module.End ℂ Q} {N N' : Submodule ℂ Q}
    (h : IsStab ρ N) (h' : IsStab ρ N') : IsStab ρ (N ⊔ N') := by
  intro i x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h i y hy) (h' i z hz)

theorem rad_ne_top : ∀ (ι Q : Type) [AddCommGroup Q] [Module ℂ Q] (ρ : ι → Module.End ℂ Q) (C N₀ : Submodule ℂ Q),
  GlobalTheory.RealQuot.HoweCond ρ C → GlobalTheory.RealQuot.IsStab ρ N₀ → C ≤ N₀ → N₀ ≠ ⊤ → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ := by
  intro ι Q _ _ ρ C N₀ hH hs hC hne
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH
  let S : Set (Submodule ℂ Q) := {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}
  have wf : WellFounded (fun x y : S => y.1 < x.1) := by
    refine ⟨fun x => ?_⟩
    by_contra hx
    obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.1 hx
    have mono : StrictMono fun n => (f n).1 := strictMono_nat_of_lt_succ hf
    have := hL (L + 1) (fun k => (f k).1) (mono.comp Fin.val_strictMono) fun k => ⟨(f k).2.1, (f k).2.2.1⟩
    omega
  obtain ⟨M, -, hM⟩ := wf.has_min Set.univ ⟨⟨N₀, hs, hC, hne⟩, trivial⟩
  have hmax : ∀ N ∈ S, N ≤ M.1 := by
    intro N hN
    have hs' : M.1 ⊔ N ∈ S := ⟨isStab_sup M.2.1 hN.1, le_sup_of_le_left M.2.2.1,
      hsum _ _ M.2.1 M.2.2.1 M.2.2.2 hN.1 hN.2.1 hN.2.2⟩
    by_contra h
    exact hM ⟨_, hs'⟩ trivial (lt_of_le_of_ne le_sup_left fun e => h (e ▸ le_sup_right))
  have e : rad ρ C = M.1 := le_antisymm (sSup_le hmax) (le_sSup M.2)
  rw [e]
  exact M.2.2.2

theorem rad_le_ker : ∀ (ι Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (β : Q →ₗ[ℂ] Pi),
  (∀ i, β ∘ₗ ρ i = σ i ∘ₗ β) → C ≤ LinearMap.ker β → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker β := by
  intro ι Q Pi _ _ _ _ ρ C σ β hi hk hrad hss
  by_contra hne
  have hKs : IsStab ρ (LinearMap.ker β) := fun i x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  have hK : LinearMap.ker β ≠ ⊤ := fun h => hne (h ▸ le_top)
  have hTs : IsStab σ ((rad ρ C).map β) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, isStab_rad ρ C i x hx, by rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]⟩
  obtain ⟨N', hN's, hc⟩ := hss _ hTs
  have hUs : IsStab ρ (N'.comap β) := fun i x hx => by
    show β (ρ i x) ∈ N'
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]
    exact hN's i _ hx
  have hCU : C ≤ N'.comap β := fun x hx => by
    show β x ∈ N'
    rw [LinearMap.mem_ker.1 (hk hx)]
    exact N'.zero_mem
  have hsup : rad ρ C ⊔ N'.comap β = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : β x ∈ (rad ρ C).map β ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht, n, hn, htn⟩ := Submodule.mem_sup.1 h1
    obtain ⟨r, hr, rfl⟩ := ht
    have h2 : x - r ∈ N'.comap β := by
      show β (x - r) ∈ N'
      rw [map_sub, ← htn, add_sub_cancel_left]
      exact hn
    have h3 := Submodule.add_mem_sup hr h2
    rwa [add_sub_cancel] at h3
  by_cases hU : N'.comap β = ⊤
  · apply hne
    intro x hx
    have h1 : β x ∈ (rad ρ C).map β := ⟨x, hx, rfl⟩
    have h2 : β x ∈ N' := by
      have : x ∈ N'.comap β := hU ▸ Submodule.mem_top
      exact this
    have h3 : β x ∈ (rad ρ C).map β ⊓ N' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h3
    exact h3
  · exact hrad (eq_top_iff.2 (hsup ▸ sup_le le_rfl (le_sSup ⟨hUs, hCU, hU⟩)))

end LALemmas

theorem hasInfExp_div : ∀ (D : D7) (α β : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D α τ a → HasInfExp D β τ b →
  HasInfExp D (β / α) τ (b - a) := by
  intro D α β τ a b hA hB
  obtain ⟨m, hm, ex, hα⟩ := hA
  obtain ⟨n, hn, -, hβ⟩ := hB
  refine ⟨n - m, by push_cast; rw [hm, hn]; ring, ex, fun θ hθ x h1 h2 => ?_⟩
  have eα := hα θ hθ x h1 h2
  have eβ := hβ θ hθ x h1 h2
  set w : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hw
  have hdiv : (((β / α) x : Circle) : ℂ) = ((β x : Circle) : ℂ) / ((α x : Circle) : ℂ) := by
    rw [MonoidHom.div_apply, Circle.coe_div]
  rw [hdiv, eα, eβ]
  rcases eq_or_ne w 0 with h0 | h0
  · have hm0 : m = 0 := by
      by_contra hm0
      have := eα
      rw [h0, _root_.zero_zpow _ hm0] at this
      exact Circle.coe_ne_zero _ this
    have hn0 : n = 0 := by
      by_contra hn0
      have := eβ
      rw [h0, _root_.zero_zpow _ hn0] at this
      exact Circle.coe_ne_zero _ this
    subst hm0 hn0
    simp
  · rw [zpow_sub₀ h0]

end GlobalTheory.RealQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamiliesStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_classes_iff_local_class_families : ∀ (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧ (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧ ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧ (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔ (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧ ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧ ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion), (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) → ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧ ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  first | exact @GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | exact GlobalTheory.TrEll.RatClasses.rat_classes_iff_local | (intros; apply GlobalTheory.TrEll.RatClasses.rat_classes_iff_local <;> assumption)
end

