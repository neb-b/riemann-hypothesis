module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0869
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0867
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0868
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpan
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaLimR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mspanR_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) :
    GlobalTheory.JSW.mspanR π ≤ bddForms E a ω := by
  rw [← GlobalTheory.JSW.rspan_eq_mspanR]
  exact GlobalTheory.JSW.rspan_le (fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ)
    (fun F hF h => mul_right_mem_bddForms hF h) (fun F hF X _ ν _ k γ hk => GlobalTheory.JSW.kerInf_mem_bddForms hF hk)

theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ bddForms E a ω :=
  hφ.elim (fun h => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ h)
    (fun h => mspanR_le_bddForms hω hπ h)

theorem mem_rsm {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) :
    φ ∈ GlobalTheory.RSThetaLowM.rsm π := by
  change φ.1 ∈ GlobalTheory.JSW.mspanR π
  rcases hφ with h | h
  · rw [← GlobalTheory.JSW.rspan_eq_mspanR]; exact GlobalTheory.JSW.mem_rspan h
  · exact h

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem resConst_ne_zero {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ2 : HasCompactSupport Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (hpos : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (hne : Φ ≠ 0) :
    ((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a ≠ 0 := by
  have hv : (finiteMeasurePi E (latt a J)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨((isOpen_latt J).measure_pos _ ⟨0, fun i => (idealFiniteAdeles J).zero_mem⟩).ne',
      (isCompact_latt J).measure_lt_top.ne⟩
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 hv) ?_
  have e : (fun u => Φ u) = fun u => (((Φ u).re : ℝ) : ℂ) := funext fun u => Complex.ext rfl (by simp [(hpos u).2])
  obtain ⟨x, hx⟩ : ∃ x, Φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hre : (Φ x).re ≠ 0 := fun h0 => hx (Complex.ext h0 (hpos x).2)
  have hpos' : 0 < ∫ u, (Φ u).re ∂(volume : Measure (Fin a → Cinf E)) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Complex.continuous_re.comp hΦ1.continuous)
      (hΦ2.comp_left Complex.zero_re) (fun u => (hpos u).1) hre
  rw [e, integral_complex_ofReal, infMeasure, integral_smul_measure]
  refine Complex.ofReal_ne_zero.2 (smul_ne_zero ?_ hpos'.ne')
  simp

theorem setIntegral_rsHat_zero_of_bdd {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦ2 : HasCompactSupport Φ) (hΦ3 : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) {ω : HChar E} (hω : ω.IsUnitary) {φ φ' : Sm E a}
    (hb : φ.1 ∈ bddForms E a ω) (hb' : φ'.1 ∈ bddForms E a ω) :
    ∫ g in 𝓕', adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 ∂μ =
      (((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a) *
        ∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ := by
  have hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ1, hΦ2, hΦ3⟩
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : IsFiniteMeasure (μ.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]; exact measure_lt_top _ _⟩
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  obtain ⟨C, hC⟩ := hb.2.2.2
  obtain ⟨D, hD⟩ := hb'.2.2.2
  have hΦi : Integrable Φ (infMeasure E a) := by
    unfold infMeasure
    exact (hΦ1.continuous.integrable_of_hasCompactSupport hΦ2).smul_measure (by simp)
  have hi : Integrable (fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2)
      ((μ.restrict 𝓕').prod (infMeasure E a)) := by
    refine ((integrable_const (C * D)).mul_prod hΦi.norm).mono'
      (continuous_rsInf hb.1 hb'.1 hΦ1.continuous hΦ3).aestronglyMeasurable (.of_forall fun p => ?_)
    simp only [rsInf, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1)))
      (norm_nonneg _)
  have hx : ∀ x, ∫ g in 𝓕', rsInf ℓ φ.1 φ'.1 Φ g x ∂μ = (∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ) * Φ x := by
    intro x
    simp only [rsInf]
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.RSResidue.setIntegral_mul_right h𝓕 (f := fun g => φ.1 g * conj (φ'.1 g))
      (GlobalTheory.Petersson.leftInv_mul_conj hω hb hb') _
  simp only [GlobalTheory.RSResidue.rsHat_zero J η φ φ' hΦ]
  rw [integral_mul_const, integral_integral_swap hi]
  simp only [hx, integral_const_mul]
  ring

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem theta_integral_low_mspanR {ℓ : Fin a} {π π' : CuspSub E a} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    {φ φ' : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) (hφ' : φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π')
    (hc : Continuous φ.1) (hc' : Continuous φ'.1) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, 1 < x →
      IntegrableOn (fun g : GA E a =>
        (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      IntegrableOn (fun g : GA E a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ)) ∂μ =
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ +
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ := by
  have h := mem_rsm hφ
  have h' := mem_rsm hφ'
  have hT : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hπ hπ' h h' hc hc' hT h𝓕
  simp only [Complex.ofReal_cpow (ideleModule E _).2.le, Complex.ofReal_sub, Complex.ofReal_one]
  exact ⟨fun x hx => ⟨(GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).1,
      GlobalTheory.RSThetaLowM.integrableOn_partA J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx,
      (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).2⟩,
    b3.continuous.comp Complex.continuous_ofReal⟩

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

theorem theta_integral_pole_mspanR : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → (∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ) ∧ Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 (c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ)) := by
  intro E _ _ _ a ℓ Φ hΦ hc hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, K = ((GroundTheory.Automorphic.GJMatrix.finiteMeasurePi E (GlobalTheory.ThetaPoisson.latt a J)).toReal : ℂ) * ∫ x, Φ x ∂GlobalTheory.ThetaPoisson.infMeasure E a := ⟨_, rfl⟩
  have hK0 : (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → K ≠ 0 := fun h1 h2 => hKdef ▸ resConst_ne_zero hΦ hc J h1 h2
  have had : ((a : ℝ) * (Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ℓ.pos)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  refine ⟨((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ)) * K,
    fun h1 h2 => mul_ne_zero (Complex.ofReal_ne_zero.2 (one_div_ne_zero had)) (hK0 h1 h2), ?_⟩
  intro π π' ω hω hπ hπ' φ φ' hφ hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ'⟩
  have hb := mem_bddForms hω hπ hφ
  have hb' := mem_bddForms hω hπ' hφ'
  obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous hc hs J η μ 𝓕 h𝓕
  obtain ⟨l1, l2⟩ := theta_integral_low_mspanR hu hu' hφ hφ' hb.1 hb'.1 hΦ hc hs J η h𝓕
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.RSResidue.rsHat_zero_props hω hb hb' ⟨hΦ, hc, hs⟩ J η
  have hres := _root_.GlobalTheory.RSThetaRes.residue_geometric E a ℓ.pos μ 𝓕 𝓕' h𝓕 h𝓕' _ f1 f2 f3
  rw [setIntegral_rsHat_zero_of_bdd hΦ hc hs J η h𝓕' hω hb hb', ← hKdef] at hres
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hT : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hsum : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
    GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
  have hint : ∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ := by
    intro x hx
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [hsum]; exact (l1 x hx).1
    have iHi : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ))
        (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ := by
      simp only [Complex.ofReal_cpow (hδ0 _).le]; exact u3 x
    refine (iLo.union iHi).mono_set fun g hg => ?_
    by_cases h : (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, (not_le.1 h).le⟩
  refine ⟨hint, ?_⟩

  set U : ℝ → ℂ := fun x => ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ with hU
  set B : ℝ → ℂ := fun x => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ with hB
  have hsplit : ∀ x : ℝ, 1 < x → ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ =
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ + B x + U x := by
    intro x hx
    rw [← integral_inter_add_diff hT (hint x hx)]
    congr 1
    simp only [hsum]
    exact (l1 x hx).2.2

  set M : ℝ := ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
    (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (2 : ℝ) ∂μ with hM
  have hUb : ∀ x : ℝ, x ≤ 2 → ‖U x‖ ≤ M := by
    intro x hx2
    refine norm_integral_le_of_norm_le ((u2 2).mono_set fun g hg => ⟨hg.1, by have h := hg.2; simp only [Set.mem_setOf_eq, not_le] at h ⊢; exact h.le⟩) ?_
    refine (ae_restrict_of_ae_restrict_of_subset (Set.diff_subset_compl _ _) (ae_restrict_mem hT.compl)).mono
      fun g hg => ?_
    have h1 : 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
      have h := hg; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h; exact h.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 g).le _)]
    exact mul_le_mul (norm_tsum_le_tsum_norm (u1 g)) (Real.rpow_le_rpow_of_exponent_le h1 hx2)
      (Real.rpow_nonneg (hδ0 g).le _) (tsum_nonneg fun _ => norm_nonneg _)
  have hx1 : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝 1) (𝓝 ((((1 : ℝ) - 1 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have tB : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * B x) (𝓝[>] 1) (𝓝 0) := by
    simpa using hx1.mul ((l2.tendsto 1).mono_left nhdsWithin_le_nhds)
  have tU : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * U x) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => ‖((x - 1 : ℝ) : ℂ)‖ * M) ?_
      (by have h := hx1.norm.mul_const M; rwa [norm_zero, zero_mul] at h)
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hUb x hx.2) (norm_nonneg _)
  have tot := (hres.add tB).add tU
  rw [add_zero, add_zero, mul_assoc] at *
  refine tot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx]
  ring

end GlobalTheory.RSThetaLimR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThick
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.RowsThick

theorem logb_le_of_log_le {l x A : ℝ} (hl : 1 ≤ Real.log l) (hx : Real.log x ≤ A) (hA : 0 ≤ A) :
    Real.logb l x ≤ A := by
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem one_le_log_of_eleven {l : ℝ} (hl : 11 ≤ l) : 1 ≤ Real.log l := by
  have h1 : Real.exp 1 ≤ l := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log l := Real.log_le_log (Real.exp_pos 1) h1

theorem colBd_le_row {l n r m S η H H' e e' hB eta₃ wP Sc large₂ flt : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m) (hS0 : 0 ≤ S) (hS : S ≤ Sc) (hη0 : 0 ≤ η)
    (hη : η ≤ eta₃) (hH0 : 0 ≤ H) (hH : H ≤ hB + eta₃) (hetaB : eta₃ ≤ hB) (hB1 : 1 ≤ hB)
    (hBb : hB ≤ 2 * Real.exp large₂) (hLg : 1 ≤ large₂) (hwP : 0 ≤ wP)
    (hflt : (wP + eta₃) / l + Sc + large₂ ≤ flt)
    (he : e ≤ 32 * H / l ^ 2 + 4 * S + 10 * η / (l - 1) + 25 * (Real.logb l (2 * H) + 1))
    (hH'0 : 0 ≤ H') (hH' : H' ≤ H)
    (he' : e' ≤ 23 * (1 + H' / l + (1 + Real.logb l (H' + 1)))) :
    (n + 1) * r * e + 4 * n * m * e' + 3 / 2 * n * (r * S + 2 * m * ((H + 1) / (l - 1) + 1)) ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) + 2082 * ((n + 1) * r * flt) +
        22365 * (n * m * (1 + hB / l + Real.logb l hB)) := by
  have hlog := one_le_log_of_eleven hl
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < l - 1 := by linarith
  have hetaP0 : 0 ≤ eta₃ := hη0.trans hη
  have hSc0 : 0 ≤ Sc := hS0.trans hS
  have hlB : 0 < Real.log l := by linarith

  have hlam : Real.logb l (2 * H) ≤ 7 + large₂ := by
    apply logb_le_of_log_le hlog _ (by linarith)
    rcases hH0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; linarith
    · have h8 : 2 * H ≤ 8 * Real.exp large₂ := by linarith
      calc Real.log (2 * H) ≤ Real.log (8 * Real.exp large₂) := Real.log_le_log (by linarith) h8
        _ = Real.log 8 + large₂ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 7 + large₂ := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]

  have hlogB : 0 ≤ Real.logb l hB := Real.logb_nonneg (by linarith) hB1
  have hlamB : Real.logb l (H' + 1) ≤ 1 + Real.logb l hB := by
    have h3 : Real.log (H' + 1) ≤ Real.log l + Real.log hB := by
      calc Real.log (H' + 1) ≤ Real.log (3 * hB) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log hB := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log l + Real.log hB := by
          have := Real.log_le_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ l by linarith)
          linarith
    unfold Real.logb
    calc Real.log (H' + 1) / Real.log l ≤ (Real.log l + Real.log hB) / Real.log l :=
          div_le_div_of_nonneg_right h3 hlB.le
      _ = 1 + Real.log hB / Real.log l := by rw [add_div, div_self hlB.ne']

  have hu0 : 0 ≤ eta₃ / l := div_nonneg hetaP0 hl0.le
  have hv0 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have hw0 : 0 ≤ wP / l := div_nonneg hwP hl0.le
  have hE0 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hHl : 32 * H / l ^ 2 ≤ 32 * (hB / l ^ 2) + 3 * (eta₃ / l) := by
    have a1 : H / l ^ 2 ≤ (hB + eta₃) / l ^ 2 := div_le_div_of_nonneg_right hH (by positivity)
    have a2 : eta₃ / l ^ 2 = (eta₃ / l) / l := by rw [div_div, sq]
    have a3 : (eta₃ / l) / l ≤ (eta₃ / l) / 11 := div_le_div_of_nonneg_left hu0 (by norm_num) hl
    have a4 := add_div hB eta₃ (l ^ 2)
    rw [mul_div_assoc]
    linarith
  have hηl : 10 * η / (l - 1) ≤ 11 * (eta₃ / l) := by
    rw [div_le_iff₀ hl1]
    have a1 : 11 * (eta₃ / l) * (l - 1) = 11 * eta₃ - 11 * (eta₃ / l) := by field_simp
    have a2 : eta₃ / l ≤ eta₃ / 11 := div_le_div_of_nonneg_left hetaP0 (by norm_num) hl
    rw [a1]; linarith
  have hwe : (wP + eta₃) / l = wP / l + eta₃ / l := add_div _ _ _
  set E1 := hB / l ^ 2 with hE1
  set M1 := 1 + hB / l + Real.logb l hB with hM1
  set cD := (H + 1) / (l - 1) + 1 with hcD
  have hflt0 : 0 ≤ flt := by linarith
  have he1 : e ≤ 32 * E1 + 225 * flt := by linarith
  have he2 : e' ≤ 69 * M1 := by
    have a1 : H' / l ≤ 2 * (hB / l) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl0.le
    linarith
  have hcD4 : cD ≤ 4 * M1 := by
    have a1 : (H + 1) / (l - 1) ≤ 4 * (hB / l) := by
      rw [div_le_iff₀ hl1]
      have b1 : 4 * (hB / l) * (l - 1) = 4 * hB - 4 * (hB / l) := by field_simp
      have b2 : hB / l ≤ hB / 11 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hl
      rw [b1]; linarith
    rw [hcD]; linarith
  have hM0 : 0 ≤ M1 := by linarith
  have h1 : (n + 1) * r * e ≤ (n + 1) * r * (32 * E1 + 225 * flt) :=
    mul_le_mul_of_nonneg_left he1 (by positivity)
  have h2 : n * m * e' ≤ n * m * (69 * M1) := mul_le_mul_of_nonneg_left he2 (by positivity)
  have h3 : n * r * S ≤ (n + 1) * r * flt := by
    have : S ≤ flt := by linarith
    calc n * r * S ≤ n * r * flt := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (n + 1) * r * flt := by
        have q1 : (n + 1) * r * flt = n * r * flt + r * flt := by ring
        have q2 := mul_nonneg hr hflt0
        linarith
  have h4 : n * m * cD ≤ n * m * (4 * M1) := mul_le_mul_of_nonneg_left hcD4 (by positivity)
  have p1 : 0 ≤ (n + 1) * r * E1 := by positivity
  have p2 : 0 ≤ (n + 1) * r * flt := by positivity
  have p3 : 0 ≤ n * m * M1 := by positivity
  linarith

attribute [local instance] nLet_neZero

section Facts

variable {D : D7} (L : SizeData₂ D)

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem Lg_ge_one : 1 ≤ TwistedPlaces.large₂ L := by
  unfold TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem placeWeight_nonneg : 0 ≤ TwistedPlaces.wP L := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := one_le_b L
    positivity
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    positivity
  have hB : 0 ≤ TwistedPlaces.wB L := by
    unfold TwistedPlaces.wB
    have := L.etaSz_pos
    exact le_max_of_le_left (by linarith)
  unfold TwistedPlaces.wP
  positivity

theorem one_le_hB : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_le_hB : TwistedPlaces.eta₃ L ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.eta₃ TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  linarith

end Facts

theorem Hmax_le {n : ℕ} [NeZero n] (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) :
    LiftingTheory.Hmax n (RamifiedCoefficientChains.MiW d b S η) (RamifiedCoefficientChains.hiW d b S η) ≤ RamifiedCoefficientChains.hpar n b S + η := by
  unfold LiftingTheory.Hmax
  apply Finset.sup_le
  intro k _
  have : b (k : ZMod n) ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ _)
  unfold RamifiedCoefficientChains.MiW RamifiedCoefficientChains.hiW RamifiedCoefficientChains.hpar
  split_ifs <;> omega

theorem hpar_le_of_thick {n : ℕ} [NeZero n] {b0 η : ℕ} {sz : ZMod n → ℕ} (S : ℕ)
    (h : ∀ a, TruncatedSeriesCountingBounds.Thick b0 η sz a) : RamifiedCoefficientChains.hpar n sz S ≤ b0 + η + S := by
  unfold RamifiedCoefficientChains.hpar
  have : Finset.univ.sup sz ≤ b0 + η := Finset.sup_le fun a _ => (h a).2
  omega

theorem rowL_of_allThick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd d bd hP04 hP54 hPar h11 hb hbox hC hA
  intro T₁ T₂ F' h2 h1 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hl' : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by rw [hp]
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setCS_of_wordsAT h11 hb hC hA T₁ T₂ F' h2 h1 hF
  obtain ⟨e, he, hcol, -⟩ :=
    hP04 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG d T₁ T₂ F' Wd.sz Wd.S Wd.η Wd.m hS trivial
  have hO := (hP54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁
    (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) hS.2.2.2.2.2.1.1
    (RamifiedCoefficientChains.jumpsLet_win _ hS)).1 hS.1
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hn : nLet i w hw = TwistedPlaces.nLam D w := by
    have h0 : Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
    unfold nLet
    rw [h0]
    exact hb.deg
  have hnR : ((nLet i w hw : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by exact_mod_cast hn
  obtain ⟨mm, k, hmm, hk, hle⟩ := hcol
  refine ⟨mm, k, hmm, hk, hle.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))⟩
  have hK : (rowC C₂).K₁ = 368 ∧ (rowC C₂).K₂ = 2082 ∧ (rowC C₂).K₃ = 22365 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃] <;> norm_num
  rw [hK.1, hK.2.1, hK.2.2]
  unfold RamifiedCoefficientChains.colBd RamifiedCoefficientChains.cD bdCD coreH coreF coreM coreE
  rw [hl', hrk, hb.m_eq, hnR]
  unfold RamifiedCoefficientChains.eBd RamifiedCoefficientChains.lam at he
  rw [hl'] at he hO
  have hHn := Hmax_le d Wd.sz Wd.S Wd.η
  have hth := hpar_le_of_thick Wd.S hA.thick
  have hHle : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ TwistedPlaces.hB L + TwistedPlaces.eta₃ L := by
    have a1 : RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η ≤ Wd.b + Wd.η + Wd.S + Wd.η := by omega
    have a2 : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ ((Wd.b + Wd.η + Wd.S + Wd.η : ℕ) : ℝ) := by
      exact_mod_cast a1
    push_cast at a2 ⊢
    linarith [hb.h_le, hb.η_le]
  have hBb : TwistedPlaces.hB L ≤ 2 * Real.exp (TwistedPlaces.large₂ L) := by
    change TwistedPlaces.hB L ≤ 2 * L.sc.b
    unfold TwistedPlaces.hB
    unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar
    linarith
  have hflt : (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / (D.nd.l i : ℝ) + L.Sc + TwistedPlaces.large₂ L ≤ flat L bd (D.nd.l i) := by
    unfold flat
    have h0 : 0 ≤ TwistedPlaces.eta₃ L := by have := L.etaSz_pos; unfold TwistedPlaces.eta₃; positivity
    split_ifs <;> linarith
  exact GlobalTheory.RowsThick.colBd_le_row (η := (Wd.η : ℝ))
    (H' := ((LiftingTheory.Hmax (nLet i w hw) (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) : ℕ) : ℝ))
    (eta₃ := TwistedPlaces.eta₃ L) (wP := TwistedPlaces.wP L) (Sc := L.Sc) (large₂ := TwistedPlaces.large₂ L)
    (by exact_mod_cast h11) (by positivity) (by positivity) (by positivity) (by positivity) hb.S_le
    (by positivity) hb.η_le (by positivity) hHle (etaP_le_hB L) (one_le_hB L) hBb (Lg_ge_one L)
    (placeWeight_nonneg L) hflt he (by positivity) (by exact_mod_cast hHn) hO

end GlobalTheory.RowsThick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerPartialCoeffBlock
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_partial_coeff_block : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → ∀ h : GA E (m + 1),
    GlobalTheory.JSW.whit (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) h =
      GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ k + 1) h) := by
  first | (exact @GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL) | (exact GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL) | (intros; apply GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL  <;> assumption)
end

