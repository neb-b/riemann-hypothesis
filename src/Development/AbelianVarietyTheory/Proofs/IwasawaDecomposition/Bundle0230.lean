module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualMeasureGlobalConstRankOnly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadricFibreMeasureEqSmulNormalisedProduct
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.XbetaScale

theorem continuous_qR {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem units_inf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | ∀ w, c w ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine Iff.trans ?_ (Pi.isUnit_iff (x := c)).symm
  simp only [isUnit_iff_ne_zero]

theorem units_fv (K : Type) [Field K] : {c : K | c ≠ 0} = {c | IsUnit c} := by
  ext c
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero]

theorem fib_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    (hR : Nice R) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E))
    (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (r t : ℝ≥0) (ht : t ≠ 0)
    (hν : (t • ν).IsAddHaarMeasure) (hβ : IsUnit β) (hm : FibAt R σ J μ ν β m)
    (fib : R → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily (r • μ) (fun X => qR R σ J (X 0)) id Set.univ (t • ν) {c | IsUnit c} fib) :
    fib β = (r / t) • m := by
  obtain ⟨fib0, h0, rfl⟩ := hm
  exact (_root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ R hR M J (r • μ) (t • ν) β _ hν hβ
    ⟨_, GlobalTheory.GramFibreRescale.isFibreFamily_smul h0 r t ht, rfl⟩).2.2 _ ⟨fib, hfib, rfl⟩

end GlobalTheory.GaugeEx.XbetaScale

namespace GlobalTheory.GaugeEx

open XbetaScale

theorem isXbetaMeasure_iff_smul_std : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b), ∃ κ : ℕ → ℝ≥0, (∀ M, κ M ≠ 0) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F) (ψ : AddChar (AF F) ℂ) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), 1 ≤ M → IsHermND σ J → β ≠ 0 → IsCharAF F ψ → IsStdX s σ J β ν → ∀ νX, IsXbetaMeasure F E σ M J ψ β νX ↔ νX = κ M • ν := by
  intro F E _ _ _ _ _ σ hσ d b s
  choose κ hκ0 hκ using _root_.GlobalTheory.GaugeSdMain.selfDual_const F E σ hσ d b s
  refine ⟨κ, hκ0, ?_⟩
  intro M J β ψ ν hM hJ hβ hψ hν
  obtain ⟨mi, mv, hmi, hmv, hprod⟩ := hν
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have hβi : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have hβv : ∀ v : HeightOneSpectrum (𝓞 F), IsUnit (algebraMap F (Fv F v) β) :=
    fun v => (isUnit_iff_ne_zero.2 hβ).map _

  have key : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∀ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf →
      ∀ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) →
      IsProd b (κ M • ν) (fibInf (algebraMap F (Ainf F) β))
        (fun v => fibV v (algebraMap F (Fv F v) β)) := by
    intro μi hμi νi hνi μv hμv νv hνv fibInf hfi fibV hfv
    obtain ⟨ri, ti, r, t, e1, e2, e3, e4, -, hti, -, ht, hfin, hk⟩ :=
      hκ M ψ J hψ hJ μi νi μv νv hμi hνi hμv hνv
    have a1 : fibInf (algebraMap F (Ainf F) β) = (ri / ti) • mi := by
      refine fib_eq_smul σ (Ainf F) nI J _ _ _ mi ri ti hti (e2 ▸ hνi.1) hβi hmi fibInf ?_
      rw [← e1, ← e2, ← units_inf]
      exact hfi
    have a2 : (fun v => fibV v (algebraMap F (Fv F v) β)) = fun v => (r v / t v) • mv v := by
      funext v
      refine fib_eq_smul σ (Fv F v) (nV v) J _ _ _ (mv v) (r v) (t v) (ht v) (e4 v ▸ (hνv v).1)
        (hβv v) (hmv v) (fibV v) ?_
      rw [← e3, ← e4, ← units_fv]
      exact hfv v
    rw [a1, a2, ← hk]
    exact GlobalTheory.T.restrictedProduct_measure_smul_factors_eq_smul F E d b 1 M ν mi mv (ri / ti) (fun v => r v / t v) hprod hfin

  obtain ⟨⟨νi0, hνi0, -⟩, hWi⟩ := _root_.GlobalTheory.GaugeEx.SdInf.existsUnique_selfDual_inf F E σ hσ ψ hψ
  obtain ⟨μi0, hμi0, -⟩ := hWi M J hJ
  choose νv0 hνv0 using fun v => (_root_.GlobalTheory.SelfDualFinite.existsUnique_selfDual_finite F E σ hσ ψ hψ v).1.exists
  choose μv0 hμv0 using fun v => ((_root_.GlobalTheory.SelfDualFinite.existsUnique_selfDual_finite F E σ hσ ψ hψ v).2 M J hJ).exists
  have exI : ∀ μi, SdW F E σ M J (Ainf F) (psiInf F ψ) 1 μi →
      ∀ νi, SdR (Ainf F) (psiInf F ψ) νi →
      ∃ fibInf : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi
        {c : Ainf F | ∀ w, c w ≠ 0} fibInf :=
    fun μi hμi νi hνi => _root_.GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf F E σ hσ M J μi νi hM hJ hμi.1 hνi.1
  have exV : ∀ μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) 1 (μv v)) →
      ∀ νv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v),
      (∀ v, SdR (Fv F v) (psiV F ψ v) (νv v)) →
      ∃ fibV : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fibV v)) := by
    intro μv hμv νv hνv
    choose fibV hfibV using fun v =>
      (GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM hJ (μv v) (hμv v).1 (νv v) (hνv v).1).2
    exact ⟨fibV, hfibV⟩
  intro νX
  constructor
  · rintro ⟨-, h⟩
    obtain ⟨fi, hfi⟩ := exI μi0 hμi0 νi0 hνi0
    obtain ⟨fv, hfv⟩ := exV μv0 hμv0 νv0 hνv0
    have h1 := (((((h.2 μi0 hμi0).2 νi0 hνi0).2 μv0 hμv0).2 νv0 hνv0).2 fi hfi).2 fv hfv
    have h2 := _root_.GlobalTheory.GaugeEx.ProdInt.integral_pure F E d b 1 M _ _ _ (key μi0 hμi0 νi0 hνi0 μv0 hμv0 νv0 hνv0 fi hfi fv hfv)
    refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b 1 M _ _ fun Φ Φinf Φf Φv c1 c2 c3 c4 => ?_
    obtain ⟨p1, -, p3⟩ := h1 d b Φ Φinf Φf Φv c1 c2 c3 c4
    obtain ⟨q1, -, q3⟩ := h2 d b Φ Φinf Φf Φv c1 c2 c3 c4
    exact ⟨p1, q1, p3.trans q3.symm⟩
  · rintro rfl
    refine ⟨?_, ⟨μi0, hμi0⟩, fun μi hμi => ⟨⟨νi0, hνi0⟩, fun νi hνi => ⟨⟨μv0, hμv0⟩, fun μv hμv =>
      ⟨⟨νv0, hνv0⟩, fun νv hνv => ⟨exI μi hμi νi hνi, fun fi hfi => ⟨exV μv hμv νv hνv, fun fv hfv =>
      _root_.GlobalTheory.GaugeEx.ProdInt.integral_pure F E d b 1 M _ _ _ (key μi hμi νi hνi μv hμv νv hνv fi hfi fv hfv)⟩⟩⟩⟩⟩⟩
    have hz := (_root_.GlobalTheory.GaugeEx.isProd_basic F E d b 1 M ν mi mv hprod).2.2.2
      {Y | qR (Ainf F) σ J (Y 0) = algebraMap F _ β}
      (fun v => {Y | qR (Fv F v) σ J (Y 0) = algebraMap F _ β})
      (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet
      (fun v => (isClosed_eq (continuous_qR _ σ J) continuous_const).measurableSet)
      (_root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ _ nI M J _ _ _ mi s.haar_nuI hβi hmi).1
      (fun v => (_root_.GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ _ (nV v) M J _ _ _ (mv v) (s.haar_nuV v) (hβv v) (hmv v)).1)
    have hs : {X : Fin 1 → Fin M → AF F ⊗[F] E | qR (AF F) σ J (X 0) ≠ algebraMap F (AF F) β} =
        {X | ¬ (projInf X ∈ {Y : Fin 1 → Fin M → Ainf F ⊗[F] E |
            qR (Ainf F) σ J (Y 0) = algebraMap F _ β} ∧
          ∀ v, projV v (projFin X) ∈ {Y : Fin 1 → Fin M → Fv F v ⊗[F] E |
            qR (Fv F v) σ J (Y 0) = algebraMap F _ β})} := by
      ext X
      exact not_congr ((GlobalTheory.GaugeEx.q_and_unitary_local_components F E σ M J).1 (X 0) β)
    rw [Measure.smul_apply, hs, hz, smul_zero]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevFormEqZeroOfSmoothOrbit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem cyc_mul_mem_UJset {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have h1 : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have h2 : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2]

theorem clm_eq_zero_of_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ)
    (L : H →L[ℂ] ℂ) {v : H} (hv : v ≠ 0) (h : ∀ g ∈ UJset ε, L (σ g v) = 0) (w : H) : L w = 0 := by
  let S : Submodule ℂ H :=
    { carrier := {x | ∀ g ∈ UJset ε, L (σ g x) = 0}
      add_mem' := fun ha hb g hg => by rw [map_add (f := _), map_add (f := _), ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by rw [map_zero, map_zero]
      smul_mem' := fun c x ha g hg => by rw [map_smul, map_smul, ha g hg, smul_zero] }
  have hc : IsClosed (S : Set H) := by
    have : (S : Set H) = ⋂ g ∈ UJset ε, {x | L (σ g x) = 0} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (L.continuous.comp (σ g).continuous) continuous_const
  have hst : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S := fun g hg x hx a ha => by
    have := hx (a * g) (cyc_mul_mem_UJset ha hg)
    rwa [hσ.1.2 a ha g hg] at this
  rcases hi S hc hst with h0 | h0
  · have : v ∈ S := h
    rw [h0] at this
    exact absurd this hv
  · have : w ∈ S := by rw [h0]; trivial
    have h1 := this 1 (by show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp)
    rwa [hσ.1.1] at h1

theorem sobCont_eq_zero_of_orbit : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∀ v ∈ smSub G (trRep σ P), v ≠ 0 → (∀ g ∈ UJset ε, ℓ (σ g v) = 0) → ∀ w ∈ smSub G (trRep σ P), ℓ w = 0 := by
  intro n ε H _ _ _ σ P G hP hG hσ hi ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨hb, hs⟩ := GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ ℓ hℓ
  have key : ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = 0 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hb φ hφ
    let L : H →L[ℂ] ℂ :=
      (ℓ ∘ₗ GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2).mkContinuousOfExistsBound ⟨C, hC⟩
    refine clm_eq_zero_of_orbit hσ hi L hv0 (fun g hg => ?_) w
    show ℓ (gard ε σ φ (σ g v)) = 0
    rw [(hs _ (sigma_mem hP hG hσ hv hg)).2 φ hφ]
    have : ∀ a : Formalism.REAL.UJ ε, ℓ (σ (umat a) (σ g v)) = 0 := fun a => by
      have := h0 (umat a * g) (cyc_mul_mem_UJset a.2 hg)
      rwa [hσ.1.2 _ a.2 g hg] at this
    simp [this]
  have := eq_zero_of_forall_test (hs w hw).1 fun φ hφ => by rw [← (hs w hw).2 φ hφ, key φ hφ]
  have e : σ (umat (1 : Formalism.REAL.UJ ε)) w = w := by
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  simpa only [e] using this

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrongApproximationUpperUnitriangularFiniteAdele
section
noncomputable section

namespace GlobalTheory.UnipApproxGL

open NumberField IsDedekindDomain Matrix PIW.ClassFinD

variable {F : Type} [Field F] [NumberField F]

theorem approx (x e : FiniteAdeleRing (𝓞 F) F) :
    ∃ r : F, e * (x + algebraMap F (FiniteAdeleRing (𝓞 F) F) r) ∈ Ohat F := by
  have hU : IsOpen ((fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) ⁻¹'
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F)) :=
    ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_Oint.preimage (continuous_const.mul (continuous_const.add continuous_id))
  have h0 : (fun y : FiniteAdeleRing (𝓞 F) F => e * (x + y)) (-x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F := by
    show e * (x + -x) ∈ ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.Oint F
    rw [add_neg_cancel, mul_zero]
    exact (Ohat F).zero_mem
  obtain ⟨r, hr⟩ := (PI.UnipApproxD.additive_dense_integers F).exists_mem_open hU ⟨-x, h0⟩
  exact ⟨r, hr⟩

theorem row_exists (n : ℕ) (u : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hu : IsUpperUni u) (i : Fin n) (e : Fin n → FiniteAdeleRing (𝓞 F) F) :
    ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j, i < j → e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
  classical
  have key : ∀ m : ℕ, ∃ y : Fin n → F, y i = 1 ∧ (∀ k, k < i → y k = 0) ∧
      ∀ j : Fin n, i < j → j.val < m →
        e j * ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j ∈ Ohat F := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun k => if k = i then 1 else 0, by simp, fun k hk => ?_, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      simp [ne_of_lt hk]
    | succ m ih =>
      obtain ⟨y, hy1, hy0, hyc⟩ := ih
      by_cases h : ∃ hm : m < n, i < (⟨m, hm⟩ : Fin n)
      · obtain ⟨hm, him⟩ := h
        obtain ⟨r, hr⟩ := approx (∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k ⟨m, hm⟩)
          (e ⟨m, hm⟩)
        have hsum : ∀ j, ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F)
              (y k + if k = (⟨m, hm⟩ : Fin n) then r else 0) * u k j
            = ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y k) * u k j +
                algebraMap F (FiniteAdeleRing (𝓞 F) F) r * u ⟨m, hm⟩ j := by
          intro j
          simp only [map_add (f := _), add_mul, Finset.sum_add_distrib, apply_ite (algebraMap F _), map_zero,
            ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        refine ⟨fun k => y k + if k = (⟨m, hm⟩ : Fin n) then r else 0, ?_, ?_, ?_⟩
        · simp [hy1, ne_of_lt him]
        · intro k hk
          simp [hy0 k hk, ne_of_lt (hk.trans him)]
        · intro j hij hjm
          rw [hsum]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
          · rw [hu.1 ⟨m, hm⟩ j (by rw [Fin.lt_def]; exact hj), mul_zero, add_zero]
            exact hyc j hij hj
          · have hjM : j = ⟨m, hm⟩ := Fin.ext hj
            subst hjM
            rw [hu.2, mul_one]
            exact hr
      · refine ⟨y, hy1, hy0, fun j hij hjm => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjm with hj | hj
        · exact hyc j hij hj
        · exfalso
          have hm : m < n := hj ▸ j.isLt
          exact h ⟨hm, by rwa [show (⟨m, hm⟩ : Fin n) = j from Fin.ext hj.symm]⟩
  obtain ⟨y, h1, h2, h3⟩ := key n
  exact ⟨y, h1, h2, fun j hij => h3 j hij j.isLt⟩

theorem matInt_inv_of_upperUni {n : ℕ} (g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))
    (hg : IsUpperUni g.val) (hi : MatInt g.val) : MatInt g⁻¹.val := by
  have hdet : g.val.det = 1 := by
    rw [det_of_upperTriangular (fun i j hij => hg.1 i j hij)]
    simp [hg.2]
  have h1 : g.val * adjugate g.val = 1 := by rw [mul_adjugate, hdet, one_smul]
  have hinv : g⁻¹.val = adjugate g.val := by
    calc g⁻¹.val = g⁻¹.val * (g.val * adjugate g.val) := by rw [h1, mul_one]
      _ = adjugate g.val := by rw [← mul_assoc, Units.inv_mul, one_mul]
  let W' : Matrix (Fin n) (Fin n) (Ohat F) := fun i j => ⟨g.val i j, hi i j⟩
  have hW : g.val = (Ohat F).subtype.mapMatrix W' := by ext i j; rfl
  intro i j
  rw [hinv, hW, ← RingHom.map_adjugate]
  exact ((adjugate W') i j).2

theorem unipApprox : PIW.ClassFinD.UnipApprox := by
  classical
  intro F _ _ n u t hu ht
  obtain ⟨τ, rfl⟩ := diag_eq_diagGL t ht
  choose y hy1 hy0 hyc using fun i => row_exists n u.val hu i
    (fun j => (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j)
  let Y : Matrix (Fin n) (Fin n) F := fun i k => y i k
  have hdet : Y.det = 1 := by
    rw [det_of_upperTriangular (fun i k hki => hy0 i k hki)]
    simp [Y, hy1]
  let Yg : GL (Fin n) F :=
    ((Matrix.isUnit_iff_isUnit_det Y).mpr (by rw [hdet]; exact isUnit_one)).unit

  let P : Fin n → Fin n → FiniteAdeleRing (𝓞 F) F := fun i j =>
    ∑ k, algebraMap F (FiniteAdeleRing (𝓞 F) F) (y i k) * u.val k j
  have hPlow : ∀ i j, j < i → P i j = 0 := by
    intro i j hji
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with hk | hk
    · rw [hy0 i k hk, map_zero, zero_mul]
    · rw [hu.1 k j (lt_of_lt_of_le hji hk), mul_zero]
  have hPdiag : ∀ i, P i i = 1 := by
    intro i
    show ∑ k, _ = _
    rw [Finset.sum_eq_single i]
    · rw [hy1 i, map_one, one_mul, hu.2]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hk | hk
      · rw [hy0 i k hk, map_zero, zero_mul]
      · rw [hu.1 k i hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  let w := (diagGL n τ)⁻¹ * glIncl F n Yg * u * diagGL n τ
  have hw : ∀ i j, w.val i j =
      (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j := by
    intro i j
    simp only [w, ← map_inv, Units.val_mul, diagGL_val, Matrix.mul_assoc, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
    rw [Matrix.mul_apply]
    rfl
  have hwu : IsUpperUni w.val := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [hw, hPlow i j hji, mul_zero, zero_mul]
    · rw [hw, hPdiag, mul_one, Units.inv_mul]
  have hwi : MatInt w.val := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [hw]
      have := hyc i j hij
      rw [show (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * P i j * τ j =
        (((τ i)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) * τ j * P i j by ring]
      exact this
    · rw [hwu.2]; exact (Ohat F).one_mem
    · rw [hwu.1 i j hji]; exact (Ohat F).zero_mem
  refine ⟨Yg⁻¹, w, ⟨hwi, matInt_inv_of_upperUni w hwu hwi⟩, ?_⟩
  simp only [w, map_inv]
  group

end GlobalTheory.UnipApproxGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersion
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem support_pushforward_subset_image_of_isClosedImmersion :
    ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules),
      support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  intro X Y g _ E y hy
  by_contra hyn
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hy
  apply hy
  have hemb := g.isClosedEmbedding
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t

  let Z0 : Set Y := {z | ∃ hz : z ∈ g ⁻¹ᵁ U, E.presheaf.germ (g ⁻¹ᵁ U) z hz s = 0}
  have hZ0 : IsOpen Z0 := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hz, hzs⟩
    obtain ⟨W, hzW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq E.presheaf z hz hz s 0
      (by rw [hzs, map_zero])
    refine ⟨W, fun z' hz' => ⟨(leOfHom iU) hz', ?_⟩, W.2, hzW⟩
    have := TopCat.Presheaf.germ_res_apply E.presheaf iU z' hz' s
    rw [he, map_zero, map_zero] at this
    exact this.symm
  obtain ⟨V', hV', hV'e⟩ := hemb.isInducing.isOpen_iff.1 hZ0
  let V : X.Opens := U ⊓ ⟨V' ∪ (Set.range g)ᶜ, hV'.union hemb.isClosed_range.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hyU, ?_⟩
    by_cases hr : y ∈ Set.range g
    · obtain ⟨z, rfl⟩ := hr
      have hzs : z ∉ support E := fun h => hyn ⟨z, h, rfl⟩
      have hz : z ∈ g ⁻¹ᵁ U := hyU
      refine Or.inl (show z ∈ g ⁻¹' V' from hV'e ▸ ⟨hz, (notMem_support_iff.1 hzs).elim _ _⟩)
    · exact Or.inr hr
  have hVU : V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV]
  have h0 : ((Scheme.Modules.pushforward g).obj E).presheaf.map (homOfLE hVU).op s = 0 := by
    refine section_eq_zero_of_germ (F := E) _ fun z hz => ?_
    have hz' : z ∈ Z0 := by
      rw [← hV'e]
      rcases hz.2 with h | h
      · exact h
      · exact absurd ⟨z, rfl⟩ h
    obtain ⟨hzU, hzs⟩ := hz'
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf ((Opens.map g.base).map (homOfLE hVU)) z hz s).trans hzs
  rw [h0, map_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypAddOfDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TypeSum in
theorem GlobalTheory.TypeSum.typAdd_of_discreteSeries : ∀ D : D7, (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) → TypAdd D := by
  intro D hex huniq θ hθ V hV τ S hS
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  refine ⟨(GlobalTheory.TypeAtTest.isTypeAt_zero θ V).2 ?_, fun φ φ' _ _ h h' => ?_⟩
  · obtain ⟨H, i1, i2, σ, hσ⟩ := hex _ ε₀ lam₀ hP₀
    obtain ⟨P, h1, h2⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
    exact ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, h1, h2⟩
  obtain ⟨H, i1, i2, σ, lam, ε, P, hE, hσ, hP, hG, hx⟩ := h
  obtain ⟨H', j1, j2, σ', lam', ε', P', hE', hσ', hP', hG', hx'⟩ := h'
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE' hE₀
  obtain ⟨U, hU⟩ := huniq _ _ _ hP₀ H' H σ' σ hσ' hσ
  refine ⟨H, i1, i2, σ, _, _, P, hE, hσ, hP, hG, fun x => ?_⟩
  exact hasTypeAll_iff.1 (hasTypeAll_add_of_equiv hσ.2.2.1 U hU hP hP' hG hG'
    (f := fun g => φ (x * atTau θ V τ g)) (f' := fun g => φ' (x * atTau θ V τ g))
    (hasTypeAll_iff.2 (hx x)) (hasTypeAll_iff.2 (hx' x)))
end

