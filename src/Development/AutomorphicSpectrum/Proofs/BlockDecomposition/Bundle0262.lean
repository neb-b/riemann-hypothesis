module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.RelSerreSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobject
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0038
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0229
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0230
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineRestrictionFunctionsNaturalityStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_restriction_functions_naturality : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] (φ : Z ⟶ X) (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)], letI : (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) := ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩; (∀ (W : (φ ⁻¹ᵁ V).toScheme.Opens) (a : A), ((φ ⁻¹ᵁ V).ι.appIso W).hom (toFunctions (A := A) ((φ ⁻¹ᵁ V).ι ''ᵁ W) a) = toFunctions (A := Γ(X, V)) W (toFunctions (A := A) V a)) → ∀ (G : Z.Modules) [G.IsQuasicoherent] (m : ℕ), ∃ g : (idealPow I G m).restrict (φ ⁻¹ᵁ V).ι ⟶ idealPow (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m, g ≫ idealPowι (Ideal.map (toFunctions (A := A) V) I) (G.restrict (φ ⁻¹ᵁ V).ι) m = (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ V).ι).map (idealPowι I G m) := by
  first | exact @GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | exact GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift | (intros; apply GlobalTheory.CompanionTheory.GE.FormalShift.restrict_idealPow_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesSubobjectStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_subobject : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] [CompactSpace X] {E : X.Modules}, IsCoherent E → ∀ D : Subobject E, (D : X.Modules).IsQuasicoherent → ∃ k : ℕ, ∀ n : ℕ, D ⊓ powSub I E (n + k) ≤ (Subobject.map D.arrow).obj (powSub I (D : X.Modules) n) := by
  first | exact @GlobalTheory.CompanionTheory.GE.artinRees_uniform | exact GlobalTheory.CompanionTheory.GE.artinRees_uniform | (intros; apply GlobalTheory.CompanionTheory.GE.artinRees_uniform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedSystemPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_system_pullback : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → ClosedSys I ((Scheme.Modules.pullback φ).obj E) (pullSys I φ E S) := by
  first | exact @GlobalTheory.CompanionTheory.GE.closedSys_pullSys | exact GlobalTheory.CompanionTheory.GE.closedSys_pullSys | (intros; apply GlobalTheory.CompanionTheory.GE.closedSys_pullSys <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CokernelSectionIdealPowerStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cokernel_section_ideal_power : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [Z.Over (Spec (.of A))] (φ : Z ⟶ X) {E : X.Modules} (S : ℕ → Subobject E) (B : Subobject ((Scheme.Modules.pullback φ).obj E)) (n : ℕ), B ⊔ powSub I _ (n + 1) = pullSys I φ E S n → ∀ (V : X.Opens), ∀ x ∈ secs (S n) V, (show Γ(cokernel B.arrow, φ ⁻¹ᵁ V) from (adjMap φ B).app V x) ∈ Set.range ((idealPowι I (cokernel B.arrow) (n + 1)).app (φ ⁻¹ᵁ V)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | exact GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι | (intros; apply GlobalTheory.CompanionTheory.GE.PowImage.adjMap_app_mem_range_idealPowι <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

theorem hE_self_fixed (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma hcm _
  have h2 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, hJ.1 i j, h2]
  ring

theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    {X : Fin 1 → Fin 2 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.hermOne_eq_scal F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)

theorem sph_unique {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

theorem ne_zero_of_mem_sph {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 2 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hA hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg


set_option maxHeartbeats 1000000 in
theorem cnt : TestEx → LSide → RSide → Cnt := by
  intro hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨⟨θ, hθ⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1
  obtain ⟨S, hS⟩ := hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨φ, A, ht, hv0, hvT⟩ := hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S
  have hLt := hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht
  have hRt := hS S (Finset.Subset.refl _) φ A ht
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  obtain ⟨_, -, -, -, -, -, -, hBinf, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Ainf F)
  have := hBinf 1 2
  obtain ⟨hφc, -, -, -, hAS, hAo⟩ := ht
  have hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _) := fun ε =>
    continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧
      ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤ := fun v => by
    have hRv := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)
    have := hB 1 2
    obtain ⟨-, k1, k2⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hco : IsCompact (A v) ∧ IsOpen (A v) := by
      by_cases hv : v ∈ S
      · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
      · rw [hAo v hv]
        exact (_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 2).2.2.2.1 v
    refine ⟨hco.1, hco.2.measurableSet, fun s => ?_⟩
    have := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1
    exact hco.1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A v = latV b v :=
    S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)
  have key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0},
        (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
          ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal) := fun ε => by
    rw [thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β => ?_
    have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))
        (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1))) := hκ β.1 β.2
    obtain ⟨-, e⟩ := _root_.GlobalTheory.CompanionTheory.SW.EulerBox.euler_box F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A
      (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof
    rw [e, mul_assoc]
  simp only [key] at hLt
  have h1 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)
  have h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A :=
    tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)
  have h3 : (κ : ℝ≥0∞) = 1 := by
    have h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj hv0 hvT).1 h4
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.RgMass

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDSpanning

theorem exists_sum_dpow : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  intro B _ J δ z
  refine ⟨(pq B).e.repr z, ?_⟩
  have h := (pq B).e.linearCombination_repr z
  rw [Finsupp.linearCombination_apply] at h
  refine h.symm.trans (Finsupp.sum_congr fun k _ => ?_)
  rw [(eta_std δ).var k, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDSpanning
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeFiltration
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.PDCrit

private theorem pq_isStd_eta {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    (pq B).IsStd δ (eta δ) :=
  Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))

theorem repr_sum {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) :
    (pq B).e.repr (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = b := by
  have hs := pq_isStd_eta δ
  have h1 : (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) =
      Finsupp.linearCombination B (pq B).e b := by
    rw [Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun k _ => ?_
    rw [hs.var k, Algebra.smul_def]
  rw [h1, (pq B).e.repr_linearCombination]

theorem mem_span_iff {B : Type} [CommRing B] (c : B) (z : (pq B).P) :
    z ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, (pq B).e.repr z k ∈ Ideal.span {c} := by
  constructor
  · intro hz k
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  · intro h
    choose d hd using fun k => Ideal.mem_span_singleton'.1 (h k)
    rw [Ideal.mem_span_singleton']
    refine ⟨∑ k ∈ ((pq B).e.repr z).support, d k • (pq B).e k, ?_⟩
    conv_rhs => rw [← (pq B).e.linearCombination_repr z]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hd k, mul_comm (d k • (pq B).e k), ← Algebra.smul_def, smul_smul, mul_comm c (d k)]

private theorem sum_finsupp_single_apply_eq_ite {B : Type} [CommRing B] (s : Finset ℕ) (a : ℕ → B) (k : ℕ) :
    (∑ i ∈ s, Finsupp.single i (a i)) k = if k ∈ s then a k else 0 := by
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mem_fil_sup_iff {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r : ℕ) (c : B)
    (z : (pq B).P) :
    z ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔
      ∀ k, (pq B).e.repr z k ∈ fil δ (r - k) ⊔ Ideal.span {c} := by
  have hT := (_root_.GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  constructor
  · intro hz k
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _), Finsupp.add_apply]
    exact Submodule.add_mem_sup ((hT r a).1 ha k) ((mem_span_iff c s).1 hs k)
  · intro h
    choose a ha s hs hsum using fun k => Submodule.mem_sup.1 (h k)
    have hF : (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) = (pq B).e.repr z := by
      ext k
      rw [Finsupp.add_apply, sum_finsupp_single_apply_eq_ite, sum_finsupp_single_apply_eq_ite]
      split_ifs with hk
      · exact hsum k
      · rw [add_zero]
        exact (Finsupp.notMem_support_iff.1 hk).symm
    have hz : z = (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (a i)) +
        (pq B).e.repr.symm (∑ i ∈ ((pq B).e.repr z).support, Finsupp.single i (s i)) := by
      rw [← map_add (f := _), hF, LinearEquiv.symm_apply_apply]
    rw [hz]
    refine Submodule.add_mem_sup ((hT r _).2 fun k => ?_) ((mem_span_iff c _).2 fun k => ?_)
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact ha k
      · exact Submodule.zero_mem _
    · rw [LinearEquiv.apply_symm_apply, sum_finsupp_single_apply_eq_ite]
      split_ifs
      · exact hs k
      · exact Submodule.zero_mem _

theorem coeff_criteria : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (b : ℕ →₀ B) (r : ℕ) (c : B), ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil (eta δ) r ⊔ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ Ideal.span {algebraMap B (pq B).P c} ↔ ∀ k, b k ∈ Ideal.span {c}) ∧ ((b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) = 0 ↔ ∀ k, b k = 0) := by
  intro B _ J δ b r c
  have hT := (_root_.GlobalTheory.CompanionTheory.PDFil.fil_pdPoly δ (pq B) (eta δ) (pq_isStd_eta δ)).2.2.2
  have hr := repr_sum δ b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hT, hr]
  · rw [mem_fil_sup_iff, hr]
  · rw [mem_span_iff, hr]
  · rw [← LinearEquiv.map_eq_zero_iff (pq B).e.repr, hr]
    simp only [Finsupp.ext_iff, Finsupp.coe_zero, Pi.zero_apply]

end GlobalTheory.CompanionTheory.PDCrit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeUniversal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PDUniv

theorem pdPoly_universal : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'') (f : B →+* C), IsDPMorphism δ δ'' f → ∀ x ∈ J'', ∃! F : (pq B).P →+* C, F.comp (algebraMap B (pq B).P) = f ∧ F ((pq B).e 1) = x ∧ IsDPMorphism (eta δ) δ'' F := by
  intro B _ J δ C _ J'' δ'' f hf x hx
  have hη : (pq B).IsStd δ (eta δ) := by
    unfold eta
    exact Classical.choose_spec (FubiniStudyChowHeightFormula₂.Adr.exists_std B J δ (pq B))
  letI : Algebra B C := f.toAlgebra
  let L : (pq B).P →ₗ[B] C := (pq B).e.constr ℕ fun n => δ''.dpow n x
  have hL : ∀ n, L ((pq B).e n) = δ''.dpow n x := fun n => (pq B).e.constr_basis ℕ _ n
  have h1 : L 1 = 1 := by
    rw [← (pq B).e_zero, hL, δ''.dpow_zero hx]
  have hbil : (LinearMap.mul B (pq B).P).compr₂ L = (LinearMap.mul B C).compl₁₂ L L := by
    refine (pq B).e.ext fun m => (pq B).e.ext fun n => ?_
    show L ((pq B).e m * (pq B).e n) = L ((pq B).e m) * L ((pq B).e n)
    rw [(pq B).e_mul, ← nsmul_eq_mul, map_nsmul]
    simp only [hL]
    rw [nsmul_eq_mul, δ''.mul_dpow hx]
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => LinearMap.congr_fun₂ hbil a b
  let F : (pq B).P →+* C := (AlgHom.ofLinearMap L h1 hmul).toRingHom
  have hFL : ∀ p, F p = L p := fun p => rfl
  have hFe : ∀ n, F ((pq B).e n) = δ''.dpow n x := fun n => (hFL _).trans (hL n)
  have hFa : ∀ b, F (algebraMap B (pq B).P b) = f b := fun b =>
    (AlgHom.ofLinearMap L h1 hmul).commutes b
  have hcomp : F.comp (algebraMap B (pq B).P) = f := RingHom.ext hFa
  have he1 : F ((pq B).e 1) = x := by rw [hFe, δ''.dpow_one hx]
  have he1mem : (pq B).e 1 ∈ (pq B).ext J := by
    unfold PDPoly.ext PDPoly.aug
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)
  have hSspan : (pq B).ext J = Ideal.span ((algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1)) := by
    rw [Ideal.span_union]
    rfl
  have hS' : ∀ s ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪ Set.range fun n : ℕ => (pq B).e (n + 1),
      F s ∈ J'' := by
    rintro s (⟨j, hj, rfl⟩ | ⟨n, rfl⟩)
    · rw [hFa]
      exact hf.ideal_comp (Ideal.mem_map_of_mem f hj)
    · rw [hFe]
      exact δ''.dpow_mem (Nat.succ_ne_zero n) hx
  have hdpS : ∀ {n : ℕ}, ∀ a ∈ (algebraMap B (pq B).P '' (J : Set B)) ∪
      Set.range fun n : ℕ => (pq B).e (n + 1), F ((eta δ).dpow n a) = δ''.dpow n (F a) := by
    intro n a ha
    rcases ha with ⟨j, hj, rfl⟩ | ⟨m, rfl⟩
    · rw [hη.dp.dpow_comp j hj, hFa, hFa, hf.dpow_comp j hj]
    · dsimp only
      have hv : (pq B).e (m + 1) = (eta δ).dpow (m + 1) ((pq B).e 1) := (hη.var (m + 1)).symm
      rw [hv, (eta δ).dpow_comp (Nat.succ_ne_zero m) he1mem]
      simp only [hη.var, map_mul, map_natCast, hFe]
      rw [δ''.dpow_comp (Nat.succ_ne_zero m) hx]
  have hdp : IsDPMorphism (eta δ) δ'' F := IsDPMorphism.on_span (eta δ) δ'' hSspan hS' hdpS
  refine ⟨F, ⟨hcomp, he1, hdp⟩, ?_⟩
  rintro G ⟨hG1, hG2, hG3⟩
  have hGa : ∀ b, G (algebraMap B (pq B).P b) = f b := fun b => RingHom.congr_fun hG1 b
  have hGe : ∀ n, G ((pq B).e n) = δ''.dpow n x := by
    intro n
    rw [← hη.var n, ← hG3.dpow_comp _ he1mem, hG2]
  let Ga : (pq B).P →ₐ[B] C := { G with commutes' := hGa }
  have hlin : Ga.toLinearMap = L := (pq B).e.ext fun n => by
    show G ((pq B).e n) = L ((pq B).e n)
    rw [hGe, hL]
  ext p
  exact LinearMap.congr_fun hlin p

end GlobalTheory.CompanionTheory.PDUniv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerLogMultiplicativeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_log_multiplicative : ∀ {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ),
    (∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) → ∀ v w : A, v - 1 ∈ J → w - 1 ∈ J →
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  first | exact @GlobalTheory.CompanionTheory.TruncLog.dlog_mul | exact GlobalTheory.CompanionTheory.TruncLog.dlog_mul | (intros; apply GlobalTheory.CompanionTheory.TruncLog.dlog_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousEpsilonPowerStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_epsilon_power : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), ∃ η : ((base l).cont ℤ_[l]).A,
  (∀ (m : ℕ) (z : ℤ_[l]), Hom.f ((base l).evCont z) η - (base l).s (ε.e 0) ^ (PadicInt.toZModPow m z).val ∈ Ideal.span {(base l).pi ^ (l ^ m)}) ∧
  Hom.f (contShift (base l)) η = ((base l).cont ℤ_[l]).s (ε.e 0) * η := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | exact GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta | (intros; apply GlobalTheory.CompanionTheory.ContUniv.EtaFn.exists_eta <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_acris_truncated_witt : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) (n : ℕ), letI := (Mid.wn r n).toAlgebra; Module.Flat (Wc.Wm l r.k n) ((base l).Acr n) := by
  first | exact @GlobalTheory.CompanionTheory.CrisFlat.flat_acr | exact GlobalTheory.CompanionTheory.CrisFlat.flat_acr | (intros; apply GlobalTheory.CompanionTheory.CrisFlat.flat_acr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevelStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_coarsen_to_lower_level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) →
  ∀ {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A), CompleteOrthogonalIdempotents e →
  (∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) →
  CompleteOrthogonalIdempotents (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
  ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.coi_descend | exact GlobalTheory.CompanionTheory.ContUniv.coi_descend | (intros; apply GlobalTheory.CompanionTheory.ContUniv.coi_descend <;> assumption)
end

