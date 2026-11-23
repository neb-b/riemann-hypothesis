module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLevelSphericalOffSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOntoSph

variable {D : D7}


open Classical in
theorem sep_level {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : OffS D c.S P) : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  rintro PP (h | h)
  · rw [hPg] at h
    exact GlobalTheory.HeckeOffLevel.sep_of_offS hP (by unfold Com.S; exact Finset.mem_image.2 ⟨PP, h, rfl⟩)
  · rw [hQ] at h
    exact absurd h (Finset.notMem_empty _)

theorem exists_unif_of_F (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (GlobalTheory.InertOfConj.unram D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap] at h2
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.1 h2
  exact ⟨x, algebraMap _ _ x, rfl, Ideal.mem_comap.1 hx, fun h => hx2 (Ideal.mem_comap.2 h)⟩

theorem level_spherical_off_S : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧
    SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L,
      ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
      (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  intro D c _ j _ s hs
  obtain ⟨N, hB, hNP⟩ := hs.base
  have hoff : ∀ P, OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S := fun P => GlobalTheory.GoodPrimes.offS_iff _ P
  have key := fun P e f (hP : OffS D c.S P) (hi : IsPrimeIdem P e f) =>
    (GlobalTheory.LevSplit.lev_split s.V s.β s.Λ N s.L hB).2 P e f hi (hNP P ((hoff P).1 hP)) (sep_level hs hP)
  have hex := fun P => (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V).2.1 P
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P e f hP hi => (key P e f hP hi).2.2, hoff, exists_unif_of_F⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    exact ⟨e, f, hi, h1, h2⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    refine ⟨e, f, hi, h1, fun g hg hf => ?_⟩
    show conj (Lev.levChi s.V s.β s.L g) = 1
    rw [h2 g hg hf, map_one]

end GlobalTheory.ChainOntoSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepRealThetaRuleOfNodesFarApart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.ChainParOfGap

theorem chainPar_of_nodeGap : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ k, ChainPar D k := by
  intro D h k
  unfold GlobalTheory.Chain.ChainPar
  intro τ
  obtain ⟨al, be, ga, de, hc, h1, h2⟩ := GlobalTheory.ArchRec.ParChain.parChain D k τ
  unfold GlobalTheory.ArchRec.Centred at hc
  unfold Formalism.MainNotions.SchurIrreducible.DataAR
  refine ⟨al, be, ga, de, ⟨hc.1, hc.2.2 h⟩, hc.2.1, ?_, ?_⟩
  · rw [h1]
    clear hc h1 h2 h
    congr 1
    unfold expT GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alT
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
  · rw [h2]
    clear hc h1 h2 h
    congr 1
    unfold expS GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.alS
    rcases Nat.even_or_odd (k : ℕ) with hk | hk
    · have ho : Odd ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Odd (k : ℕ) := Nat.not_odd_iff_even.mpr hk
      have hne2 : ¬ Even ((k : ℕ) + 1) := Nat.not_even_iff_odd.mpr ho
      simp [ho, hk, hne, hne2] <;> ring
    · have ho : Even ((k : ℕ) + 1) := hk.add_one
      have hne : ¬ Even (k : ℕ) := Nat.not_even_iff_odd.mpr hk
      have hne2 : ¬ Odd ((k : ℕ) + 1) := Nat.not_odd_iff_even.mpr ho
      simp [ho, hk, hne, hne2] <;> ring

end GlobalTheory.Corev.ChainParOfGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {f : WO S T → ℂ}

theorem thetaKO_left_fst (hω : IsWeilDatumO ψ S T χS χT om) (hf : IsThetaFunO ψ S T f) :
    ∀ γ ∈ GQ S, ∀ g h, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g h => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  unfold thetaKO
  rw [e, map_mul]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

theorem thetaKO_le_quotHeight {θ : InfFam D} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    (hf : IsThetaFunO ψ S T f) :
    ∃ (K : ℝ) (A : ℕ), 0 ≤ K ∧ ∀ g h, ‖thetaKO om g h f‖ ≤ K * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, hC0, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  have hb := (hC χS χT om hω μ 𝓕 hμ f hl).2
  have hK : 0 ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A := by positivity
  refine ⟨_, A, hK, fun g h => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  rw [← thetaKO_left_fst hω hf γ hγ g h, ← GlobalTheory.Chain.LiftConv.thetaKO_left hω hf (γ * g) γ' hγ' h]
  refine (hb _ _).trans ?_
  have e : C * (sobO ψ θ μ 𝓕 d f).toReal * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A =
      C * (sobO ψ θ μ 𝓕 d f).toReal * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos (height_pos S _) (height_pos T _)).le
    (mul_le_mul h1 h2 (height_pos T _).le (by linarith [quotHeight_pos S g])) A) (by positivity)

end GlobalTheory.ChainOnto.ThetaSwap

namespace GlobalTheory.ChainOnto.ThetaSwap

open GlobalTheory.Grow GlobalTheory.Size

theorem integrable_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {ν : Measure (GA D S)} {X : Set (GA D S)} {ν' : Measure (GA D T)}
    {X' : Set (GA D T)} (hν : ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ S) X ν) (hν' : ν'.IsHaarMeasure)
    (hX' : IsFundamentalDomain (GQ T) X' ν') {G : GA D S → ℂ} {F : GA D T → ℂ} (hG : RapidDec S G)
    (hF : RapidDec T F) :
    Integrable (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g))
      ((ν'.restrict X').prod (ν.restrict X)) := by
  obtain ⟨-, -, -, hS2, hSB⟩ := Formalism.IndefR.Eqv.ga_facts D S
  obtain ⟨-, -, -, hT2, hTB⟩ := Formalism.IndefR.Eqv.ga_facts D T
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  obtain ⟨K, A, hK, hb⟩ := thetaKO_le_quotHeight hθ hω hf
  obtain ⟨B, hB⟩ := hG.decay A
  obtain ⟨B', hB'⟩ := hF.decay A
  have hc : Continuous (Function.uncurry fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) := by
    have h1 : Continuous fun p : GA D T × GA D S => thetaKO om p.2 p.1 f :=
      (hω.om_cont f hf 0).comp (continuous_snd.prodMk continuous_fst)
    exact (h1.mul (hF.continuous.comp continuous_fst)).mul
      (Complex.continuous_conj.comp (hG.continuous.comp continuous_snd))
  refine Integrable.of_bound hc.aestronglyMeasurable (K * B * B') (.of_forall fun p => ?_)
  obtain ⟨h, g⟩ := p
  have hq := (pow_pos (quotHeight_pos S g) A).le
  have hq' := (pow_pos (quotHeight_pos T h) A).le
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) hq).trans (hB g)
  calc ‖Function.uncurry (fun (h : GA D T) (g : GA D S) => thetaKO om g h f * F h * conj (G g)) (h, g)‖
        = ‖thetaKO om g h f‖ * ‖F h‖ * ‖G g‖ := by simp [Function.uncurry, norm_mul]
    _ ≤ K * (quotHeight S g * quotHeight T h) ^ A * ‖F h‖ * ‖G g‖ := by gcongr; exact hb g h
    _ = K * (‖G g‖ * quotHeight S g ^ A) * (‖F h‖ * quotHeight T h ^ A) := by ring
    _ ≤ K * B * B' := by
        gcongr
        · exact hB g
        · exact hB' h

theorem integral_swap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ →
    IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ (ν : Measure (GA D S)) (X : Set (GA D S))
    (ν' : Measure (GA D T)) (X' : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) X ν →
    ν'.IsHaarMeasure → IsFundamentalDomain (GQ T) X' ν' → ∀ (G : GA D S → ℂ) (F : GA D T → ℂ),
    GlobalTheory.Grow.RapidDec S G → GlobalTheory.Grow.RapidDec T F →
    ∫ h in X', ∫ g in X, thetaKO om g h f * F h * conj (G g) ∂ν ∂ν' =
      ∫ g in X, ∫ h in X', thetaKO om g h f * F h * conj (G g) ∂ν' ∂ν := by
  intro D ψ θ S T χS χT om hθ hω f hf ν X ν' X' hν hX hν' hX' G F hG hF
  have : IsFiniteMeasure (ν.restrict X) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol S ν X hν hX).ne
  have : IsFiniteMeasure (ν'.restrict X') :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol T ν' X' hν' hX').ne
  exact integral_integral_swap (integrable_prod hθ hω hf hν hX hν' hX' hG hF)

end GlobalTheory.ChainOnto.ThetaSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro hgap c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := _root_.GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe hgap c hc k hk s s' hs hs' p hp u B hB hL
  have key := _root_.GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan hgap c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj hgap c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar hgap c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hF
  · have : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
    rw [← this]; exact hPF

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainHeckeParameterInjectivePlacewise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSupBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology Pointwise

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem lintegral_translate (hψ : IsStdChar D ψ (-1)) {φ : WO S T → ℂ} (hφ : IsThetaFunO ψ S T φ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hm : IsCovolOne (ratL T S) μ 𝓕) (y : WO S T) :
    ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨-, hN⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  obtain ⟨N, hN⟩ := hN φ hφ.cont (theta_norm_periodic hψ hφ)
  have hμ := hm.1
  have hs : IsAddFundamentalDomain (ratL T S) ((fun w => -y + w) ⁻¹' 𝓕) μ :=
    hm.2.1.preimage_of_equiv (measurePreserving_add_left μ (-y)).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ x => by
        change -y + (γ + x) = γ + (-y + x)
        abel
  have e1 := (measurePreserving_add_left μ y).setLIntegral_comp_preimage_emb (measurableEmbedding_addLeft y)
    (fun w => ‖φ w‖ₑ ^ 2) ((fun w => -y + w) ⁻¹' 𝓕)
  have e2 : (fun a => y + a) ⁻¹' ((fun w => -y + w) ⁻¹' 𝓕) = 𝓕 := by
    ext a
    simp
  rw [e2] at e1
  rw [e1, (hN μ _ hμ hs).2.2.1, (hN μ 𝓕 hμ hm.2.1).2.2.1, measure_preimage_add]

theorem cube_dilate_bound_at (hψ : IsStdChar D ψ (-1)) (hc : Chart θ σ) {N : ℕ} (b : Module.Basis (Fin N) ℝ (RW T S))
    {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ φ, IsThetaFunO ψ S T φ → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) φ = φ) → ∀ y : WO S T,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖φ (y + ∑ i, iotaW σ T S (t i • n • b i))‖ ^ 2 ≤ c * (l2O μ 𝓕 φ).toReal ^ 2 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ₀, 𝓕₀, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ι : (Fin N → ℝ) →+ WA T S := (iotaW σ T S).comp b.equivFun.symm.toLinearMap.toAddMonoidHom
  let π : WA T S →+ (Fin N → ℝ) := b.equivFun.toLinearMap.toAddMonoidHom.comp (piW θ T S)
  have hι : Continuous ι := (hc.continuous_iota T S).comp b.equivFunL.symm.continuous
  have hπ : Continuous π := b.equivFunL.continuous.comp (continuous_pi' hc.inf T S)
  have hπι : ∀ t, π (ι t) = t := fun t => by
    show b.equivFun (piW θ T S (iotaW σ T S (b.equivFun.symm t))) = t
    rw [hc.pi_iota, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ w, ι (π w) = iotaW σ T S (piW θ T S w) := fun w => by
    show iotaW σ T S (b.equivFun.symm (b.equivFun (piW θ T S w))) = _
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨c, K₁, hK₁, hreal⟩ := lintegral_real_le (G := WA T S) μ₀ ι π hι hπ hπι hK₀ h0
    (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := lintegral_compact_le (G := WA T S) (ratL T S) μ₀ h𝓕 hK₁
  refine ⟨c * M, fun μ 𝓕 hm n hn φ hφ hl y => ?_⟩
  obtain ⟨e, he, heL⟩ := exists_dilation (S := S) (T := T) hn
  have hsum : ∀ t : Fin N → ℝ, y + ∑ i, iotaW σ T S (t i • n • b i) = y + e (ι t) := fun t => by
    rw [he]
    show _ = y + n • iotaW σ T S (b.equivFun.symm t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, ← map_nsmul, Finset.smul_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm]
  have en : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hmeas : Measurable fun w : WA T S => ‖φ (y + e w)‖ₑ ^ 2 :=
    (hφ.cont.comp (continuous_const.add e.continuous)).measurable.enorm.pow_const 2
  have a1 := hreal _ hmeas fun w hw => by
    have hinf : (w - ι (π w)).map (infPart D) = 0 := by
      have hp : piW θ T S (w - ι (π w)) = 0 := by rw [hιπ, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
      ext i j
      exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
    have := GlobalTheory.HeisOrtho.norm_heisO hψ.1 φ (n • (w - ι (π w))) (y + e (ι (π w)))
    rw [hl _ hw hinf, ← he, add_assoc, ← map_add (f := _), add_sub_cancel] at this
    rw [← en, ← en, this]
  have a2 := hM _ hmeas fun γ hγ w => by
    rw [← en, ← en, map_add (f := _), add_left_comm, theta_norm_periodic hψ hφ _ ((heL γ).2 hγ)]
  have a3 : ∫⁻ w in 𝓕₀, ‖φ (y + e w)‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ :=
    lintegral_comp_aut (G := WA T S) (ratL T S) hK hcov e heL hμ h𝓕 h1 hm.1 hm.2.1 hm.2.2
      (f := fun x => φ (y + x)) (hφ.cont.comp (continuous_const.add continuous_id)) fun γ hγ w => by
        change ‖φ (y + (γ + w))‖ = ‖φ (y + w)‖
        rw [add_left_comm]
        exact theta_norm_periodic hψ hφ γ hγ _
  have a3' := lintegral_translate hψ hφ hm y
  simp only [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + e (ι t))‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    ((hφ.cont.comp (continuous_const.add (e.continuous.comp hι))).norm.pow 2).aestronglyMeasurable]
  simp only [en]
  have he : l2O μ 𝓕 φ ^ 2 = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
    have : BorelSpace (WO S T) := ⟨rfl⟩
    simpa [l2O] using eLpNorm_nnreal_pow_eq_lintegral (μ := μ.restrict 𝓕) (p := 2)
      two_ne_zero hφ.cont.measurable.aestronglyMeasurable
  have a4 := a1.trans (mul_le_mul_right (a2.trans_eq (congrArg _ ((a3.trans a3').trans he.symm))) _)
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    (ENNReal.pow_ne_top (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hm.1 hm.2.1 hφ)))) a4).trans_eq ?_
  simp [mul_assoc]

end GlobalTheory.SupremumSobolevWords

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.Size

end GlobalTheory.SupremumSobolevWords

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolQAndIntegrableIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QuotFundDom

theorem volQ_and_integrable_iff : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (X : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) X ν → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ V ν = (ν X).toReal ∧ ∀ F : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → AEStronglyMeasurable F ν → (Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) F) (GlobalTheory.AutomorphicL2Unitary.autMeasure V ν) ↔ IntegrableOn F X ν) := by
  intro D V ν X hν hX
  refine ⟨?_, fun F hF _ => ?_⟩
  · rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.volQ, Measure.real, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hX]
  · have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) F := hF
    rw [← memLp_one_iff_integrable, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff hX, hL.lift_descend,
      memLp_one_iff_integrable]
    rfl

end GlobalTheory.QuotFundDom
end

