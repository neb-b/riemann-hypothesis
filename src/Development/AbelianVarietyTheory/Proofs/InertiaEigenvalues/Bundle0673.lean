module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0451
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateTwistMultiplicationIntertwines
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExt
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.AdmQuotExt

section Gen
variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (X : Type) [AddCommGroup X] [Module O X]

def redExt (c : O) : ((↥L.T ⊗[O] X) × O) →ₗ[O] ((↥L.T ⊗[O] X) × (O ⧸ Ideal.span {c})) :=
  LinearMap.prodMap LinearMap.id (Ideal.span {c}).mkQ

omit [TopologicalSpace G] in
theorem redExt_surjective (c : O) : Function.Surjective (redExt L X c) := by
  rintro ⟨m, y⟩
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  exact ⟨(m, y), rfl⟩

omit [TopologicalSpace G] in
theorem ker_redExt (lam : O) (a : ℕ) : LinearMap.ker (redExt L X (lam ^ a)) = tableLineDegreeTwo.kerExt L X lam a := by
  rw [redExt, LinearMap.ker_prodMap, LinearMap.ker_id, Submodule.ker_mkQ]
  rfl

theorem redExt_actExt (χ₁ : G →* Oˣ) {c : O} (hc : ∀ x : X, c • x = 0)
    (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ₁ X) ⊤) (g : G) (x : (↥L.T ⊗[O] X) × O) :
    redExt L X c (tableLineDegreeTwo.actExt L X χ₁ z g x) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (redExt L X c x) := by
  obtain ⟨m, y⟩ := x
  have h := Ea_apply (latRep L) χ₁ hc ⟨z, hz⟩ g m y
  change (_, _) = Ea (latRep L) χ₁ hc ⟨z, hz⟩ g (m, Ideal.Quotient.mk _ y)
  rw [h]
  simp only [tableLineDegreeTwo.actExt, smul_smul, mul_comm y]
  rfl

end Gen


set_option maxHeartbeats 2000000 in
theorem admissible_quotientExtension_iff_admissible_ext' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (jT : ZMod S.n → ℤ → ℤ),
    (∀ i a, ((S.D.Ut i).count a : ℤ) = jT i a) →
    ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T.ρ) (X : Type) [AddCommGroup X] [Module S.O X]
      (z : S.G → ↥L.T ⊗[S.O] X) (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤) (a : ℕ)
      (ha : ∀ x : X, S.Γ.lam ^ a • x = 0),
      (tableLineDegreeTwo.AdmQ (P.PD S.K) S.emb S.Γ.lam jT (tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t) (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
                         (tableLineDegreeTwo.kerExt L X S.Γ.lam a) ↔ S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩)) := by
  intro l _ P S jT hj T L X _ _ z hz a ha
  have h := GlobalTheory.FullCharpoly.admissibleQuotient_iff_admissible_module S jT hj _ _ (tableLineDegreeTwo.actExt L X S.Γ.χ₁ z)
    (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) (redExt L X (S.Γ.lam ^ a)) (redExt_surjective L X _)
    (redExt_actExt L X S.Γ.χ₁ ha z hz)
  rw [ker_redExt L X S.Γ.lam a] at h
  exact h

end GlobalTheory.AdmQuotExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ArcTools

theorem arc_tools_from_clauses :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧
      UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧
      UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧
      UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, pE⟩ := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  have hNat : HerrComplexNaturality.HerrNaturality D HW F :=
    HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_part_a_every_record D HW F)
  have sA : UnusedSlot80.SaturationArcLifting D HW F := UnusedSlot80.saturation_general_statement D HW F ⟨p1, p9⟩
  have sE : UnusedSlot80.SaturationEtale D HW F := UnusedSlot80.saturation_unramified_statement D HW F ⟨p1, p9⟩
  have sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F := UnusedSlot80.saturation_pullback_statement D HW F p9
  have pi : UnusedSlot80.GammaPreservesUniformiser D HW F := UnusedSlot80.gamma_uniformizer_divisible_statement D HW F p9
  have kL : UnusedSlot80.KillerAtLevels D HW F := UnusedSlot80.annihilator_levels_unramified_statement D HW F Cm ⟨p4, p9⟩
  have kA : UnusedSlot80.KillerBoundWithConstant D HW F 8 := UnusedSlot80.killer_first_theorem_holds D HW F (le_refl _) ⟨kL, pi⟩
  have kE : UnusedSlot80.KillerAtLevelsSecondForm D HW F := UnusedSlot80.killer_second_theorem_holds D HW F pi
  have f1A : UnusedSlot80.FirstFiltrationArcLifting D HW F := UnusedSlot80.firstFiltrationTheoremCaseA D HW F ⟨p2, p5, p9, a, hNat⟩
  have f1E : UnusedSlot80.FirstFiltrationEtale D HW F := UnusedSlot80.firstFiltrationTheoremEtale D HW F ⟨p2, p5, p9, a, hNat⟩
  have f2A : UnusedSlot80.SecondFiltrationArcLifting D HW F := UnusedSlot80.second_filtration_theorem_arc_lifting D HW F ⟨⟨p7, p9, b⟩, f1A⟩
  have f2E : UnusedSlot80.SecondFiltrationEtale D HW F := UnusedSlot80.cohomology_class_unramified_statement D HW F ⟨⟨p7, p9, b⟩, f1E⟩
  have tE : UnusedSlot80.FiltrationPropertiesEtale D HW F Cm := UnusedSlot80.tools_unramified_statement D HW F Cm ⟨p3, p4, p9⟩
  have bc : UnusedSlot80.H1fBaseChangeFree D := UnusedSlot80.base_change_statement D
  exact ⟨sA, sE, sP, pi, kL, kA, kE, f1A, f1E, f2A, f2E, tE, bc⟩

end GlobalTheory.ArcTools
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverFrameMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (h γ₁ γ₂ : GA D V) (hγ₁ : γ₁ ∈ GQ V) (hγ₂ : γ₂ ∈ GQ V)
    (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin r → D.host.E)) (G₁ G₂ : Matrix (Fin r) (Fin r) D.host.E)
    (hG₁ : G₁ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hG₂ : G₂ = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose)
    (hL₁ : (L₁ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₁ * h) : Set _))
    (hL₂ : (L₂ : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V (γ₂ * h) : Set _)) :
    ∃ γ : GL (Fin r) D.host.E,
      (L₁ : Set (Fin r → D.host.E)) = (γ : Matrix (Fin r) (Fin r) D.host.E).mulVec '' (L₂ : Set _) ∧
      (∀ v w, herm G₁ ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec v) ((γ : Matrix (Fin r) (Fin r) D.host.E).mulVec w) =
        herm G₂ v w) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ x : Matrix (Fin r) (Fin r) ℂ,
          Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₁ * h)) * x =
            (γ : Matrix (Fin r) (Fin r) D.host.E).map τ *
              (Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (γ₂ * h)) * x) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG₁ hG₂
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V _ (mul_mem hγ₁ (inv_mem hγ₂))
  have hprod : γ₁ * γ₂⁻¹ * (γ₂ * h) * 1 = γ₁ * h := by group
  obtain ⟨ht1, -⟩ := GlobalTheory.ShortMoveIso.transport (finHom V) (latGHat V)
    (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) 1 (γ₁ * γ₂⁻¹) (γ₂ * h) 1 rfl
  rw [hprod] at ht1
  have hmem : ∀ (L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V),
      (L : Set (Fin V.rank → D.host.E)) =
        (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast (rfl : V.rank = V.rank).symm) '' (latG V g : Set _) →
      ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g := fun L g hL v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hlat : ∀ v, v ∈ L₂ ↔ δ.1 *ᵥ v ∈ L₁ := fun v => by
    rw [hmem _ _ hL₂, hmem _ _ hL₁, ht1, hδf]
  refine ⟨δ, ?_, fun u v => ?_, fun τ θ hθ x => ?_⟩
  · ext v
    constructor
    · intro hv
      have hri : δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      exact ⟨(δ⁻¹).1 *ᵥ v, (hlat _).2 (by rw [hri]; exact hv), hri⟩
    · rintro ⟨u, hu, rfl⟩
      exact (hlat u).1 hu
  · rw [hG₁, hG₂]
    exact hδu u v
  · have hmul : ∀ a b : GA D V, archM V θ (a * b) = archM V θ a * archM V θ b := by
      intro a b
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have e : γ₁ * h = γ₁ * γ₂⁻¹ * (γ₂ * h) := by group
    rw [hre, hre, e, hmul, hδa _ _ hθ, Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem frames_differ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨-, -, -, -, -, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hf₁⟩ := hd₁ h
  obtain ⟨γ₂, hγ₂, hL₂, -, hf₂⟩ := hd₂ h
  obtain ⟨γ, hl, hi, hf⟩ := move (T.V j σ) hr₁ h γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ _).1 (hW₂ _).1 hL₁ hL₂
  refine ⟨γ, hl, hi, fun τ t₂ t₁ => ?_⟩
  have e₂' := hf₂ ⟨τ, t₂⟩
  have e₁' := hf₁ ⟨τ, t₁⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
  rw [e₁', e₂']
  exact hf τ _ (hth₁ _ ⟨τ, t₁⟩) _

end GlobalTheory.CoverFrameMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoFiniteTrivialRepUnramifiedColumnPlacesA
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ColumnUnramified

theorem blochKatoFinite_trivialRep_unramified_columnPlaces : ∀ (D : D7) (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i), Formalism.MainNotions.EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc := by
  intro D i dc w hw _ C
  rw [GlobalTheory.BridgeInertia.inertEq D i w hw]
  exact GlobalTheory.T.unramified_trivial_local (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i))
    (D.nbr i w hw).Kw C.LL

end GlobalTheory.ColumnUnramified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDim
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.Per.LetterJumps

theorem card_jumps_letter : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (V : Type) [AddCommGroup V] [Module ↥LL.1 V]
      [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
      (ρ : Representation ↥LL.1 ↥(GK K) V) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      IsCrys (P.PD K) ρ →
      (∀ i τ, tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ → ∀ a, multV (P.PD K) ρ τ a = (U i).count a) →
      ∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 V := by
  intro l _ P AI hT H K LL hA V _ _ _ _ _ ρ U hC hU i
  classical
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI := (P.PD K).finK
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  let eK : ↥K.1 ≃ₐ[ℚ_[l]] ↥(K0 K) := IntermediateField.equivOfEq e.symm
  let τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 := ((H.W K 1 LL hA.2.2).emb i).comp eK.toAlgHom
  have hτ : tableLineDegreeTwo.Over (H.W K 1 LL hA.2.2).emb i τ := by
    refine AlgHom.ext fun x => ?_
    show (H.W K 1 LL hA.2.2).emb i (eK (algebraMap ↥(K0 K) ↥K.1 x)) = (H.W K 1 LL hA.2.2).emb i x
    congr 1
  have hc : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 := by
    rw [← Nat.card_congr ((IntermediateField.equivOfEq e).arrowCongr (AlgEquiv.refl : ↥LL.1 ≃ₐ[ℚ_[l]] ↥LL.1)),
      ← Nat.card_congr (Equiv.ofBijective _ (H.W K 1 LL hA.2.2).emb_bij), Nat.card_zmod]
    exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hdim := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l P AI T K LL V ρ).2 hc
    (GlobalTheory.TopSteps.CrysRules.isDR T K LL ρ hC) τ
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ).1
  haveI : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR (P.PD K) ρ) inf_le_left
  obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) ρ τ
  obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) ρ τ
  obtain ⟨b0, hb0⟩ := (U i).toFinset.bddBelow
  obtain ⟨b1, hb1⟩ := (U i).toFinset.bddAbove
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℤ, m ≤ lo ∧ m ≤ b0 ∧ m ≤ hi :=
    ⟨min (min lo b0) hi, by omega, by omega, by omega⟩
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, hi ≤ k ∧ b1 < k := ⟨max hi (b1 + 1), by omega, by omega⟩
  have hmk : m ≤ k := by omega
  have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) ρ τ m k hmk
  rw [hlo m hm1, hhi k hk1, finrank_bot, Nat.cast_zero, sub_zero, hdim] at hsum
  have hsub : (U i).toFinset ⊆ Finset.Ico m k := fun a ha => by
    have h0 := hb0 (Finset.mem_coe.2 ha)
    have h1 := hb1 (Finset.mem_coe.2 ha)
    rw [Finset.mem_Ico]
    omega
  have hcnt : ∑ a ∈ Finset.Ico m k, ((U i).count a : ℤ) = (Multiset.card (U i) : ℤ) := by
    rw [← Multiset.toFinset_sum_count_eq, Nat.cast_sum]
    exact (Finset.sum_subset hsub fun a _ ha => by
      rw [Multiset.mem_toFinset] at ha
      rw [Multiset.count_eq_zero.2 ha, Nat.cast_zero]).symm
  have := (Finset.sum_congr rfl fun a _ => hU i τ hτ a).symm.trans hsum
  rw [hcnt] at this
  exact_mod_cast this

end GlobalTheory.Per.LetterJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.SuppLaw

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpZero (σ : Weil h) : (WD.lpZero (h := h)).charPol σ = 1 := by
  rw [WD.lpZero, WD.charPol_mk]
  exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic _)
    (by rw [LinearMap.charpoly_natDegree]; simp)

theorem charPol_sumList (l : List (WD h)) (σ : Weil h) :
    (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod := by
  induction l with
  | nil => simp [sumList, charPol_lpZero]
  | cons b l ih =>
    have : sumList (b :: l) = WD.lpSum b (sumList l) := rfl
    rw [this, WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]

theorem nu_eq {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) : rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

theorem charPol_seg {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}
    (H : LawsLit a ha e rc) (Δ : Segment (w.adicCompletion E)) (σ : Weil h) :
    (((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)).charPol σ
      = (Δ.ms.map fun y => (rc y).charPol σ).prod := by
  rw [(GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h (rc Δ.first)).2 Δ.len σ, Segment.ms, Multiset.map_map]
  have h1 : ∀ j : Fin Δ.len, (rc (Δ.term j)).charPol σ = ((rc Δ.first).lpTw ((j : ℕ) : ℝ)).charPol σ := by
    intro j
    rw [Segment.term, show (((j : ℕ) : ℂ)) = ((((j : ℕ) : ℝ)) : ℂ) by push_cast; rfl, nu_eq H]
  change _ = ∏ j : Fin Δ.len, (fun y => (rc y).charPol σ) (Δ.term j)
  simp only [h1]
  rw [Fin.prod_univ_eq_prod_range (fun j => ((rc Δ.first).lpTw (j : ℝ)).charPol σ) Δ.len]
  rfl

end GlobalTheory.LocLanglands.SuppLaw

namespace GlobalTheory.LocLanglands

theorem charPol_eq_prod_support : LanglandsExhaustionGL → ZelevinskyPolynomialRing → GeometricLemma →
    BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ)
    (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ)
    (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (x : IrrGL (k := w.adicCompletion E)) s,
    HasSupport x.rep s → ∀ σ, (rc x).charPol σ = (s.map fun y => (rc y).charPol σ).prod := by
  intro hEx hZ hG hBZ E Ω _ _ _ _ _ A w h a ha e rc H x s hs σ
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := hEx (w.adicCompletion E) x
  have h1 := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZ _ 𝔪 x hm
  obtain rfl : s = msupp 𝔪 := GlobalTheory.T.supercuspidalSupport_unique_GL hG hBZ hZ _ x s _ hs h1
  rw [H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, SuppLaw.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => SuppLaw.charPol_seg H Δ σ)

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosingAtRecord
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.Closing

theorem closing_at_record : ∀ D : D7, DualJumpL D.loc ∧ PotDRL D.loc ∧ PcrisTensorL D.loc ∧
    PairedCharacterCondition.tieBr (D := D) ∧ InertEq D := by
  intro D
  have hT : ∀ (l : ℕ) [Fact (Nat.Prime l)], Nonempty (LocTied l (D.loc l) (D.locA l)) :=
    fun l _ => ⟨D.locT l⟩
  refine ⟨GlobalTheory.DualJump.dualJumpL D.loc D.locA hT, GlobalTheory.Pass.potDRL_of_tied D.loc D.locA hT,
    GlobalTheory.PcrisTwist.pcrisTensorL_of_tied D.loc D.locA hT, ?_, GlobalTheory.BridgeInertia.inertEq D⟩
  intro i w hw
  exact GlobalTheory.bridge_degW D.nbr i w hw

end GlobalTheory.Closing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleClassAdmissible
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem GlobalTheory.admissible_eventually_iff_mem_cls : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] (W : Representation S.O S.G M) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X],
    (∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0) →
    (∀ (a : ℕ) (ha : ∀ x : X, S.Γ.lam ^ a • x = 0), 1 ≤ a →
      S.cls W X = admAt (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut W X a ha) →
    ∀ z : ↥(Z1 (twCoef W S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea W S.Γ.χ₁ ha z)) ↔
        Submodule.Quotient.mk z ∈ S.cls W X) := by
  intro l _ P S M _ _ W X _ _ _ hX hlev z
  constructor
  · rintro ⟨a₀, h⟩
    obtain ⟨a₁, h1⟩ := hX
    have hle1 : a₁ ≤ max a₀ (max a₁ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : ∀ x : X, S.Γ.lam ^ (max a₀ (max a₁ 1)) • x = 0 := by
      intro x
      rw [← Nat.sub_add_cancel hle1, pow_add, mul_smul, h1, smul_zero]
    have hA := h (max a₀ (max a₁ 1)) (le_max_left _ _) ha
    have hone : 1 ≤ max a₀ (max a₁ 1) := le_trans (le_max_right _ _) (le_max_right _ _)
    rw [hlev _ ha hone]
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mpr hA
  · intro h
    refine ⟨1, fun a ha1 ha => ?_⟩
    rw [hlev a ha ha1] at h
    exact (mk_mem_admissibleAt_iff_cocycle ha z).mp h
end

