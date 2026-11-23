module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import GroundTheory.GlobalFields.Adele.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0459
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleFiniteFactorArchimedeanSchwartz
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchUniq

variable {F : Type} [Field F] [NumberField F]

def intFinInd (F : Type) [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  Set.indicator (Set.pi Set.univ fun _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) 1

theorem intFinInd_mem_SB (κ : Type) [Fintype κ] : intFinInd F κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set C := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  have hoI : IsOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles
  have hcI := GroundTheory.Global.isCompact_integralFiniteAdeles F
  have ho : IsOpen C := isOpen_set_pi Set.finite_univ fun _ _ => hoI
  have hc : IsClosed C :=
    isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen
      (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hoI
  have hk : IsCompact C := isCompact_univ_pi fun _ => hcI
  refine ⟨?_, HasCompactSupport.intro' hk hc fun y hy => Set.indicator_of_notMem hy _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ C
  · filter_upwards [ho.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
    simp only [intFinInd]
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem snd_eq_zero_of_at {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 := congrArg Prod.snd h
  change (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 at h2
  rwa [one_mul] at h2

theorem exists_admissible_finite_factor : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ,
    (∀ f : SInf F κ, Rest (evI F) (⇑f) r₀) ∧
    ∀ f₁ f₂ : SInf F κ, tens (evI F) (⇑f₁) r₀ = tens (evI F) (⇑f₂) r₀ → f₁ = f₂ := by
  intro F _ _ κ _
  refine ⟨fun x => intFinInd F κ (fun i => (x i).2), fun f => ⟨fun x z hz => ?_, ?_⟩, fun f₁ f₂ h => ?_⟩
  · have : (fun i => (x + z) i |>.2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intFinInd F κ, intFinInd_mem_SB κ, rfl⟩
  · ext y
    have h1 := congrFun h (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)), 0))
    have hy : (fun i => evI F (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0) : AF F)) = y := by
      funext i
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
    have h0 : intFinInd F κ (fun _ => 0) = 1 := by
      simp only [intFinInd]
      rw [Set.indicator_of_mem (show (fun _ => (0 : FiniteAdeleRing (𝓞 F) F)) ∈ Set.pi Set.univ
        fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun _ _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem)]
      rfl
    simp only [tens, hy, h0, mul_one] at h1
    exact h1

end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdmissibleUnipotentSplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_unipotent_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | exact GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt | (intros; apply GlobalTheory.SplitChoose.exists_admissible_unipotent_splitPlace_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaHeisCLM

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

theorem exists_schr_pureA_eq {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g' ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F (T f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  let h : AdeleRing (𝓞 F) F := ⅟(2 : AdeleRing (𝓞 F) F) * (w.1 ⬝ᵥ w.2)
  let c : κ → mixedEmbedding.mixedSpace F := fun i => q (w.2 i)
  let t : κ → mixedEmbedding.mixedSpace F := fun i => q (w.1 i)
  let k : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (q h)
  let d : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.2 i)
  let s : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (w.1 i)
  refine ⟨(SchwartzMap.smulLeftCLM ℂ (fun y => eChar ((-trL c) y + -k))).comp (SchwartzMap.compSubConstCLM ℂ (-t)),
    finS ψ g d s (p2 h), finS_mem ψ hψ.1 hg d s (p2 h), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h1 : (fun i => q ((x + w.1) i)) = y + t := funext fun i => map_add q (x i) (w.1 i)
  have h2 : (fun i => p2 ((x + w.1) i)) = z + s := funext fun i => map_add p2 (x i) (w.1 i)
  have h3 : ψ (x ⬝ᵥ w.2 + h) = eChar ((-trL c) y + -k) * finChar ψ (z ⬝ᵥ d + p2 h) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.HeisSchA.mk (p1 (x ⬝ᵥ w.2 + h)) 0) = y ⬝ᵥ c + q h := by
        change q (x ⬝ᵥ w.2 + h) = _
        rw [map_add (f := _), RingHom.map_dotProduct]
        rfl
      rw [e1, map_add (f := _), eChar_apply, ContinuousLinearMap.neg_apply, trL_apply]
      congr 1
      push_cast
      ring
    · rw [map_add (f := _), RingHom.map_dotProduct]
      rfl
  change ψ (x ⬝ᵥ w.2 + h) * (f (fun i => q ((x + w.1) i)) * g (fun i => p2 ((x + w.1) i))) =
    archS f c t k y * (finChar ψ (z ⬝ᵥ d + p2 h) * g (z + s))
  rw [h1, h2, h3, archS_apply]
  ring

theorem exists_clm_thetaSum_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g) = L f := by
  obtain ⟨l, hl, hl'⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F κ
  obtain ⟨L, hL⟩ := hl g hg
  exact ⟨L, fun f => (hl' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hL f)⟩

theorem exists_clm_thetaSum_rho_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ (u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ Λ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f,
      GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = Λ f := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ hG u φ hSB hvac
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hG.std).mono fun v h => h.1.trans h.2
  have hg : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F =>
      ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈ GlobalTheory.WeilM.SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  obtain ⟨T, g', hg', hT⟩ := exists_schr_pureA_eq ψ hψ (M.co.e u) hg
  obtain ⟨L, hL⟩ := exists_clm_thetaSum_pureA hg'
  refine ⟨L.comp T, fun f => ?_⟩
  rw [ContinuousLinearMap.comp_apply, ← hL, ← hT]
  rfl

end GlobalTheory.ThetaHeisCLM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRepRightTranslationMaxCompactStaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_rightTranslation_maxCompactStable : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  first | exact @GlobalTheory.KTypeRep.exists_contRep_types | exact GlobalTheory.KTypeRep.exists_contRep_types | (intros; apply GlobalTheory.KTypeRep.exists_contRep_types <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGridCosetDataEqWeilCosetVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isThetaAt_unique {D : D7} {m n : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {c : ℂ}
    {f₀ Φ f f' : Mx D m n → ℂ} (h : IsThetaAt ψ B hs e Λ c f₀ Φ f) (h' : IsThetaAt ψ B hs e Λ c f₀ Φ f') : f = f' := by
  obtain ⟨⟨T, hT⟩, h1⟩ := h
  exact (h1 T hT).trans (h'.2 T hT).symm

theorem exists_cosetVec_of_match {D : D7} {S T : Grid.Node D} {V₁ V₂ : HSp D}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin V₁.rank → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin V₂.rank → D.host.E)}
    {I I' : Ideal (𝓞 D.host.E)} {e : AE D} {ψ ψ' : AddChar (AF D.host.F) ℂ}
    (hS : S.V = V₁) (hT : T.V = V₂) (hΛ₁ : HEq S.Λ Λ₁) (hΛ₂ : HEq T.Λ Λ₂) (hI : I = I') (hψ : ψ = ψ')
    (vac : WO (negSp V₁) V₂ → ℂ) (cv : Cos Λ₁ Λ₂ I' → WO (negSp V₁) V₂ → ℂ)
    (hcv : ∀ κ : Cos Λ₁ Λ₂ I', IsThetaAt ψ (symplO (negSp V₁) V₂) (heisO ψ (negSp V₁) V₂) e
      (latO (negSp V₁) V₂ (Λ₁ : Set _) (Λ₂ : Set _) fun _ => True) 1 vac (cosInd e κ) (cv κ))
    (hA : ∀ c : Grid.Coset S T I, ∃ κ : Cos S.Λ T.Λ I, Grid.cosetInd S T e I c = cosInd e κ)
    (hB : ∀ κ : Cos S.Λ T.Λ I, ∃ c : Grid.Coset S T I, Grid.cosetInd S T e I c = cosInd e κ)
    (f : WO S.V T.V → ℂ) (hf : HEq f vac) :
    ∃ v : Grid.Coset S T I → (WO S.V T.V → ℂ), (∀ c, Grid.IsCosetVec ψ' true S T e I c f (v c)) ∧
      (∀ c, ∃ κ, HEq (v c) (cv κ)) ∧ ∀ κ, ∃ c, HEq (v c) (cv κ) := by
  subst hS hT hI hψ
  obtain rfl := eq_of_heq hΛ₁
  obtain rfl := eq_of_heq hΛ₂
  obtain rfl := eq_of_heq hf
  choose κ hκ using hA
  refine ⟨fun c => cv (κ c), fun c => ?_, fun c => ⟨κ c, HEq.rfl⟩, fun κ' => ?_⟩
  · show IsThetaAt ψ _ _ e _ 1 f (Grid.cosetInd S T e I c) (cv (κ c))
    rw [hκ c]
    exact hcv (κ c)
  · obtain ⟨c, hc⟩ := hB κ'
    refine ⟨c, heq_of_eq ?_⟩
    have h1 := hcv (κ c)
    have h2 := hcv κ'
    rw [← hκ c, hc] at h1
    exact isThetaAt_unique h1 h2

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

theorem isFrame_col {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}
    (hR : GlobalTheory.Hk3.Core R F) {G : GlobalTheory.Grid.GridPre R} (hsp : G.IsSpaces) {i : ℕ} (hi : i ≤ D.R.m) :
    Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
  cases i with
  | zero =>
    obtain ⟨c, hc⟩ := hR.lev.βY 0 (by have := D.R.two_le_m; omega)
    exact hc.1
  | succ k =>
    obtain ⟨c, hc⟩ := (hsp.vert k 0 hi (Nat.zero_le _)).frame
    exact hc.1

theorem exists_cosData_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i, i < D.R.m → ∀ f : WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ, HEq f (W.vac i) → ∃ v : G.toGridSp.Cos R i → (WO (G.V (i + 1) 0).V (G.V i 0).V → ℂ), (∀ c, GlobalTheory.Grid.IsCosetVec R.ψ true (G.V (i + 1) 0) (G.V i 0) G.idem (G.lvl R) c f (v c)) ∧ (∀ c, ∃ κ, HEq (v c) (W.cosVec i κ)) ∧ ∀ κ, ∃ c, HEq (v c) (W.cosVec i κ) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hDC hHC hH F hR hsc G' W hW G hsp hch hag hcos i hi f hf
  have hA := _root_.GlobalTheory.CosetIndCompare.coset_eq_cos (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  have hB := _root_.GlobalTheory.CosToCoset.cosInd_eq_cosetInd (G.V (i + 1) 0) (G.V i 0) G.idem (G.toPlaceDat.W R.Pg) G.toPlaceDat.depth
    (isFrame_col hR hsp (by omega)) (isFrame_col hR hsp hi.le) hch.places.idem
  exact exists_cosetVec_of_match (I := G.lvl R) (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).sp
    (hag.vert i 0 hi.le (Nat.zero_le _)).sp (hag.vert (i + 1) 0 (by omega) (Nat.zero_le _)).lat
    (hag.vert i 0 hi.le (Nat.zero_le _)).lat hag.lvl hW.ψ (W.vac i) (W.cosVec i) (hcos i hi) hA hB f hf

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivArch

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_heisD {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f
      (heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  intro r hr x
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add (f := _),
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, GlobalTheory.HeisDeriv.evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV (F := F) y) := by
  intro a ha
  funext i
  refine Prod.ext ?_ ?_
  · have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
    show a.1 * ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = 0
    rw [h1, zero_mul]
  · show a.2 * 0 = 0
    exact mul_zero _

end GlobalTheory.HeisDerivArch


open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch in
theorem GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ ∀ f g : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) ⇑f ⇑g → ∀ y, g y =
        fderiv ℝ (⇑f) y v.1 - 2 * Real.pi * Complex.I * (trP F (Fin n × Fin d) y v.2 : ℂ) * f y := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ v
  set u := M.co.e.symm (liftV v.1, liftV v.2) with hu
  have heu : M.co.e u = (liftV v.1, liftV v.2) := by rw [hu, LinearEquiv.apply_symm_apply]
  refine ⟨u, ?_, ?_⟩
  · intro a ha
    have e1 : a • u = M.co.e.symm (a • (liftV v.1, liftV v.2)) := by rw [hu, map_smul]
    rw [e1, Prod.smul_mk, at_liftV v.1 a ha, at_liftV v.2 a ha, Prod.mk_zero_zero, map_zero]
  · intro f g hg y
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
    have hr := hR f
    set x : Fin n × Fin d → AF F := liftV y with hx
    have hd1 := hg R hr x
    have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
    have huniq := hd1.unique hd2
    have hRx : R x = R 0 := by
      have := hr.1 0 x (at_liftV y)
      rwa [zero_add] at this
    have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
    simp only [tens, hlx, hRx] at huniq
    have huniq' := mul_right_cancel₀ hR0 huniq
    rw [huniq', heisD_apply, mult_apply, heu]
    have hv1 : (fun i => evI F ((liftV (F := F) v.1) i)) = v.1 := Coord.loc_lift v.1
    simp only [hv1, trForm_apply]
    have hv2 : ∀ i, evI F ((liftV (F := F) v.2) i) = v.2 i := fun i => congrFun (Coord.loc_lift v.2) i
    simp only [hv2, trP]
    ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_split_stabilizer_decomposition : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  first | exact @GlobalTheory.RatSplitLat.exists_rat_split_lat | exact GlobalTheory.RatSplitLat.exists_rat_split_lat | (intros; apply GlobalTheory.RatSplitLat.exists_rat_split_lat <;> assumption)
end

