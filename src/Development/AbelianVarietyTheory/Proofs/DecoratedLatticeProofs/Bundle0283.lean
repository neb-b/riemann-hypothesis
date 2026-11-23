module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0051
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallPrincipalCongruenceLiftVector
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.SmallEx

theorem exists_isVacO {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := Formalism.IndefR.Datum.measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := _root_.GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩

theorem exists_small_stepVec : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sA : RealMat A) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → A.rank ≤ H.rank → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∃ (βH : GL (Fin H.rank) (Formalism.IndefR.Lev.EAf D)) (f₀ f : WO A H → ℂ), Formalism.L2.DIV.IsFrame βH (frameLat H) ∧ IsStepVecOf ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z) (fun _ => 1) ∅ (fun _ => 1) f₀ f := by
  classical
  intro D ψ θ A H χA om sA sH hθ _ hW hA hH _ β Z hP
  have dA := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat A
  have dH := GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat H
  have hspan : Submodule.span D.host.E (frameLat H : Set (Fin H.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (H.L0 : Set H.V) = ⊤ := by
      let W := Submodule.span D.host.E (H.L0 : Set H.V)
      change W = ⊤
      by_contra h
      let e : H.V ≃ₗ⋆[D.host.E] H.V :=
        (H.frame.equivFun.trans (starLinearEquiv D.host.E)).trans H.frame.equivFun.symm
      let g : H.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (H.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E H.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ H.L0 := by
        rw [← H.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : H.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : H.hT y (e x) = 0 := by
          rw [(H.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] H.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict H.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) H.L0 := Module.Finite.iff_fg.mpr H.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat H : Set (Fin H.rank → D.host.E)) =
        H.frame.equivFun.toLinearMap '' (H.L0 : Set H.V) :=
      (H.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨βH, hβH⟩ := GlobalTheory.AdelicFrame.exists_isFrame (F := D.host.F) (frameLat H) dH.1.fg hspan
  obtain ⟨f₀, hf₀⟩ := exists_isVacO ψ θ hW.std hθ A H sA sH hA hH _ _ dA dH
  have hsp : ∃ e : AE D, IsIdemSum e ((prinDat A Z).Pg ∪ ∅) := by
    obtain ⟨e, he⟩ := hP.idem
    exact ⟨e, by rw [Finset.union_empty]; exact he⟩
  obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.stepVecExists D ψ θ A H sA sH (frameLat A) (frameLat H) β βH (prinDat A Z)
    (fun _ => 1) ∅ (fun _ => 1) dA dH hP.frame hβH (Finset.disjoint_empty_right _) hsp f₀ hf₀
  exact ⟨βH, f₀, f, hβH, hf⟩

end GlobalTheory.Core.Rk.SmallEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldIntegralBesselQuotientSupportedFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem fold_quot : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B 𝓢 h𝓢 Fs hFs
  obtain ⟨c₁, hc₁, hL1⟩ := _root_.GlobalTheory.Core.Mi.Disint.disint D X h u ψ A B
  obtain ⟨β, hβm, hβ1, hβF⟩ := _root_.GlobalTheory.Core.Mi.Fold.exists_cutoff_srat D X u Fs hFs
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK0 : X.B.μf X.K2 ≠ 0 := hK.2.2.1.ne'
  have hKT : X.B.μf X.K2 ≠ ⊤ := hK.2.2.2.ne
  refine ⟨c₁ * (X.B.μf X.K2).toReal, mul_pos hc₁ (ENNReal.toReal_pos hK0 hKT), ?_⟩
  intro F hFm hFl hFr hFsupp
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (_root_.GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  haveI : SigmaFinite B.lev.μR := inferInstance
  have hK2m : MeasurableSet X.K2 := (Formalism.L2.SG.Pf.DstarIdxPf.isOpen_levelSubgroup' X).measurableSet
  have hι : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
    (iotaX X h).continuous.comp continuous_subtype_val

  have key : ∀ y : X.B.I.Ginf,
      ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) * F (iotaX X h s.1 * (y, X.xu u) * (1, k))
          ∂X.B.μf ∂B.lev.μR =
        X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR := by
    intro y
    set g : X.B.I.GA := (y, X.xu u) with hg
    have e1 : ∀ s : besGrp B.d B.o,
        ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g * (1, k)) ∂X.B.μf =
          ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂X.B.μf := by
      intro s
      refine setLIntegral_congr_fun hK2m (fun k hk => ?_)
      rw [hFr k hk]
    simp_rw [e1]
    have hmeas : Measurable (Function.uncurry fun (s : besGrp B.d B.o) (k : X.B.I.Gf) =>
        β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g)) := by
      have c1 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g * (1, p.2)) :=
        ((hι.comp continuous_fst).mul continuous_const).mul (continuous_const.prodMk continuous_snd)
      have c2 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g) :=
        (hι.comp continuous_fst).mul continuous_const
      exact (hβm.comp c1.measurable).mul (hFm.comp c2.measurable)
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have e2 : ∀ k ∈ X.K2, ∫⁻ s, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂B.lev.μR =
        ∫⁻ s in 𝓢, F (iotaX X h s.1 * g) ∂B.lev.μR := by
      intro k hk
      have hf : Measurable (fun x : X.B.I.GA => β (x * g * (1, k)) * F (x * g)) :=
        (hβm.comp ((continuous_id.mul continuous_const).mul continuous_const).measurable).mul
          (hFm.comp (continuous_id.mul continuous_const).measurable)
      rw [_root_.GlobalTheory.Core.Mi.Unfold.lintegral_unfold D X h u ψ A B 𝓢 h𝓢 _ hf]
      refine lintegral_congr fun s => ?_
      have e3 : ∀ σ : Srat X u, β ((σ : X.B.I.GA) * iotaX X h s.1 * g * (1, k)) * F ((σ : X.B.I.GA) * iotaX X h s.1 * g) =
          β ((σ : X.B.I.GA) * (iotaX X h s.1 * g * (1, k))) * F (iotaX X h s.1 * g) := by
        intro σ
        rw [mul_assoc (σ : X.B.I.GA) (iotaX X h s.1) g, hFl _ σ.2, mul_assoc (σ : X.B.I.GA) (iotaX X h s.1 * g)]
      simp only [e3]
      rw [ENNReal.tsum_mul_right, hβ1, one_mul]
    rw [setLIntegral_congr_fun hK2m (fun k hk => e2 k hk), setLIntegral_const, mul_comm]
  calc ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := hβF F hFm hFl
    _ = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) *
          F (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
        refine hL1 (fun x => β x * F x) (hβm.mul hFm) (fun x hx => hFsupp x ?_)
        intro h0; exact hx (by rw [h0, mul_zero])
    _ = ENNReal.ofReal c₁ * ∫⁻ y, X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
        congr 1; exact lintegral_congr key
    _ = _ := by
        rw [lintegral_const_mul' _ _ hKT, ← mul_assoc, ENNReal.ofReal_mul hc₁.le, ENNReal.ofReal_toReal hKT]

end GlobalTheory.Core.Mi.Fold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplit
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem hsNormSq_add_le_three_halves {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsNormSq (A + B) ≤ 3 / 2 * hsNormSq A + 3 * hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (A (stdOrthonormalBasis ℂ Wq i)) (B (stdOrthonormalBasis ℂ Wq i))
  have h0 := norm_nonneg (A (stdOrthonormalBasis ℂ Wq i) + B (stdOrthonormalBasis ℂ Wq i))
  rw [ContinuousLinearMap.add_apply]
  nlinarith [sq_nonneg (‖A (stdOrthonormalBasis ℂ Wq i)‖ - 2 * ‖B (stdOrthonormalBasis ℂ Wq i)‖)]

theorem hsDev_le_split_three_halves : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤
    3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  intro D u
  have e : Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + AdmissibleBoundsFromSource.Kpp D u u := by abel
  unfold GlobalTheory.Core.Rk.hsDev
  rw [e]
  exact hsNormSq_add_le_three_halves _ _

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.FinComb

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isFinComb_zero : IsFinComb ψ S T f₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩

theorem isFinComb_add {f g : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) (hg : IsFinComb ψ S T f₀ g) :
    IsFinComb ψ S T f₀ (f + g) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  obtain ⟨m, c', x', hx', rfl⟩ := hg
  refine ⟨n + m, Fin.append c c', Fin.append x x', fun k => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hx i
    · rw [Fin.append_right]; exact hx' i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem isFinComb_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsFinComb ψ S T f₀ f) : IsFinComb ψ S T f₀ (a • f) := by
  obtain ⟨n, c, x, hx, rfl⟩ := hf
  exact ⟨n, fun k => a * c k, x, hx, by rw [Finset.smul_sum]; simp only [smul_smul]⟩

theorem isFinComb_single (a : ℂ) (x : WO S T) (hx : x.map (infPart D) = 0) :
    IsFinComb ψ S T f₀ (a • heisO ψ S T x f₀) :=
  ⟨1, fun _ => a, fun _ => x, fun _ => hx, by simp⟩

end GlobalTheory.AdForm.FinComb

namespace GlobalTheory.AdForm

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.AdForm.FinComb

theorem isFinComb_of_isThetaAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (e : AE D) (f₀ Φ f : WO S T → ℂ),
    IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → e * e = e → infPart D e = 0 →
    IsSBHalf e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ →
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f →
    IsFinComb ψ S T f₀ f := by
  intro D ψ S T ΛS ΛT e f₀ Φ f hψ hS hT he hinf hΦ hθ
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  rw [hall Tm hTm]
  clear hall
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ latO S T ΛS ΛT fun _ => True,
      a • u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have hLL' : ∀ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e,
      ∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T u y) = 1 := fun u hu y hy =>
    (hdual u (infPart_of_half hinf ((isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hX : ∀ x ∈ half S T e, (∀ y ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) →
      x ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e := fun x hx h => by
    refine ⟨(hdual x (infPart_of_half hinf ((isHalf_iff S T).2 hx))).2 fun u hu => ?_, hx⟩
    have := h _ (hsm _ he' u hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this
  have hfin' : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, ∃ r ∈ R,
        ∃ u ∈ (latO S T ΛS ΛT fun _ => True) ⊓ half S T e, t = r + k • u := fun k hk => by
    obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e he u hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  have hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ (latO S T ΛS ΛT fun _ => True) := fun y hy =>
    exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy))
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : Φ ∈ waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T e) (half S T (cA D e))
      ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T e) (half_div S T _) tf hfin' Φ
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩
  clear hΦ
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    have s0 := GlobalTheory.isSBHalf_halfInd e (latO S T ΛS ΛT fun _ => True)
    have s1 : IsSBHalf e (latO S T ΛS ΛT fun _ => True)
        fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd e (latO S T ΛS ΛT fun _ => True) (t + (k * k') • u) =
            halfInd e (latO S T ΛS ΛT fun _ => True) t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) ((latO S T ΛS ΛT fun _ => True) ⊓ half S T e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd e (latO S T ΛS ΛT fun _ => True) t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := hTm.vac
    rw [one_smul] at v1
    rw [e1, hTm.trans _ s1 x ((isHalf_iff S T).2 hx), hTm.modul _ s0 y ((isHalf_iff S T).2 hy), v1]
    have hxy := heisL_heisL S T ψ x y f₀
    change heisO ψ S T x (heisO ψ S T y f₀) = ψ (symplOH S T x y) • heisO ψ S T (x + y) f₀ at hxy
    rw [hxy]
    refine isFinComb_single _ _ ?_
    have h1 := infPart_of_half hinf ((isHalf_iff S T).2 hx)
    have h2 := infPart_of_half (infPart_cA hinf) ((isHalf_iff S T).2 hy)
    ext i j
    have a1 := congrFun (congrFun h1 i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [RingHom.map_add (f := _), a1, a2, add_zero]
  | zero => rw [LinearMap.map_zero]; exact isFinComb_zero
  | add g g' _ _ hg hg' => rw [LinearMap.map_add (f := _)]; exact isFinComb_add hg hg'
  | smul c g _ hg => rw [LinearMap.map_smul]; exact isFinComb_smul c hg

end GlobalTheory.AdForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MiStar2OfAnchored
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

namespace GlobalTheory.MiTop

theorem miStar2_of_anchored : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) (c : (fc X.zs).Dc.Mem → Bs.Tup → ℂ), OpsUnit X V U → Anchored X eV sEE V U c → UnitAt X c → X.MIstar2 eV sEE := by
  intro K _ _ _ Bs A X fc eV sEE V U c hOp hAn hUn
  choose p b hp hb hid using hAn
  refine ⟨⟨V, fun u => p u / (b u * c u Bs.μ0), U, fun u t => c u t / c u Bs.μ0⟩, ?_, ?_, ?_⟩
  · refine ⟨hOp.1, hOp.2, ⟨fun u t => div_ne_zero (hUn.1 u t) (hUn.1 u Bs.μ0), fun u w k hk => hUn.2 u w k hk⟩,
      fun u => div_self (hUn.1 u Bs.μ0)⟩
  · intro u t φ F
    have h := hid u t φ F
    have hc := hUn.1 u Bs.μ0
    have hbu := hb u
    dsimp only
    field_simp
    linear_combination h
  · intro u
    exact div_ne_zero (hp u) (mul_ne_zero (hb u) (hUn.1 u Bs.μ0))

end GlobalTheory.MiTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem concK_of_finX : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  intro hWu D large₂ C' Cl Cg cb Cu cT CT S hC' hCl hFX hL hTF hH
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties S.X
  exact ⟨Formalism.L2.SG.ThmSOwn.concKOf S ⟨hFX, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D S.X S.Y u hK,
    (hWu D hG S.X).1, (hWu D hG S.X).2, hL, hTF⟩⟩

end GlobalTheory.Core.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_annihilator_openSubgroup_finPart_compact : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (AE D), IsOpen (U : Set (AE D)) → ∃ K : Set (AE D), IsCompact K ∧ ∀ x : AE D, (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) → ∃ k ∈ K, finPart D (x - k) = 0 := by
  first | exact @GlobalTheory.CondBound.annihilator_finPart_compact | exact GlobalTheory.CondBound.annihilator_finPart_compact | (intros; apply GlobalTheory.CondBound.annihilator_finPart_compact <;> assumption)
end

