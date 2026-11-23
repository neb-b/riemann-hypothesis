module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.IUnfold
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
section
open Formalism.BasicNotions

namespace GlobalTheory.TwArch

theorem archOnRecord_closed : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D :=
  fun hDS hHC D => GlobalTheory.ArchRec.archOnRecord hDS hHC D

end GlobalTheory.TwArch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseTermNormCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf


set_option maxHeartbeats 1000000 in
theorem base_term_norm_coords : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ (𝓐 : Set (flagN d)) (𝓑 : Set (GA D W)), (∀ f : GA D V → ENNReal, Measurable f → (∀ c, ∀ n ∈ flagN d, f (d.nC c * n) = f n) → ∫⁻ n in 𝓐, f n.1 ∂vN.ν = ∫⁻ u, ∫⁻ b in vb.𝓕, f (d.nB b * d.levi u.1) ∂vb.μ ∂vU.ν) → ∀ g : GA D V, ∫⁻ h in 𝓑, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν ∂vW.μ = ∫⁻ p in 𝓐 ×ˢ 𝓑, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ ∂(vN.ν.prod vW.μ) := by
  intro D ψ V V₀ W ρ d χV χW om om' hω hω' vS vN vb vU vW x₀ G Φ hG hΦ 𝓐 𝓑 hlay g
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (GlobalTheory.MixPer.isIsoSub_e d)
  obtain ⟨hN1, hN2, hN3⟩ := vN.unit
  haveI := vW.haar
  haveI : SFinite vN.ν := inferInstance
  haveI : SFinite vW.μ := inferInstance
  have hTL := _root_.GlobalTheory.Unf.TermLaw.term_laws D ψ V V₀ W ρ d χV χW om om' hω hω' vS
  have hsplit : ∀ (n : GA D V) (h : GA D W), om (n * g, h) Φ = om (n, 1) (om (g, h) Φ) := by
    intro n h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hψn : ∀ x, ‖ψ x‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hω.std.1.2.1 x, ENNReal.ofReal_one]
  have hFm : Measurable (fun p : flagN d × GA D W =>
      ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) x₀‖ₑ) := by
    refine Continuous.measurable ?_
    refine ((hG.2.1.comp continuous_snd).mul ?_).enorm
    exact ((hTL Φ hΦ).2.2.2.1 x₀).comp
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
  have hfib : ∀ h : GA D W, ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
      ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν =
      ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
    intro h
    have hΨ : IsThetaFunO ψ V W (om (g, h) Φ) := hω.om_pres (g, h) Φ hΦ
    have hfm : Measurable (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) :=
      (((hTL _ hΨ).2.2.2.1 x₀).comp (continuous_id.prodMk continuous_const)).enorm.measurable
    have hinv : ∀ c, ∀ n ∈ flagN d,
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) (d.nC c * n) =
        (fun m : GA D V => ‖term ψ d W vS (om (m, 1) (om (g, h) Φ)) x₀‖ₑ) n := by
      intro c n hn
      have hΨ' := hω.om_pres (n, 1) _ hΨ
      have t1 := (hTL _ hΨ').1 x₀ 0 1 c
      rw [d.nB_zero, OneMemClass.coe_one, map_one, mul_one, mul_one, ← Module.End.mul_apply, ← map_mul,
        Prod.mk_mul_mk, one_mul] at t1
      show ‖term ψ d W vS (om (d.nC c * n, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖term ψ d W vS (om (n, 1) (om (g, h) Φ)) x₀‖ₑ
      rw [t1, enorm_mul, hψn, one_mul]
      simp [term]
    have hval : ∀ (u : UX D ρ) (b : Mx D ρ V₀.rank),
        ‖term ψ d W vS (om (d.nB b * d.levi u.1, 1) (om (g, h) Φ)) x₀‖ₑ =
        ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ := by
      intro u b
      have t1 := (hTL _ hΨ).1 x₀ b u 0
      rw [d.nC_zero, one_mul] at t1
      rw [t1, enorm_mul, hψn, one_mul]
      rfl
    have hl := hlay _ hfm hinv
    calc ‖G h‖ₑ * ∫⁻ u, ∫⁻ b in vb.𝓕,
          ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) (rat x₀ ⬝ u.1.1) (rat x₀ ⬝ b)‖ₑ ∂vb.μ ∂vU.ν
        = ‖G h‖ₑ * ∫⁻ n in 𝓐, ‖term ψ d W vS (om (n.1, 1) (om (g, h) Φ)) x₀‖ₑ ∂vN.ν := by
          rw [hl]
          simp only [hval]
      _ = ∫⁻ n in 𝓐, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) x₀‖ₑ ∂vN.ν := by
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          refine lintegral_congr fun n => ?_
          rw [enorm_mul, hsplit]
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFm.aemeasurable]
  refine lintegral_congr fun h => ?_
  exact hfib h

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem besGrp_iff_sA (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (g : GA D (D.sp.Y 0)) :
    g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := by
  have hS : besGrp B.d B.o = (Formalism.L2.SG.Pf.SAsub X u).comap (iotaX X h).toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := (B.tieN n).1 hn
        exact ⟨fun v => (h1 v).1, Formalism.L2.SG.Pf.nfin_sfin X u h2⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (B.tieH g).1 hg
        exact ⟨hinf_le_sinf X u _ h1, Formalism.L2.SG.Pf.hfin_sfin X u ⟨_, h2⟩⟩
    · intro g hg
      have hg' : (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := hg
      obtain ⟨hg1, hg2⟩ := hg'
      obtain ⟨hi, hhi, ni, hni, ei⟩ := Formalism.L2.SG.Pf.Sinf.levi X u hg1
      obtain ⟨hf, nf, hnf, ef⟩ := Formalism.L2.SG.Closed.FinLeviC_holds D X u _ hg2
      have hgeq : g = (iotaX X h).symm (hi, (hf : X.B.I.Gf)) * (iotaX X h).symm (ni, nf) := by
        rw [← map_mul, (iotaX X h).eq_symm_apply]
        exact Prod.ext ei ef
      rw [hgeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · refine (B.tieH _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hhi, hf.2⟩
      · refine (B.tieN _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hni, hnf⟩
  rw [hS]; rfl

theorem besGrp_eq_sGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A),
    (∀ g, g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u) ∧
      ∀ g, g ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o ↔ iotaX X h g ∈ Srat X u := by
  intro D X h u ψ A B
  refine ⟨besGrp_iff_sA D X h u ψ A B, fun g => ?_⟩
  rw [Subgroup.mem_inf, besGrp_iff_sA D X h u ψ A B, Formalism.L2.SG.Pf.srat_eq, Subgroup.mem_inf,
    Formalism.MainNotions.LeviCoordinates.rr_mem_GF, Formalism.IndefR.RationalEmbedding.iota_rat]
  have e : iotaX X h g = Formalism.L2.SG.RowsJoinPinned.castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e, castGA_mem_GFset]
  rfl

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.EvalAtZero

variable {D : D7}

theorem heisO_smul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (c : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w₀ (c • f) = c • heisO ψ S T w₀ f := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem det_UX {ρ : ℕ} (γ : UX D ρ) : Matrix.GeneralLinearGroup.det γ.1 = 1 := by
  have hu : γ.1 ∈ UX D ρ := γ.2
  rw [mem_UX] at hu
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hT : (γ.1.1 : Matrix (Fin ρ) (Fin ρ) (AE D)).BlockTriangular id := fun i j hij => (hu i j).1 hij
  rw [Matrix.det_of_upperTriangular hT]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

end GlobalTheory.EvalAtZero

namespace GlobalTheory.EvalAtZero

theorem halfMod_UX {D : D7} {ρ : ℕ} (n : ℕ) (γ : UX D ρ) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n γ.1 = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_UX, map_one, NNReal.coe_one, Real.one_rpow]

end GlobalTheory.EvalAtZero


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_rad : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)))) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => _root_.GlobalTheory.MixTargetProof.mixedTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (_root_.GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u h₀ n hn h'
  obtain ⟨b, c, rfl⟩ := ((GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d).2.1 n).1 hn
  set k := J.d.nB b * J.d.nC c * J.d.emb0 h' with hk
  have hks : k ∈ stabX J.d := mul_mem (radX_le_stabX J.d hn) (wittSmallGroupEmbedding_mem_pointwiseStabilizerIsotropic J.d h')
  have hkx : mt J.W k⁻¹ ⬝ J.d.jX = J.d.jX := inv_mem hks

  have e1 : (embA B.d B.o h₀, k) = (embA B.d B.o h₀, 1) * (1, k) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hk1 := s.weil.om_pres (1, k) Ψ hΨ
  have s1 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1) =
      om' (B.o.emb (h₀, 1), 1) (om' (1, k) (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1))) := by
    have hc := (FS _ hk1).core (B.o.emb (h₀, 1)) (xZero J.d ⬝ u.1.1)
    have ht := (FS _ hΨ).target k (xZero J.d ⬝ u.1.1)
    change B.d.mixS _ _ _ _ _ _ = _ at hc
    rw [e1, map_mul, Module.End.mul_apply, embA_apply, hc, ht, ← Matrix.mul_assoc,
      xZero, hkx]
    rfl
  set G := B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ u.1.1) with hG
  have hGt : IsThetaFunO ψ B.V₀ J.W G := MV _

  have e2 : ((1 : GA D B.V₀), k) = (1, J.d.nB b) * ((1, J.d.nC c) * (1, J.d.emb0 h')) :=
    Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, mul_one, mul_one]) (by rw [Prod.snd_mul, Prod.snd_mul, hk, mul_assoc])
  have h3 := hom'.om_pres (1, J.d.emb0 h') G hGt
  have h2 := hom'.om_pres (1, J.d.nC c) _ h3
  have hy : mt B.V₀ (B.o.emb (h₀, 1))⁻¹ ⬝ y₀ = y₀ := by
    rw [hy₀, yZero_vecB, ← map_inv, Prod.inv_mk, inv_one, ← Matrix.mul_assoc, B.o.emb_jB, mt_one, Matrix.mul_one]
  have hpt : ptT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.V₀ J.W₀ (y₀ ⬝ b) := by
    rw [ptT_nB_mul_nC, ← ptT_nB_mul_nC J.d B.V₀ y₀ b 0, J.d.nC_zero, mul_one, ptT,
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.wittSmallProjection_wittNB_inv_mul_adjointInclusion]
  have hcen : cenT J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) = J.d.qT B.V₀ c y₀ :=
    (_root_.GlobalTheory.MixPer.jacT_hom D ψ J.W J.W₀ B.V₀ ρ J.d y₀ (fun v hv => yZero_mul B.V₀ _ hv)).1 b c
  have t1 := (FT _ hGt).core h' y₀
  have t2 := (FT _ h3).centre c y₀
  have t3 := (FT _ h2).unip b y₀
  have t4 := (FT _ (hom'.om_pres (1, k) G hGt)).source (B.o.emb (h₀, 1)) y₀
  have t5 : om' (1, k) G = om' (1, J.d.nB b) (om' (1, J.d.nC c) (om' (1, J.d.emb0 h') G)) := by
    rw [e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (embA B.d B.o h₀, k) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [s1, t4, hy, t5, t3, t2, t1]
  show _ = s.om₀ (B.o.emb (h₀, 1), 1) (jacT ψ J.d B.V₀ y₀ (J.d.nB b * J.d.nC c) (s.om₀ (1, h') _))
  unfold jacT
  simp only [hpt, hcen, heisO_smul, evalAt, hG]
  rfl


open GlobalTheory.EvalAtZero in
theorem GlobalTheory.Unf.evalAt_xZero_yZero_levi : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ
  have FS := fun f hf => _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have FT := fun f hf => _root_.GlobalTheory.MixTargetProof.mixedTarget D ψ B.V₀ J.W J.W₀ ρ J.d s.χV s.χW om' s.om₀ hom' s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol f hf
  have MV := fun x => (_root_.GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  set y₀ := yZero B.V₀ ρ (vecB B.o B.ζ) with hy₀
  intro u γ
  have e0 : (mt J.W (J.d.levi γ.1)⁻¹ ⬝ (xZero J.d ⬝ u.1.1) : Mx D J.W.rank ρ) = xZero J.d ⬝ (γ⁻¹ * u).1.1 := by
    rw [← map_inv, ← Matrix.mul_assoc, levi_xZero, Matrix.mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_mul]
  change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕 ((_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d) J.W ψ s.vS.μ s.vS.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1)) y₀ = _
  rw [(FS _ hΨ).target, e0, (FT _ (MV _)).levi, yZero_mul B.V₀ _ γ.2, det_UX, halfMod_UX, map_one,
    Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  rfl

theorem GlobalTheory.Unf.evalAt_xZero_yZero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
  fun D ψ ρ B J s om' hom' Ψ hΨ => ⟨GlobalTheory.Unf.evalAt_xZero_yZero_rad D ψ ρ B J s om' hom' Ψ hΨ,
    GlobalTheory.Unf.evalAt_xZero_yZero_levi D ψ ρ B J s om' hom' Ψ hΨ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariant
section
namespace I195MixedCoordinates_33afad4828ca82e8e9e203c8

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_33afad4828ca82e8e9e203c8

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB

variable {D : D7}

theorem det_of_mem_UX {ρ : ℕ} {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    Matrix.GeneralLinearGroup.det u = 1 := by
  have hb : Matrix.BlockTriangular u.1 id := fun i j h => (hu i j).1 h
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun i _ => (hu i i).2

theorem halfMod_of_mem_UX {ρ : ℕ} (m : ℕ) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod m u = 1 := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, det_of_mem_UX hu, map_one]
  simp

theorem mixT_zero_flagN {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (ψ : AddChar (AF D.host.F) ℂ)
    (χS : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S T₀) (μ : Measure (Mx D σ S.rank)) (𝓕 : Set (Mx D σ S.rank))
    (hpres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f))
    (hF : ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.FormulasT d ψ χS om om₀ μ 𝓕 f)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (n : GA D T) (hn : n ∈ flagN d) :
    (_root_.I195MixedCoordinates_33afad4828ca82e8e9e203c8.target d) S ψ μ 𝓕 (om (1, n) f) 0 = (_root_.I195MixedCoordinates_33afad4828ca82e8e9e203c8.target d) S ψ μ 𝓕 f 0 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D T T₀ σ d).1 n).1 hn
  have e : ((1 : GA D S), d.levi u * (d.nB b * d.nC c)) = (1, d.levi u) * ((1, d.nB b) * (1, d.nC c)) := by
    simp
  have h3 := hpres (1, d.nC c) f hf
  have h2 := hpres (1, d.nB b) _ h3
  have hq : d.qT S c 0 = 0 := by
    simp [HypDec.qT, map_zero, symplOH_zero_left]
  have ha : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T₀ 0 = 0 := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  change _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ μ 𝓕 (om (1, d.levi u * (d.nB b * d.nC c)) f) 0 =
    _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target d S ψ μ 𝓕 f 0
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hF _ h2).levi, Matrix.zero_mul,
    det_of_mem_UX hu, map_one, halfMod_of_mem_UX _ hu, (hF _ h3).unip, Matrix.zero_mul, ha, (hF _ hf).centre, hq]
  funext w
  rw [AddChar.map_zero_eq_one, one_smul]
  simp only [Circle.coe_one, Complex.ofReal_one, mul_one, one_smul]
  change ψ (symplOH S T₀ w 0) * _ = _
  rw [add_zero]
  rw [show symplOH S T₀ w 0 = 0 by
    first
    | exact symplOH_zero_right S T₀ w
    | exact GlobalTheory.MixModel.symplOH_zero_right S T₀ w
    | simp [symplOH, symplO, hO]]
  rw [AddChar.map_zero_eq_one, one_mul]

theorem evalAt_zero_equivariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1))
    (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀),
    ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)),
      evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 =
        s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  intro D hD ψ σ J B s Ψ hΨ g n hn h x
  obtain ⟨om₁, hom₁⟩ := (hD ψ J.W B.V s.χV s.χW s.om s.weil).1 J.W₀ (σ + 1) J.d
  have hS := _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ J.W J.W₀ B.V (σ + 1) J.d s.χV s.χW s.om om₁ s.weil hom₁ s.vS.μ s.vS.𝓕 s.vS.covol
  have hT := _root_.GlobalTheory.MixTargetProof.mixedTarget D ψ J.W₀ B.V B.V₀ σ B.d s.χV s.χW om₁ s.om₀ hom₁ s.weil₀ s.vT.μ s.vT.𝓕 s.vT.covol
  have hV := (_root_.GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 J.W J.W₀ B.V (σ + 1) J.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ
  have hΨk := s.weil.om_pres (1, n * embA B.d B.o h) Ψ hΨ
  simp only [evalAt]
  change _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target B.d J.W₀ ψ s.vT.μ s.vT.𝓕
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source J.d B.V ψ s.vS.μ s.vS.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x) 0 =
    s.om₀ (g, B.o.emb (h, 1)) (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target B.d J.W₀ ψ s.vT.μ s.vT.𝓕
    (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source J.d B.V ψ s.vS.μ s.vS.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x)) 0)
  rw [show s.om (J.d.emb0 g, n * embA B.d B.o h) = s.om (J.d.emb0 g, 1) * s.om (1, n * embA B.d B.o h) by
    rw [← map_mul]; simp]
  rw [Module.End.mul_apply, (hS _ hΨk).core, (hS _ hΨ).target]
  have hFt := hV (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x)
  generalize _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source J.d B.V ψ s.vS.μ s.vS.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) = F at hFt ⊢
  have hF1 := hom₁.om_pres (1, B.d.emb0 (B.o.emb (h, 1))) F hFt
  have hF2 := hom₁.om_pres (1, n) _ hF1
  have hz := mixT_zero_flagN B.d ψ s.χV om₁ s.om₀ s.vT.μ s.vT.𝓕 hom₁.om_pres hT _ hF1 n hn
  change _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target B.d J.W₀ ψ s.vT.μ s.vT.𝓕 (om₁ (1, n) (om₁ (1, B.d.emb0 (B.o.emb (h, 1))) F)) 0 =
    _root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target B.d J.W₀ ψ s.vT.μ s.vT.𝓕 (om₁ (1, B.d.emb0 (B.o.emb (h, 1))) F) 0 at hz
  rw [show om₁ (1, n * embA B.d B.o h) = om₁ (1, n) * om₁ (1, B.d.emb0 (B.o.emb (h, 1))) by
    rw [← map_mul, embA_apply]; simp]
  rw [Module.End.mul_apply, (hT _ hF2).source, Matrix.mul_zero,
    hz, (hT _ hFt).core,
    show s.om₀ (g, B.o.emb (h, 1)) = s.om₀ (g, 1) * s.om₀ (1, B.o.emb (h, 1)) by rw [← map_mul]; simp,
    Module.End.mul_apply]

end GlobalTheory.Unf.FB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepEqTwoThetaColumnLiftsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts : ∀ D : D7, ContrLaw D := by
  first | exact @GlobalTheory.Unf.Contr.contrLaw | exact GlobalTheory.Unf.Contr.contrLaw | (intros; apply GlobalTheory.Unf.Contr.contrLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem family_laws : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws)
    (Z : TC.Later B (I.cols l)), (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).EqP I.chi ∧
      (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G).VecP I.chi := by
  intro B X I h _ l Z
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hδ := ((I.J.ok_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G).1 h.amb_ok).1
  have hχ : TaylorLogMetric.IsChi (assemble B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  exact ⟨GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ,
    (GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1⟩

end GlobalTheory.Core.Ht2
end

