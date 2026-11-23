module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0639
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0723
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasInfExpMulOfIsOpenKer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

open GlobalTheory.RawLift

variable {D : D7}

theorem kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om →
    ∃ omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χV omh ∧
      ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsThetaFunO ψ (GlobalTheory.Doubling.dblSp W) V (dbl V W f₁ f₂) ∧
        ∀ h, thetaKO omh 1 h (dbl V W f₁ f₂) = thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) := by
  intro D ψ V W χV χW om hw
  have hS := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std V W
  have hom' := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V W χV χW om hw
  have hr : ResEta D 1 (GlobalTheory.Doubling.dblSp W).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D W.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp W) V 1 χV hw.std
    ⟨continuous_const, fun _ => rfl⟩ hw.hecS hr hw.resS
  refine ⟨omh, homh, fun f₁ f₂ h₁ h₂ => ?_⟩
  have TC := GlobalTheory.DoublingTheta.thetaClause D ψ W V χW χV (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) omh hom' homh
  obtain ⟨hth, hrest⟩ := TC (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) (hS.theta _ h₂) (hS.theta _ h₁)
  refine ⟨hth, fun h => ?_⟩
  have e := (hrest 1 1 h).2
  have dd : ∀ f : WO V W → ℂ, GlobalTheory.PairLift.dag W V (GlobalTheory.PairLift.dag V W f) = f := fun f => by
    funext y; simp only [GlobalTheory.PairLift.dag, hS.invol, Complex.conj_conj]
  have d0 : GlobalTheory.PairLift.adjO V W 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have k : ∀ f : WO V W → ℂ, thetaKO (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) 1 h (GlobalTheory.PairLift.dag V W f) =
      starRingEnd ℂ (thetaKO om h 1 f) := fun f => by
    simp only [thetaKO, GlobalTheory.ConjAdjWeil.conjAdjoint_apply, dd]
    simp only [GlobalTheory.PairLift.dag, d0]
  have i1 : GlobalTheory.Doubling.io W (1, 1) = 1 := map_one _
  rw [i1, k, k, Complex.conj_conj] at e
  simp only [map_one, inv_one, Circle.coe_one, mul_one] at e
  rw [show dbl V W f₁ f₂ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) from rfl, e]
  simp only [Complex.star_def]
  ring

theorem terms : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
    ∀ (χ : (AE D)ˣ →* Circle) (omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ)),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χ omh →
    ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' →
      ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
        GlobalTheory.Eis.term (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W))
          (GlobalTheory.SiegelFormula.swSection W V ν 𝓖' omh (dbl V W f₁ f₂)) 1 q = lagTerm μ 𝓕 (fr (e q)) f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χ omh hω ν 𝓖' hν
  obtain ⟨omh', -, hK⟩ := kernel D ψ V W χV χW om hs.weil
  have hF := (hK f₁ f₂ h₁ h₂).1
  obtain ⟨e, he⟩ := _root_.GlobalTheory.SWLagTerms.lagTerms_eq D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ ν 𝓖' hν
  refine ⟨e, fun q => ?_⟩
  obtain ⟨C, hC, hq⟩ := he q
  rw [← _root_.GlobalTheory.RawLift.lagTerm_frame_indep D ψ V W μ 𝓕 hs.covol hs.weil.std f₁ f₂ h₁ h₂ (e q) C (fr (e q)) hC (hs.frame _), ← hq]
  simp only [GlobalTheory.Eis.term, mul_one, GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero]
  congr 1
  funext y
  exact _root_.GlobalTheory.RatSubst.om_rat_left_apply D ψ _ V 1 χ omh hω _ hF _ (q.out : GQ (GlobalTheory.Doubling.dblSp W)).2 _

theorem swPair (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) (D : D7) : SWPair D := by
  intro ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂
  rcases Nat.eq_zero_or_pos W.rank with h0 | hr
  · exact Model.swPair_rank_zero hs h0 f₁ f₂
  obtain ⟨omh, hω, hK⟩ := kernel D ψ V W χV χW om hs.weil
  obtain ⟨hF, hθ⟩ := hK f₁ f₂ h₁ h₂
  haveI := hs.haarV
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx V = 0 := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
    exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef hs.sigOK hs.pos)
  obtain ⟨ν, 𝓖', hν⟩ := GlobalTheory.Size.exists_isCovolOne W V
  have P := (hW D W V νV hs.haarV hr (Or.inl hwitt)).2 ψ χV omh hω (dbl V W f₁ f₂) hF
  obtain ⟨-, hconv⟩ := P.2 hs.big ν 𝓖' hν
  obtain ⟨hc, hsum⟩ := hconv 1
  obtain ⟨e, he⟩ := terms D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χV omh hω ν 𝓖' hν
  have H1 := hc.hasSum
  rw [hsum] at H1
  have H2 : HasSum (fun Y : Lag W => lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    refine e.hasSum_iff.1 ?_
    convert H1 using 1
    funext q
    simp [he]
  have A : (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) =
      ⨍ h in 𝓗, thetaKO omh 1 h (dbl V W f₁ f₂) ∂νV :=
    GlobalTheory.ThetaMean.thetaMean_eq hω hF hs.fdV 1
  have vol := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V νV 𝓗 ⟨hs.haarV, hs.fdV⟩
  have hv : ((νV 𝓗).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.2 vol)
  have key : ∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV = ((νV 𝓗).toReal : ℂ) *
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    rw [A, setAverage_eq, Complex.real_smul, Measure.real, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    simp_rw [hθ]
  rw [key]
  exact H2.mul_left _

end GlobalTheory.SWPairProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramAtOfUnramOutside
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum.BasePair

variable {D : D7}

theorem placeIdem_mul_eq_zero {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hne : v' ≠ v) : ε' * ε = 0 := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  obtain ⟨α', rfl, h1', h2'⟩ := h'
  have e : α' * α = 0 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw; rw [h2' w hne.symm, zero_mul]
    · rw [h2 w hw, mul_zero]
  show pairA D.host.F 0 α' * pairA D.host.F 0 α = 0
  have e2 : pairA D.host.F 0 α' * pairA D.host.F 0 α = pairA D.host.F 0 (α' * α) := Prod.ext (mul_zero _) rfl
  rw [e2, e]
  rfl

end GlobalTheory.SingleDatum.BasePair

end
end

