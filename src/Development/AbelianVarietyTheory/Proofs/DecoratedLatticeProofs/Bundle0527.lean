module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0524
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0525
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartTwist

theorem chart_dict : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ
  have hpl := _root_.GlobalTheory.PlaceProjAt.under_resCard D v φ PP hφ
  refine ⟨hpl.1, hpl.2, fun ξl h => _root_.GlobalTheory.tameLift_isTame_not_isUnram D v φ PP (w.ξ PP) hφ (hw.ne PP hPP) ξl h, ?_, ?_⟩
  · intro k hk μ hμ
    have hres := _root_.GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
    have hPg : PP ∈ c.Pg := by
      classical
      rw [hw.union]; exact Finset.mem_union.2 (Or.inr hPP)
    have hq : (c.chi (k + 1) PP)⁻¹ = w.ξ PP := by rw [hw.chiQ (k + 1) PP hPP, inv_inv]
    rcases hμ with hμ | hμ
    · exact _root_.GlobalTheory.ResLift.liftsChar_of_resAt D _ PP _ (hq ▸ (hres.1 PP hPg).1) v φ hφ μ hμ
    · exact _root_.GlobalTheory.ResLift.liftsChar_of_resAt D _ PP _ (hq ▸ (hres.1 PP hPg).2) v φ hφ μ hμ
  · intro ι hι
    have hfl := hs.choose_spec.2
    obtain ⟨e, he⟩ := _root_.GlobalTheory.ChartSplitIso.exists_equiv_emb D s j v φ ι hfl.selfDual hfl.frame hι
    refine ⟨⟨e, he, _root_.GlobalTheory.ChartStab.chart_stab D s j v φ ι hfl.selfDual hfl.frame hι e he, _root_.GlobalTheory.ChartHgt.isHgt_chart D s j v φ ι hfl.selfDual hfl.frame hι e he⟩,
      _root_.GlobalTheory.chart_level_iff D c w hw j hj s hs PP hPP v φ hφ ι hι, ?_⟩
    intro ξl hξ y hy d hd
    exact _root_.GlobalTheory.ChartChi.levChi_chart D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd

end GlobalTheory.ChartTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairsExistAtLevelPrimeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairs_exist_at_levelPrime : GlobalTheory.AdForm.StdEx' := by
  first | exact @GlobalTheory.AdForm.StdExProof.stdEx' | exact GlobalTheory.AdForm.StdExProof.stdEx' | (intros; apply GlobalTheory.AdForm.StdExProof.stdEx' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralInertAdelicStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_doubling_integral_inert_adelic : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.LocZetaInertAd.localZetaOn_inert | exact GlobalTheory.LocZetaInertAd.localZetaOn_inert | (intros; apply GlobalTheory.LocZetaInertAd.localZetaOn_inert <;> assumption)
end

