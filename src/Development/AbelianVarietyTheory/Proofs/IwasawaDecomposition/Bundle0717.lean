module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0716
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupPinsOfMuIsW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw


set_option maxHeartbeats 4000000 in
theorem datExt0_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt0 := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine ((_root_.GlobalTheory.Mem.R3.Rw.ExtBuild.exists_ext_build h1 h2 h3 h4 h5 h6 h7).and (_root_.GlobalTheory.Mem.R3.TwistedPlaceExtensions.extendedData_nonzero_index_places_correspond h1 h2 h3 h4 h5 h6 h7)).trans (StepW.of_all ?_)
  intro K B' f' T' w' _ _ hAB B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV
  obtain ⟨z', hz', he⟩ := hAB.1 B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV
  exact ⟨z', hz', he.ext (hAB.2 B f T w hE hf hP hpx Z hX Wt z hg hga hF hL Z' hX' hg' hga' hV z' hz' he)⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PublishedInputsImplyConclusion
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th

namespace GlobalTheory.Mem.Top.Closing

theorem divEx_geoCl (h1 : GlobalTheory.NT.RayField) (h2 : GlobalTheory.Published.PrincipalIdealSt) (h3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt)
    (R : RPosition) (N : NCondition) (S : SPosition) : DivEx ⟨R, N, S, OX (geoCl anyGeometry)⟩ := by
  have h := GlobalTheory.Mem.Top.DivRec.divEx_of_ox h1 h2 h3 ⟨R, N, S, OX anyGeometry⟩ rfl
  refine GlobalTheory.Mem.Top.Bl.StepW.trans h (GlobalTheory.Mem.Top.Bl.StepW.of_all ?_)
  intro K B f T w _ _ hw Z l
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := hw Z
    { g := l.g, coh := l.coh, Wt := l.Wt, p0 := l.p0, what₂ := l.what₂, rx := l.rx, nch := l.nch, n := l.n, xd := l.xd,
      chiT := l.chiT, nx := l.nx, col := l.col, real := l.real, dsig_eq := l.dsig_eq, del := l.del, sx := l.sx }
  refine ⟨Y, hY1, hY2, hY3, fun O t e1 e2 e3 => ?_⟩
  obtain ⟨o⟩ := hY4 O t e1 e2 e3
  exact ⟨⟨geoCl_of o.geo, o.lam⟩⟩

theorem io_zero (𝒮 : Slots) (h : 𝒮.Rx = RX) : ∀ K B f T (w : ColW B f T) (Z : w.Lt) Wt p0 (t : RowsT K w Z Wt p0),
    𝒮.Rx K B f T w Z Wt p0 t → ∀ μ, ¬ Formalism.IndefR.RecTie.Used0 (w.D Z) μ → ∀ j, j < (w.D Z).R.m → (w.D Z).what₂.io μ j = 0 := by
  intro K B f T w Z Wt p0 t r μ hμ j _
  rw [h] at r
  exact (RXs.io r μ j hμ).1

end GlobalTheory.Mem.Top.Closing
end

