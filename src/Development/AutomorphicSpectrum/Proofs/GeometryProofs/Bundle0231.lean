module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HalfLatticeTypes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Formalism.MeanHeightDescent.CombinedAverageDegreeBound
public import Formalism.MonomialMeanResidues.FilteredDegree
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0230
public import Development.WeilBound.CoreStatements.ProjectiveValuations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsGlobal
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem exists_isGlobal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (l : Level H) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∃ Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F), Top.IsGlobal Xo l c Y := by
  intro E _ _ _ H Dw Xo l c hpq hg hA
  obtain ⟨-, hI⟩ := GlobalTheory.CompanionTheory.Ar.Top.partI_holds
  obtain ⟨Yl, hYl, hN6⟩ := hI E H Dw hpq Xo
  obtain ⟨Ygl, hD, hDom⟩ := hN6 l c hg hA
  exact ⟨Ygl, Yl, hg, hYl, hA, hD, hDom⟩

end GlobalTheory.CompanionTheory.Ar.Rec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldOfDatumAbelian
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem field_of_datum_abelian : ∀ D : D7, IsAbelianGalois ℚ D.host.E := by
  intro D
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  haveI : IsMulCommutative (D.host.E ≃ₐ[ℚ] D.host.E) :=
    ⟨⟨fun s t => GlobalTheory.Mem.FieldsLaws.gal_comm D.host s t⟩⟩
  exact {}

end GlobalTheory.CompanionTheory.Ar.Rec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReading
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS

theorem GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x :=
  @DifferentiableLines.holomorphic_extension_sections
end

