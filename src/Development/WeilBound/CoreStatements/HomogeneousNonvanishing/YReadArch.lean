module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
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
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YReadArchC
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.UnitarySelfGeneration

theorem y_read_arch : (Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c) (Rd : Reading Fr h Z), ∃ u : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) u ∧ ∀ (σ : c.F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal RM.y), (∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) z (σ t)) → MvPolynomial.aeval z u ≠ 0 → ∃ k, Over (U (goodOf c σ)) (e Z) k ∧ ∃ y ∈ ((U (goodOf c σ)).X k).dom, ∀ (a : WZ E) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = RM.coef (towerWt Dw a) 0 j) → ∃ θ : ℂ, ‖θ‖ = (∏ r', (Or.sing r').h z ^ n' (some r')) * lieFacZ Dw x a * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a k) (fun _ => 1) y ∧ ∀ f ∈ secZ Xo c a, (GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * rdU (U (goodOf c σ)) f k y)) ∧ (¬ GoodEmb c σ → Small.HasVal RM.y (Top.combLine (RM.line 1) n').a (Fr.rd f * (∏ r', Or.e r' ^ (-n' (some r')))) z (θ * starRingEnd ℂ (rdU (U (goodOf c σ)) f k y)))) := by
  intro _ E _ _ _ H Dw l Xo c r U h e hL x hx O _ β Y SS RM Sys Fx Or Fr Z Rd
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Good.exists_finset E H Dw l Xo c O β Y SS RM Sys Fx Or Fr
  obtain ⟨u, hu, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub.exists_subring_val RM.K RM.ι RM.Ω RM.y RM.birational B
  refine ⟨u, hu, fun σ z hz hcst hzu => ?_⟩
  have hz' := RA.ptsOver_of_mcPts hz
  by_cases hσ : GoodEmb c σ
  · have eg : goodOf c σ = σ := if_pos hσ
    rw [eg]
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ z hz' hzu
    obtain ⟨-, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hσ hz' ev hev hcst
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    exact ⟨θ, h1, fun f hf => ⟨fun _ => h2 f hf, fun hn => absurd hσ hn⟩⟩
  · have eg : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    have hg := goodEmb_goodOf c σ
    have hcst' : ∀ t : c.F, Small.HasVal RM.y 0 (Or.𝔐.cst t) (fun p => starRingEnd ℂ (z p)) (goodOf c σ t) := fun t => by
      rw [eg]
      exact RA.hv_conj (hcst t)
    have hz'' := RA.ptsOver_conj hz'
    obtain ⟨A, ev, hBA, hQ, hev⟩ := hA ℂ _ hz'' (by rw [RA.aeval_conj]; exact (map_ne_zero _).2 hzu)
    obtain ⟨hc, k, hk, y, hy, hh⟩ := RA.core hL hx Rd (hB A hBA hQ) hg hz'' ev hev hcst'
    simp only [Complex.conj_conj] at hc
    refine ⟨k, hk, y, hy, fun a n' hn => ?_⟩
    obtain ⟨θ, h1, h2⟩ := hh a n' hn
    refine ⟨starRingEnd ℂ θ, ?_, fun f hf => ⟨fun hn => absurd hn hσ, fun _ => ?_⟩⟩
    · rw [Complex.norm_conj, h1]
      simp only [← hc]
    · have h3 := RA.hv_conj (h2 f hf)
      simp only [Complex.conj_conj, map_mul] at h3
      exact h3

end PositivityTheory.UnitarySelfGeneration
