module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.PureIdentity
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.HermitianIntegration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfWsf.Hand.Merge

theorem siegelND : PositivityTheory.GramSchwartzFunctions.BC.SiegelND := by
  intro D r V ψ θ μ lam ν φ hyp β hβ
  obtain ⟨hr, hψ, hθ, hμ, hlam, hν, hφ, habs⟩ := hyp
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (β.1 b a) = β.1 a b := fun a b => by
    have := congrFun (congrFun β.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  have hInt := fun Φ hΦ => PositivityTheory.PfWsf.Hand.TupleUntupling.hermitian_unfolding_integral r V ψ hψ θ hθ μ hμ lam hlam hr dx hdx.1 db hdb.1 Φ hΦ
  have hc := PositivityTheory.PfWsf.Hand.CoreH.coreH D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb
    hInt μH 𝓕 hμH h𝓕 _ (GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ) β.1 hT hβ
  rw [GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate D r V θ hθ ν hν φ hφ habs μH 𝓕 hμH h𝓕 β hβ, hW φ β, hc]
  rfl

end PositivityTheory.PfWsf.Hand.Merge
