module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0489
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficient

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem siegelDeg : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg := by
  intro D r V ψ θ μ lam ν φ hH β hβ
  obtain ⟨a, t, γ, ha, hγ, rfl⟩ := GlobalTheory.T.singular_hermitian_congruent_block_normal_form D r β hβ
  rw [_root_.GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH D V ν r φ γ a ha, ← _root_.GlobalTheory.CompanionTheory.WeilSiegel.Deg.W_congr D r V ψ μ lam φ γ a ha hH.2.2.2.1 hH.2.2.2.2.1]
  have hH' := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Deg.hyp_pull D r V ψ θ μ lam ν φ a ha hH
  by_cases hx : ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = γ.1
  · exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.Frame.siegel_frame D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx
  · exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.noFrame D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
