module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExC
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.SiegelND in
theorem _root_.PositivityTheory.Rg.Rsw.L.fibEx : FibEx := by
  intro D r V hr ψ hψ θ hθ μ hμ lam hlam b₀ hb₀
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.whit_eq_coefN D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (b₀.1 b a) = b₀.1 a b := fun a b => by
    have := congrFun (congrFun b₀.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props _ _ D.sp.cm.sig hCM (AF D.host.F)
  have := hB r V.rank
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props _ _ D.sp.cm.sig hCM V.rank V.gram hJ (AF D.host.F)
  obtain ⟨ac, -, -, -⟩ := hact r
  have hTI := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ μH 𝓕 hμH h𝓕 r b₀.1
  have hfin := thFin V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀
  refine ⟨(thM V μH 𝓕 b₀.1).map (tupE D V.rank r), finE _, suppE V b₀.1 _ hTI.2,
    fun h => invE V _ h (ac.comp (continuous_const.prodMk continuous_id)).measurable (hTI.1 h), fun φ hφ => ?_⟩
  have hSB := GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ
  have hI := thInt V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀ _ hSB
  refine ⟨(tupE D V.rank r).measurableEmbedding.integrable_map_iff.2 hI, ?_⟩
  rw [hW φ b₀, (tupE D V.rank r).measurableEmbedding.integral_map]
  exact _root_.GlobalTheory.CompanionTheory.SiegelND.Coef.coefN_eq_theta D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb μH 𝓕 hμH h𝓕 _ hSB
    b₀.1 hT hb₀

end PositivityTheory.Rg.Rsw.L.LFibEx

end
