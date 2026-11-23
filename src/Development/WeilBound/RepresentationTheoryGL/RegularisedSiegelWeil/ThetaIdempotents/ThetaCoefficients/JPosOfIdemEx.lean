module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0069
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682

@[expose] public section

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := _root_.GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation (_root_.GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps _root_.GlobalTheory.CompanionTheory.Jp.Iw.jpIw _root_.GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt _root_.GlobalTheory.CompanionTheory.Jp.Unif.jpUnif _root_.GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp _root_.GlobalTheory.CompanionTheory.Jp.Pos.jpPos)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := _root_.PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact _root_.GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
