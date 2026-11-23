module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0309
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306

@[expose] public section

namespace PositivityTheory.Rg.BcB.D1

theorem mulF : MulF := _root_.GlobalTheory.CompanionTheory.WedgeMinor.mulF
theorem detMono : DetMono := _root_.GlobalTheory.CompanionTheory.DetMonotone.detMono
theorem mulI : MulI := _root_.GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono detMono
theorem wedgeF : WedgeF := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF mulF
theorem wedgeI : WedgeI := _root_.GlobalTheory.CompanionTheory.Wedge.wedgeI_of_detMono_mulI detMono mulI
theorem wedgeSub : WedgeSub := _root_.GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub
theorem pairF : PairF := _root_.GlobalTheory.CompanionTheory.Wedge.pairF_of_mulF mulF
theorem pairI : PairI := _root_.GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono detMono
theorem logAbsBasic : LogAbsBasic := _root_.GlobalTheory.CompanionTheory.LogAbs.logAbsBasic
theorem szFin : SzFin := _root_.GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
theorem finSupp : FinSupp := _root_.GlobalTheory.CompanionTheory.WedgeSupport.finSupp_of_mul mulF mulI szFin
theorem degAdelic : DegAdelic := GlobalTheory.T.adelic_degree_formula mulF mulI logAbsBasic finSupp
theorem degBasisG : DegBasisG := _root_.GlobalTheory.CompanionTheory.DegBasisGen.degBasisG_of wedgeF wedgeI mulF mulI logAbsBasic finSupp
theorem degBasis : DegBasis := _root_.GlobalTheory.CompanionTheory.DegreeBasis.degBasis_of_degBasisG degBasisG
theorem degSubmod : DegSubmod := GlobalTheory.T.degree_submodule_bound wedgeF wedgeI wedgeSub finSupp degBasisG _root_.GlobalTheory.CompanionTheory.LinAlg.twoBases
theorem degRat : DegRat := _root_.GlobalTheory.CompanionTheory.Degree.degRat_of_degBasisG degBasisG
theorem degMove : DegMove := _root_.GlobalTheory.CompanionTheory.DegMoveProof.degMove_of mulF mulI szFin finSupp degBasisG
theorem degBdd : DegBdd := _root_.GlobalTheory.CompanionTheory.DegBound.degBdd_of wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
theorem conjPlaces : ConjPlaces := GlobalTheory.T.conjugate_places_facts
theorem sizeBasic : SizeBasic := _root_.GlobalTheory.CompanionTheory.Size.sizeBasic szFin conjPlaces
theorem degPairing : DegPairing :=
  _root_.GlobalTheory.CompanionTheory.DegPairingProof.degPairing_of wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG _root_.GlobalTheory.CompanionTheory.RadicalForm.radical
theorem mahler_of_c (h : MahlerC) : Mahler := _root_.GlobalTheory.CompanionTheory.Cutoff.mahler_of degBdd degRat h
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
theorem onlyStable : OnlyStable := _root_.GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of degSubmod degMove degBdd degPairing sizeBasic
theorem onlyIsotropic : OnlyIsotropic := _root_.GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of onlyStable degPairing sizeBasic
theorem ellTerm : EllTerm := _root_.GlobalTheory.CompanionTheory.EllIso.ellTerm_of_onlyIsotropic onlyIsotropic
theorem chainSum : ChainSum := fun m =>
  ⟨_root_.GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator m, _root_.GlobalTheory.CompanionTheory.SignChain.gam_support m, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.1, (_root_.GlobalTheory.CompanionTheory.ChainSum.chainSum_rest m).2.2⟩

end PositivityTheory.Rg.BcB.D1
