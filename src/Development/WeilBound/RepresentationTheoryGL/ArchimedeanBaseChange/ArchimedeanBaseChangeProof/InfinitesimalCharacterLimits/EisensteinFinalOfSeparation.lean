module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.EFinalOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.IsometrySymmetry.IsoVSymm
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitVectorIdentity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation

theorem eisenstein_final_of_separation (hS : Sep4) : EFinal :=
  eFinal_of hS FiniteDiscreteTypes.finDisc (_root_.GlobalTheory.CompanionTheory.LimV.limVec : LimVec)

end PositivityTheory.Rg.BcB.SpectralAccumulation
