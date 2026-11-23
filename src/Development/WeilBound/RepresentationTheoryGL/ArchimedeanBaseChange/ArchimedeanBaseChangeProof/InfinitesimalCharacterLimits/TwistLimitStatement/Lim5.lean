module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.LimitOfFiniteDiscrete
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TreeLemmas
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypes
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394

@[expose] public section

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LimG

theorem lim5 : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc → PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5 := fun hFD =>
  PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.limit_of_finite_discrete hFD _root_.GlobalTheory.CompanionTheory.LimV.BlockTy.blockTypes _root_.GlobalTheory.CompanionTheory.TotalTrace.twBound _root_.GlobalTheory.CompanionTheory.TreeNode.nodeEmb
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.2.1 PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.1
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.1

end PositivityTheory.Rg.BcB.SpectralAccumulation.LimG
