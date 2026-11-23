module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0650
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestTermLemmaReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0421

@[expose] public section

namespace PositivityTheory.RgBcC.RealD

theorem countG_holds : CountG := GlobalTheory.CompanionTheory.RealCountG.countG

theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := GlobalTheory.CompanionTheory.DiracKType0.dirac_inequality_k_types

theorem adm_least_zero_holds : AdmLeast0 :=
  adm_least_zero_of_dirac GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T dirac_inequality_k_types GlobalTheory.CompanionTheory.SpinBound.lemmaHT

theorem adm_least_holds : AdmLeast := adm_least_of_zero_module adm_least_zero_holds

end PositivityTheory.RgBcC.RealD
