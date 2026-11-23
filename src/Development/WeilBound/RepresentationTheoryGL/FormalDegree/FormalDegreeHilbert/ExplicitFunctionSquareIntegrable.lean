module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.NormIndOfSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.CoefPow

@[expose] public section

namespace PositivityTheory.RgFd

open PositivityTheory.RgDs

theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

theorem fdAll_of_key (hK : Key) (hH : Hilb) : FdAll := fdAll_of_norm psiNorm hK hH

end PositivityTheory.RgFd
