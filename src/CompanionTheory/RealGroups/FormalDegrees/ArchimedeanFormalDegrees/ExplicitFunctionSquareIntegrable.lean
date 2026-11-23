module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.NormIndOfSteps
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0671
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CoefPow

@[expose] public section

namespace CompanionTheory.RgFd

open CompanionTheory.RgDs

theorem psiNorm : PsiNorm := psiNorm_of (normInd_of_steps coefPow GlobalTheory.CompanionTheory.RgFdNorm.norm_induction_of_estimates)

theorem explicit_function_square_integrable : ExplicitFunctionSquareIntegrable := square_integrable_of_norm psiNorm

end CompanionTheory.RgFd
