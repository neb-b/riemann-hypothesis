module

public import Formalism.FormalGroupWitt.Statement
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.Bundle0001
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot

@[expose] public section

namespace Formalism.FG

universe u v w

theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
