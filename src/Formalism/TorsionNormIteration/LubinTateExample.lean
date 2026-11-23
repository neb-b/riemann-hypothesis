module

public import Formalism.TorsionNormIteration.InverseIntegralClasses.Bundle0001
public import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.Bundle0002
public import Formalism.TorsionNormIteration.InvIntegralOfClass
public import Formalism.FormalGroupLog.Statement

@[expose] public section

namespace Formalism.LT

universe u v

theorem funEqSubst : Formalism.G.FunEqSubst.{u, v} :=
  FunEqSubst_of IntegralSubst_proof CoeffBound_valid PowCongr_valid FrobCongr_valid

theorem funEqGroup : Formalism.G.FunEqGroup.{u} :=
  FunEqGroup_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

theorem funEqHom : Formalism.G.FunEqHom.{u} :=
  FunEqHom_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

end Formalism.LT
