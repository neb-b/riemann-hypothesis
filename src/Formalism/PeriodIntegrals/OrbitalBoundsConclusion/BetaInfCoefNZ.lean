module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Bundle0003

@[expose] public section

namespace PI.BICNZ

theorem betaInfCoefNZ_proof_of (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) : Formalism.MainNotions.S.Pv.BetaCut.BetaInfCoefNZ :=
  betaInfCoefNZ_of_limits hS lim_leftLimit lim_rightLimit

end PI.BICNZ
