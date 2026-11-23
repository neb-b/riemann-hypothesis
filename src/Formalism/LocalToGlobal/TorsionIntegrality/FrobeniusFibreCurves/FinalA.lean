module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PderivZeroZeroWeierstrassDifference
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0002

@[expose] public section

namespace Formalism.L2.Th1.B

theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  exact ⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
theorem primRules : PrimRules := by
  intro K _ _ f
  exact ⟨dz_prim f, constantCoeff_prim f⟩
theorem waveUnique : WaveUnique := wave_equation_unique
theorem waveKills : WaveKills := wave_operator_kills
theorem parCauchy : ParCauchy := parallelogram_cauchy_equation
theorem dqRule : DqRule := difference_quotient_rule_holds
theorem wpReduced : WpReduced := weierstrassReducedEquations
theorem wSecond : WSecond := invertedSecondDeriv
theorem wOfWp : WOfWp := shiftedReciprocalInverted
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst dqRule
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst
theorem sigma1Sq : Sigma1Sq := Sq.sigmaOneSquare

end Formalism.L2.Th1.B
