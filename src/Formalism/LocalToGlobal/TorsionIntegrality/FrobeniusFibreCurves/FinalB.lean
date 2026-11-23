module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InvariantDerivationSubstLawThree

@[expose] public section

namespace Formalism.L2.Th1.B

theorem halfExists : HalfExists := by
  exact formal_halving_exists
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
