module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular

@[expose] public section

namespace Formalism.L2.Th1.E

theorem generalIntOf : GeneralIntOf := general_integrality
theorem torsionIntegral : TorsionIntegral := torsion_integral
theorem ptOfZero : PtOfZero := PtOfZero_of
theorem wpBridge : WpBridge := AnaSys.wpBridge
theorem transWpBridge : TransWpBridge := AnaSys.transWpBridge
theorem analyticSys : AnalyticSys := AnalyticSys_of transWpBridge
theorem opUTh0Root : OpUTh0Root := OpUTh0Root_of

theorem ptOfInt_of_add (hA : PtOfAdd) : PtOfInt := PtOfInt_of hA ptOfZero torsionIntegral
theorem kernelPtInt_of_add (hA : PtOfAdd) : KernelPtInt := KernelPtInt_of (ptOfInt_of_add hA)
theorem cm4Int_of_add (hA : PtOfAdd) : CMIntegrality := cm_integrality_of_torsion_points (ptOfInt_of_add hA)
theorem analyticTrans_of_add (hA : PtOfAdd) : AnalyticTrans :=
  AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit
theorem th0Analytic_of_add (hA : PtOfAdd) : ThetaZeroAnalytic :=
  Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root

theorem ptOfAdd : PtOfAdd := PtOfAdd_of
theorem ptOfInt : PtOfInt := ptOfInt_of_add ptOfAdd
theorem kernelPtInt : KernelPtInt := kernelPtInt_of_add ptOfAdd
theorem cm4Int : CMIntegrality := cm4Int_of_add ptOfAdd
theorem analyticTrans : AnalyticTrans := analyticTrans_of_add ptOfAdd
theorem th0Analytic : ThetaZeroAnalytic := th0Analytic_of_add ptOfAdd

end Formalism.L2.Th1.E
