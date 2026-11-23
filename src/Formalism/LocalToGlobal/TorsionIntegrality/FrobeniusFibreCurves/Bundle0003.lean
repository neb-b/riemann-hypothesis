module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
section
namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)

def QuadTwoAdic : Prop :=
  ∀ T N : ℤ, Odd T → Even N →
    ∃ b b' : ℤ_[2], b + b' = (T : ℤ_[2]) ∧ b * b' = (N : ℤ_[2]) ∧ ‖b‖ = 1 ∧ ‖b'‖ < 1

def RootsTwoAdic : Prop :=
  ∀ (ι : ℂ ≃+* ℂ_[2]) (α : ℂ) (T N : ℤ), α + conj α = (T : ℂ) → α * conj α = (N : ℂ) → Odd T →
    Even N → ∃ b b' : ℤ_[2], ‖b‖ = 1 ∧ ‖b'‖ < 1 ∧
      ((ι α = ((b : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b' : ℚ_[2]) : ℂ_[2])) ∨
        (ι α = ((b' : ℚ_[2]) : ℂ_[2]) ∧ ι (conj α) = ((b : ℚ_[2]) : ℂ_[2])))

def ThetaZeroTwoTrace : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W →
    ‖W.a₁‖ = 1 → ∀ (α ω₀ : ℂ) (T N : ℤ), MulStable L α → α + conj α = (T : ℂ) →
    α * conj α = (N : ℂ) → Odd T → Even N →
    ω₀ ∈ L.lattice → α * (ω₀ / 2) ∉ L.lattice → conj α * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

def ThetaZeroTwoCM : Prop :=
  ∀ (d : ℕ) (L : PeriodPair), d % 8 = 7 → Formalism.L2.Th1.CM.HasCMBy d L →
    ∀ (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), Unif 2 L ι W → IntCurve W → ‖W.a₁‖ = 1 →
    ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → Formalism.L2.Th1.CM.omegaK d * (ω₀ / 2) ∉ L.lattice →
    conj (Formalism.L2.Th1.CM.omegaK d) * (ω₀ / 2) ∉ L.lattice →
    Simeq (ι := Unit) (evenSigmaLogAtTwoTorsion W (ι (Formalism.L2.Th1.F.s2 L)) (px W (ptW 2 L ι W (ω₀ / 2)))) 0 ∧
      OneUnit (inW 2 ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) ∧
      ∀ (s : ℂ) (M : ℕ), 0 < M → ¬ 2 ∣ M → (M : ℂ) * s ∈ L.lattice →
        GaussOne (inW 2 ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.B
end
end

