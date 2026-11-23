module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.FormalGroupConstCoeffZero
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
section
universe u v

namespace Formalism.L2.Th1.A

theorem cubeTwoR : CubeTwoR.{u} := cube_two_relation
theorem cubeThreeR : CubeThreeR.{u} := cube_three_relation
theorem coeffMem : CoeffMem.{u} := coeffMem_of zSerMap halfLog

theorem shortInv : ShortInv := short_weierstrass_inverse
theorem wpNumEq : WpNumEq := wpNumEq_of wpShape wpRecursion
theorem uSerEq : USerEq := uSerEq_of wpShape wpRecursion

end Formalism.L2.Th1.A
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementR
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

def WpPrimeInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 3 * (-2 + logSer W ^ 3 * (derivative (wpReg W)).subst (logSer W)) =
      logSer W ^ 3 * (-2 * xS W + C W.a₁ * X * xS W + C W.a₃ * X ^ 3)

def BridgeCurve3 : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    IntModel W →
    Formalism.L2.Th1.B.CurveHyp3 (fgl W) (logSer W) (wpReg W) (xS W) W.a₁ W.a₃

end Formalism.L2.Th1.A
end
end

