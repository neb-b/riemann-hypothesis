module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementS
public import Formalism.GaussJetBounds.Bundle0002
public import Formalism.GaussJetBounds.StatementP
public import Formalism.GaussJetBounds.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementR

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

section DefsK

variable {K : Type} [Field K]

def betaPair (H : Type) [Fintype H] (N0 N1 : ℕ) (u : H → K) :
    MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) K :=
  ∑ t : H, ∑ ab : Fin N0 × Fin N1, MvPowerSeries.C (u t) *
    MvPowerSeries.X ((false, t), ab.1, ab.2) * MvPowerSeries.X ((true, t), ab.1, ab.2)

end DefsK

end Formalism.L2.Th1.G
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

section DefsT

variable {K : Type} [Field K]

def th0 [CharZero K] (W : WeierstrassCurve K) (x0 y0 s2 : K) : PowerSeries K :=
  mvExp (-(lam (wTr W x0 y0) s2))

end DefsT

def KernelTwo : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l linv ph : PowerSeries K),
    IsLogPair l linv → IsOneUnit (unitBall K) (PowerSeries.derivative (R := K) l) →
    PowerSeries.constantCoeff ph = 0 → (∀ i : ℕ, 1 ≤ i → ‖jet l ph i‖ ≤ 1) →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) ∧
    ∀ P : MvPolynomial n K, (∀ m, ‖AddMonoidAlgebra.coeff P m‖ ≤ 1) →
      ‖jetPair P (toZ linv (mvExp (-(phSum c ph)) * G))‖ ≤ 1

def SplitVanishTwo : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → F1 R l linv ph → EndInt R l linv a →
    a ∈ closure (Set.range (fun n : ℤ => (n : K))) → PhNormAt R l linv ph a b →
    a ≠ 0 → a ≠ b → b ≠ 1 →
    IsBinomScalar R (a * (a - b))⁻¹ → IsBinomScalar R (a * (1 - b))⁻¹ →
    LG R ph

end Formalism.L2.Th1.G
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementV
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

def CurveJetsUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    ‖al - albar‖ = 1 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ i : ℕ, 1 ≤ i → ‖jet (logSer W) (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)) i‖ ≤ 1

end Formalism.L2.Th1.G
end
end

