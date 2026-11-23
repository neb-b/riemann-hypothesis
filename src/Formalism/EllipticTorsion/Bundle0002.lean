module

public import Mathlib
public import Formalism.EllipticTorsion.WChordSeries
public import Formalism.FormalGroupLog.Statement

@[expose] public section

-- bundled from Formalism.EllipticTorsion.CoeffRing
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def wU {K : Type u} [Field K] (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff (n + 3) w

def invSer {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) : PowerSeries K :=
  X * (-1 + C W.a₁ * X + C W.a₃ * w)⁻¹

abbrev coeffRing {K : Type u} [Field K] (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)

def CubeTwo : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let a : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
    let b : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
    ∃ c : MvPowerSeries (Fin 2) K, (∀ d, MvPowerSeries.coeff d c ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff c = -1 ∧
      b ^ 2 * ((wU w).subst a)⁻¹ - a ^ 2 * ((wU w).subst b)⁻¹
        = c * F * MvPowerSeries.subst ![a, (invSer W w).subst b] F

def CubeThree : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let t : Fin 3 → MvPowerSeries (Fin 3) K := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) K := fun i =>
      ![t i ^ 3, t i * ((wU w).subst (t i))⁻¹, -((wU w).subst (t i))⁻¹]
    ∃ e : MvPowerSeries (Fin 3) K, (∀ d, MvPowerSeries.coeff d e ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst ![MvPowerSeries.subst ![t 0, t 1] F, t 2] F
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.Statement
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def legendre {K : Type u} [CommRing K] (l : K) : WeierstrassCurve K :=
  ⟨0, -(1 + l), 0, l, 0⟩

def deuring {K : Type u} [CommRing K] (a : K) : WeierstrassCurve K :=
  ⟨a, 0, 1, 0, 0⟩

def IntegralModel {K : Type u} [NormedField K] (W : WeierstrassCurve K) : Prop :=
  ‖W.a₁‖ ≤ 1 ∧ ‖W.a₂‖ ≤ 1 ∧ ‖W.a₃‖ ≤ 1 ∧ ‖W.a₄‖ ≤ 1 ∧ ‖W.a₆‖ ≤ 1

def LegendreInv : Prop :=
  ∀ (K : Type u) [CommRing K] (l : K),
    (legendre l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 ∧ (legendre l).c₄ = 16 * (l ^ 2 - l + 1)

def DeuringInv : Prop :=
  ∀ (K : Type u) [CommRing K] (a : K),
    (deuring a).Δ = a ^ 3 - 27 ∧ (deuring a).c₄ = a * (a ^ 3 - 24)

def ModelLegendre : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(2 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ l : K, ‖l‖ = 1 ∧ ‖l - 1‖ = 1 ∧
        (legendre l).c₄ ^ 3 = j * (legendre l).Δ ∧ ‖(legendre l).Δ‖ = 1

def ModelDeuring : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K],
    ‖(3 : K)‖ = 1 → ∀ j : K, ‖j‖ ≤ 1 →
      ∃ a : K, ‖a‖ ≤ 1 ∧
        (deuring a).c₄ ^ 3 = j * (deuring a).Δ ∧ ‖(deuring a).Δ‖ = 1

def ModelUnit : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (j : K), ‖j‖ ≤ 1 →
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j

def IntValuedZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [NormedAlgebra ℚ_[p] K]
    (P : Polynomial K), (∀ n : ℕ, ‖P.eval (n : K)‖ ≤ 1) →
      ∀ b : ℤ_[p], ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1

section Cong

variable {K : Type u} [NormedField K] [CharZero K] {σ : Type}

def logOnePlus (f : MvPowerSeries σ K) : MvPowerSeries σ K := (PowerSeries.log K).subst f

def InN (G : MvPowerSeries σ K) : Prop :=
  ∃ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 ∧ IntegralMv f ∧ G = logOnePlus f

def Cong (G H : MvPowerSeries σ K) : Prop := InN (G - H)

end Cong

def NAddSubgroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type),
    InN (0 : MvPowerSeries σ K) ∧
    (∀ G H : MvPowerSeries σ K, InN G → InN H → InN (G + H)) ∧
    (∀ G : MvPowerSeries σ K, InN G → InN (-G))

def NZpSmul : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CharZero K] [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K), InN G →
      ∀ b : ℤ_[p], InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G)

def NPderiv : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (σ : Type)
    (G : MvPowerSeries σ K), InN G → ∀ i : σ, IntegralMv (MvPowerSeries.pderiv (R := K) i G)

end Formalism.ELL
end
end

