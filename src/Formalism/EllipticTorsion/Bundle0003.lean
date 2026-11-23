module

public import Mathlib
public import Formalism.EllipticTorsion.Bundle0002
public import Formalism.EllipticTorsion.Bundle0001

@[expose] public section

-- bundled from Formalism.EllipticTorsion.ChangeIntegral
section
universe u

namespace Formalism.ELL

def ChangeIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (C : WeierstrassCurve.VariableChange K),
    IntegralModel W → IntegralModel (C • W) → W.Δ ≠ 0 → ‖(C • W).Δ‖ = ‖W.Δ‖ →
      ‖(C.u : K)‖ = 1 ∧ ‖C.r‖ ≤ 1 ∧ ‖C.s‖ ≤ 1 ∧ ‖C.t‖ ≤ 1

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.CompExpWeight
section
open PowerSeries

universe u

namespace Formalism.ELL

open Formalism.G

def CompExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (σ : Type) [Finite σ] (c : ℝ),
    0 < c → c ≤ 1 →
    ∀ E : PowerSeries K, constantCoeff E = 0 →
      (∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ c ^ (1 - (n : ℤ))) →
    ∀ G : MvPowerSeries σ K, IntegralMv G → ∀ α : σ →₀ ℕ,
      ‖MvPowerSeries.coeff α
          (MvPowerSeries.subst (fun i : σ => E.subst (MvPowerSeries.X i : MvPowerSeries σ K)) G)‖
        ≤ c ^ (-(α.degree : ℤ))

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.FormalGroupPointsTorsionFree
section
universe u

noncomputable section

local instance (α : Sort u) : DecidableEq α := Classical.decEq α

namespace Formalism.ELL

open WeierstrassCurve

def InFormalGroupPoints {K : Type u} [NormedField K] {W : WeierstrassCurve K} : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < ‖x‖


open Classical in
def FormalGroupPointsSubgroup' : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → InFormalGroupPoints (P + Q) ∧ InFormalGroupPoints (-P)


open Classical in
def FormalGroupPointsTorsionFree : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ P : W.toAffine.Point, InFormalGroupPoints P → n • P = 0 → P = 0


open Classical in
def TorsionIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      n • (Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.JetsCube
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

abbrev FK (F : FormalGroup (unitBall K)) : FormalGroup K := F.map (unitBall K).subtype

abbrev Y3 (i : Fin 3) : MvPowerSeries (Fin 3) K := MvPowerSeries.X i

def F2 (F : FormalGroup (unitBall K)) (i j : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![Y3 i, Y3 j] (FK F).toPowerSeries

def F3 (F : FormalGroup (unitBall K)) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![F2 F 0 1, Y3 2] (FK F).toPowerSeries

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.UnitCancel
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

def LogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 → 2 ≤ q →
    ∀ (F : FormalGroup (unitBall K)) (e l : PowerSeries K),
      IsHom (F.map (unitBall K).subtype) (F.map (unitBall K).subtype) e → IntegralPS e →
      coeff 1 e = p → (∀ n, 2 ≤ n → n < q → coeff n e = 0) →
      IsLog (F.map (unitBall K).subtype) l →
      ∀ n : ℕ, 1 ≤ n → ‖coeff n l‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((q : ℝ) - 1))

def UnitCancel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K) (b : ℤ_[p]), IsUnit b →
      InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G) → InN G

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.VeluIntegralModel
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

section Velu

variable {L : Type u} [Field L]

def veluGx (W : WeierstrassCurve L) (x y : L) : L := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
def veluGy (W : WeierstrassCurve L) (x y : L) : L := -2 * y - W.a₁ * x - W.a₃
open Classical in
def veluV (W : WeierstrassCurve L) (x y : L) : L :=
  if veluGy W x y = 0 then veluGx W x y else 2 * veluGx W x y - W.a₁ * veluGy W x y
def veluU (W : WeierstrassCurve L) (x y : L) : L := veluGy W x y ^ 2

def veluCurve (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) : WeierstrassCurve L :=
  ⟨W.a₁, W.a₂, W.a₃,
    W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2),
    W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))⟩

def veluX (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) (x : L) : L :=
  x + ∑ i, (veluV W (S i).1 (S i).2 / (x - (S i).1) + veluU W (S i).1 (S i).2 / (x - (S i).1) ^ 2)

def veluY (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) (x y : L) : L :=
  y - ∑ i, (veluU W (S i).1 (S i).2 * (2 * y + W.a₁ * x + W.a₃) / (x - (S i).1) ^ 3
      + veluV W (S i).1 (S i).2 * (W.a₁ * (x - (S i).1) + y - (S i).2) / (x - (S i).1) ^ 2
      + (W.a₁ * veluU W (S i).1 (S i).2 - veluGx W (S i).1 (S i).2 * veluGy W (S i).1 (S i).2)
          / (x - (S i).1) ^ 2)

end Velu

def VeluIntegralModel : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K) (k : ℕ)
    (S : Fin k → K × K), IntegralModel W → (∀ i, ‖(S i).1‖ ≤ 1 ∧ ‖(S i).2‖ ≤ 1) →
      IntegralModel (veluCurve W S)

def VeluUSeries : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (w : PowerSeries K) (k : ℕ) (S : Fin k → K × K),
    IntegralModel W → WFixed W w → (∀ i, ‖(S i).1‖ ≤ 1 ∧ ‖(S i).2‖ ≤ 1) →
    let L := FractionRing (MvPowerSeries Unit K)
    let WL := W.map (algebraMap K L)
    let SL : Fin k → L × L := fun i => (algebraMap K L (S i).1, algebraMap K L (S i).2)
    let x := xOf w (MvPowerSeries.X () : MvPowerSeries Unit K)
    let y := yOf w (MvPowerSeries.X () : MvPowerSeries Unit K)
    ∃ f : PowerSeries K, IntegralPS f ∧ coeff 0 f = 0 ∧ coeff 1 f = 1 ∧
      algebraMap (MvPowerSeries Unit K) L f = -(veluX WL SL x) / veluY WL SL x y

end Formalism.ELL
end
end

