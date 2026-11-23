module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
public import Formalism.FormalGroupLog.LogDeterminesLaw

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

abbrev U₁ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0

abbrev U₂ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1

def FglMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    MvPowerSeries.map φ (fgl W) = fgl (W.map φ)

def FglChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    lam W * (U₂ - U₁) = (wSer W).subst (U₂ : MvPowerSeries (Fin 2) R) - (wSer W).subst (U₁ : MvPowerSeries (Fin 2) R) ∧
    MvPowerSeries.constantCoeff (uThird W) = 0 ∧
    wThird W = (wSer W).subst (uThird W) ∧
    fgl W = (iSer W).subst (uThird W) ∧
    MvPowerSeries.constantCoeff (fgl W) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (fgl W) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (fgl W) = 1

def FglSum : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K),
    Formalism.ELL.ChordAt W (wSer W) U₁ U₂ (fgl W)

def FglGroup : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ F : FormalGroup R, F.toPowerSeries = fgl W ∧ F.IsComm

def FglLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) ∧
    fgl W = (expSer W).subst ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K))

def FglInv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    MvPowerSeries.subst (![X, iSer W] : Fin 2 → R⟦X⟧) (fgl W) = 0

def ZSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    (∀ n : ℤ, constantCoeff (zSer W n) = 0 ∧ coeff 1 (zSer W n) = (n : R)) ∧
    zSer W 0 = 0 ∧ zSer W 1 = X ∧ zSer W (-1) = iSer W ∧
    (∀ n : ℕ, zSer W (n : ℤ) = nSer W n) ∧
    (∀ m n : ℤ, MvPowerSeries.subst (![zSer W m, zSer W n] : Fin 2 → R⟦X⟧) (fgl W)
      = zSer W (m + n)) ∧
    (∀ m n : ℤ, (zSer W m).subst (zSer W n) = zSer W (m * n))

def ZSerMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (n : ℤ), PowerSeries.map φ (zSer W n) = zSer (W.map φ) n

def ZSerLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ),
    (logSer W).subst (zSer W n) = C (n : K) * logSer W

def HalfSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), IsUnit (2 : R) →
    constantCoeff (halfSer W) = 0 ∧ 2 * coeff 1 (halfSer W) = 1 ∧
    (nSer W 2).subst (halfSer W) = X ∧ (halfSer W).subst (nSer W 2) = X ∧
    MvPowerSeries.subst (![halfSer W, halfSer W] : Fin 2 → R⟦X⟧) (fgl W) = X

def HalfLog : Prop :=
  (∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    2 * (logSer W).subst (halfSer W) = logSer W) ∧
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    IsUnit (2 : R) → PowerSeries.map φ (halfSer W) = halfSer (W.map φ)

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementP
section
open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

def TSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP : R),
    constantCoeff (tDen W xP) = 1 ∧ tDen W xP * invOfUnit (tDen W xP) 1 = 1 ∧
    toL (tS W xP) * (xL W - HahnSeries.C xP) = 1 ∧
    coeff 2 (tS W xP) = 1 ∧ X ^ 2 ∣ tS W xP ∧
    (tS W xP).subst (iSer W) = tS W xP

def PlusChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP)

def PlusFlow : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    IsFlow (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) ∧
    constantCoeff (xPlus W xP yP) = xP ∧ constantCoeff (yPlus W xP yP) = yP

def PlusLogDeriv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xP yP : R), W.toAffine.Equation xP yP →
    DL W (toL (tS W xP) * DL W (xL W))
      = 2 * xL W - toL (xPlus W xP yP) - toL (xPlus W xP (W.toAffine.negY xP yP))

def PlusMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (xP yP : R),
    PowerSeries.map φ (tS W xP) = tS (W.map φ) (φ xP) ∧
    PowerSeries.map φ (xPlus W xP yP) = xPlus (W.map φ) (φ xP) (φ yP) ∧
    PowerSeries.map φ (yPlus W xP yP) = yPlus (W.map φ) (φ xP) (φ yP)

def TwoTorsionU : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (xT yT : R), W.toAffine.Equation xT yT →
    2 * yT + W.a₁ * xT + W.a₃ = 0 →
    xPlus W xT yT = C xT + C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ∧
    D W (tS W xT) ^ 2 = 4 * tS W xT + C (12 * xT + W.b₂) * tS W xT ^ 2
      + 4 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 3 ∧
    D W (D W (tS W xT)) = 2 + C (12 * xT + W.b₂) * tS W xT
      + 6 * C (3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT) * tS W xT ^ 2

def TwoTorsionZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xT yT : K),
    W.toAffine.Equation xT yT → 2 * yT + W.a₁ * xT + W.a₃ = 0 →
    let e₁ : K := xT + W.b₂ / 12
    let kap : K := 3 * e₁ ^ 2 - g₂ W / 4
    let w₁ : K⟦X⟧ := (tS W xT).subst (expSer W)
    4 * e₁ ^ 3 - g₂ W * e₁ - g₃ W = 0 ∧
    (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X - Polynomial.C (g₃ W) : Polynomial K)
      = 4 * (Polynomial.X - Polynomial.C e₁) *
        (Polynomial.X ^ 2 + Polynomial.C e₁ * Polynomial.X + Polynomial.C (e₁ ^ 2 - g₂ W / 4)) ∧
    kap = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT ∧
    toL w₁ * (wpL W - HahnSeries.C e₁) = 1 ∧
    X ^ 2 ∣ w₁ ∧ coeff 2 w₁ = 1 ∧ w₁.subst (-X : K⟦X⟧) = w₁ ∧
    derivative w₁ ^ 2 = 4 * w₁ * (1 + 3 * C e₁ * w₁ + C kap * w₁ ^ 2) ∧
    derivative (derivative w₁) = 2 + 12 * C e₁ * w₁ + 6 * C kap * w₁ ^ 2 ∧
    (xPlus W xT yT).subst (expSer W) + C (W.b₂ / 12) = C e₁ + C kap * w₁ ∧
    ∀ e₂ e₃ : K, (4 * Polynomial.X ^ 3 - Polynomial.C (g₂ W) * Polynomial.X
        - Polynomial.C (g₃ W) : Polynomial K)
        = 4 * (Polynomial.X - Polynomial.C e₁) * (Polynomial.X - Polynomial.C e₂)
          * (Polynomial.X - Polynomial.C e₃) →
      kap = (e₁ - e₂) * (e₁ - e₃) ∧
      derivative w₁ ^ 2 = 4 * w₁ * (1 + C (e₁ - e₂) * w₁) * (1 + C (e₁ - e₃) * w₁)

def PlusZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP yP : K),
    W.toAffine.Equation xP yP →
    IsFlow (curveS W) (derivative (R := K)) ((xPlus W xP yP).subst (expSer W))
      ((yPlus W xP yP).subst (expSer W)) ∧
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 ∧
    dL (toL ((tS W xP).subst (expSer W)) * dL (wpL W))
      = 2 * xZ W - toL ((xPlus W xP yP).subst (expSer W))
        - toL ((xPlus W xP (W.toAffine.negY xP yP)).subst (expSer W))

end Formalism.L2.Th1.A
end
end

