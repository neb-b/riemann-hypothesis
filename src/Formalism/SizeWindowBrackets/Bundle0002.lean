module

public import Formalism.RankGapBounds.Bundle0001
public import Mathlib
public import Formalism.SizeWindowBrackets.Bundle0001

@[expose] public section

-- bundled from Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
section
open Real

namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds

open Formalism.RankGapBounds.WeightedMeanData

noncomputable section

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)

def Lo5 (u0 : U0) (u : W u0) : ℝ :=
  C.cSl1 * D.IO u0 + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * Real.log (D.T u0 u)
    + C.cSl1 * Xpp + 1

def QuotientSlopeBoundsWith : Prop :=
  ∀ u0 (u : W u0),
    D.muMaxN u0 u ≤ D.muMaxM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u + C.cSl1 * (m : ℝ) * D.B0 ∧
    D.muM u0 u + D.Ga u0 + D.Fo u0 - D.Ee u0 u - Lo5 D C Xpp u0 u ≤ D.muN u0 u

def EComp5 : Prop :=
  ∀ u0 (u : W u0), |D.Ee u0 u - (m : ℝ) * D.sumA * D.lg| ≤ C.cE * (m : ℝ) * D.B0

def Count5 : Prop :=
  ∀ u0 (u : W u0),
    ((∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
        - C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k) ≤ Real.log (D.T u0 u)) ∧
    Real.log (D.T u0 u) ≤ C.cCount * (m : ℝ) * D.L ∧
    ∀ u' : W u0, |Real.log (D.T u0 u) - Real.log (D.T u0 u')| ≤ C.cCount * Real.log D.k

def LossBounds : Prop :=
  ∀ u0, D.ASK u0 - D.Ga u0 ≤ D.LoP C ∧ D.IO u0 ≤ D.LoP C

def MLo5 : ℝ :=
  C.cSl1 * D.LoP C + C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') * (C.cCount * (m : ℝ) * D.L)
    + C.cSl1 * Xpp + 1

def UBar5 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0
    + MLo5 D C Xpp

def ErrX5at (u0 : U0) : ℝ :=
  D.sumA * (C.cCount * (D.La + (m : ℝ) ^ 2 * D.La / D.k))
    + (C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε))
    + (m : ℝ) * C.cE * D.B0
    + C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)
    + Real.log (Fintype.card (W u0) : ℝ)
    + D.LoP C
    + MLo5 D C Xpp
    + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH) * (UBar5 D C Xpp + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))

def PointwiseBoundVariant : Prop :=
  D.HidaSetting C → D.DIV C → EComp5 D C → D.HComp C → Count5 D C → D.Slopes C →
    QuotientSlopeBoundsWith D C Xpp → LossBounds D C → D.SlopeIneq → D.HHBound C → D.FParams →
    ∀ u0, D.ASK u0 ≤ D.Main u0 + ErrX5at D C Xpp u0

end

end Formalism.LFunctionChainParameters.WeightedSlopeBounds
end

-- bundled from Formalism.SizeWindowBrackets.SecondKindBucket
section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas

open Finset Classical

noncomputable section

variable {ι κ τ : Type*}

def ASK (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (dT : κ → τ → ℝ) : ℝ :=
  ∑ j ∈ J, ∑ t ∈ TT, ((∑ p ∈ Ps, 2 * Real.log p * vonMangoldtClassSum j t p) + dT j t)

def GaW (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gainW : κ → ι → ℝ) (tauW : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * ((∑ j ∈ J, gainW j w) - tauW w)

def deficit (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (gain : κ → ℕ → ℝ)
    (tau : ℕ → ℝ) (p : ℕ) : ℝ :=
  (∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p) - ((∑ j ∈ J, gain j p) - tau p)

structure UnitRule (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ) (J : Finset κ)
    (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ) : Prop where
  unit : ∀ p ∈ Ps, ∑ w ∈ W.filter (fun w => below w = p), l w = Real.log p
  onPs : ∀ w ∈ W, below w ∈ Ps → (∀ j ∈ J, gainW j w = gain j (below w)) ∧ tauW w = tau (below w)
  offPs : ∀ w ∈ W, below w ∉ Ps → (∀ j ∈ J, gainW j w = 0) ∧ tauW w = 0

def SplitEq : Prop :=
  ∀ (ι κ τ : Type) (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ) (J : Finset κ)
    (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (dT : κ → τ → ℝ) (gainW : κ → ι → ℝ) (tauW : ι → ℝ)
    (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ),
    UnitRule W below l Ps J gainW tauW gain tau →
    ASK Ps J TT vonMangoldtClassSum dT - GaW W J l gainW tauW =
      (∑ p ∈ Ps, 2 * Real.log p * deficit J TT vonMangoldtClassSum gain tau p) + ∑ j ∈ J, ∑ t ∈ TT, dT j t

inductive PClass
  | served
  | first
  | second
  | high
  deriving DecidableEq

def SizeData₂ (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ) (p : ℕ) : Prop :=
  TTp p ⊆ TT ∧
    (∑ j ∈ J, ∑ t ∈ TTp p, (vonMangoldtClassSum j t p - lo p)) - (J.card : ℝ) * fl p ≤ (∑ j ∈ J, gain j p) - tau p

def servedLoss (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (lo fl : ℕ → ℝ) (p : ℕ) : ℝ :=
  (∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p) + (J.card : ℝ) * (TTp p).card * lo p + (J.card : ℝ) * fl p

def wholeAsk (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p

def SplitClasses : Prop :=
  ∀ (ι κ τ : Type) (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ) (cl : ℕ → PClass)
    (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (dT : κ → τ → ℝ)
    (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ),
    UnitRule W below l Ps J gainW tauW gain tau →
    (∀ p ∈ Ps, cl p = PClass.served → SizeData₂ J TT TTp vonMangoldtClassSum gain tau lo fl p) →
    (∀ p ∈ Ps, cl p ≠ PClass.served → (∀ j ∈ J, gain j p = 0) ∧ tau p = 0) →
    ASK Ps J TT vonMangoldtClassSum dT - GaW W J l gainW tauW ≤
      (∑ p ∈ Ps.filter (fun p => cl p = PClass.served), 2 * Real.log p * servedLoss J TT TTp vonMangoldtClassSum lo fl p) +
      (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p) +
      (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p) +
      (∑ p ∈ Ps.filter (fun p => cl p = PClass.high), 2 * Real.log p * wholeAsk J TT vonMangoldtClassSum p) +
      ∑ j ∈ J, ∑ t ∈ TT, dT j t

def PrimeLogSum : Prop :=
  ∀ (Y : ℝ) (s : Finset ℕ), 1 ≤ Y → (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log p / p ≤ Real.log Y + Real.log 4

def ThetaFin : Prop :=
  ∀ (Y : ℝ) (s : Finset ℕ), 0 ≤ Y → (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log p ≤ Real.log 4 * Y

def TailSq : Prop :=
  ∀ (p₀ : ℕ) (s : Finset ℕ), 3 ≤ p₀ → (∀ n ∈ s, p₀ ≤ n) →
    ∑ n ∈ s, Real.log n / (n : ℝ) ^ 2 ≤
      2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1)

def askAt (I : Finset ℕ) (at_ p : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, max (at_ / p ^ i - w i) 0

def AskUpperBound : Prop :=
  ∀ (I : Finset ℕ) (at_ p : ℝ) (w : ℕ → ℝ), 2 ≤ p → 0 ≤ at_ → (∀ i ∈ I, 0 ≤ w i) →
    (∀ i ∈ I, Odd i) → askAt I at_ p w ≤ 4 / 3 * at_ / p

def TopLoss : Prop :=
  ∀ (I : Finset ℕ) (a at_ : ℝ) (p : ℕ) (w : ℕ → ℝ), 2 ≤ p → 0 ≤ at_ → at_ ≤ 3 / 2 * a →
    (∀ i ∈ I, 0 ≤ w i) → (∀ i ∈ I, Odd i) →
    2 * Real.log p * askAt I at_ p w ≤ 4 * a * Real.log p / p

def DTerm : Prop :=
  ∀ (I : Finset ℕ) (a at_ : ℝ) (d : ℕ) (w : ℕ → ℝ), 4 ≤ d → 0 ≤ at_ → at_ ≤ 3 / 2 * a →
    (∀ i ∈ I, 0 ≤ w i) → (∀ i ∈ I, 1 ≤ i) →
    Real.log d * askAt I at_ d w ≤ 2 * a * Real.log d / d

def IntervalCount : Prop :=
  ∀ (A B : ℝ) (s : Finset ℕ), A ≤ B → (∀ n ∈ s, A ≤ n ∧ (n : ℝ) ≤ B) → (s.card : ℝ) ≤ B - A + 1

def BandCount : Prop :=
  ∀ (P c : ℝ) (s : Finset ℕ), 0 ≤ P → 0 ≤ c →
    (∀ n ∈ s, P * (1 - c) ≤ n ∧ (n : ℝ) ≤ P * (1 + c)) → (s.card : ℝ) ≤ 2 * c * P + 1

def BandSum : Prop :=
  ∀ (P c p₀ : ℝ) (s : Finset ℕ), 1 ≤ P → 0 ≤ c → c ≤ 1 / 2 → 1 ≤ p₀ →
    (∀ n ∈ s, p₀ ≤ n ∧ P * (1 - c) ≤ n ∧ (n : ℝ) ≤ P * (1 + c)) →
    ∑ n ∈ s, Real.log n / n ≤ (4 * c + 1 / p₀) * Real.log (2 * P)

def BandTotal : Prop :=
  ∀ (I : ℕ) (P : ℕ → ℝ) (X' c p₀ : ℝ) (s : ℕ → Finset ℕ), 0 ≤ c → c ≤ 1 / 2 → 1 ≤ p₀ →
    (∀ i < I, 1 ≤ P i ∧ P i ≤ X') →
    (∀ i < I, ∀ n ∈ s i, p₀ ≤ n ∧ P i * (1 - c) ≤ n ∧ (n : ℝ) ≤ P i * (1 + c)) →
    ∑ i ∈ range I, ∑ n ∈ s i, Real.log n / n ≤ I * ((4 * c + 1 / p₀) * Real.log (2 * X'))

def BandRoot : Prop :=
  ∀ (X' ρ p : ℝ) (i : ℕ), 0 < X' → 0 ≤ ρ → ρ ≤ 1 → 0 ≤ p → 1 ≤ i →
    X' * (1 - ρ) ≤ p ^ i → p ^ i ≤ X' * (1 + ρ) →
    X' ^ ((1 : ℝ) / i) * (1 - ρ) ≤ p ∧ p ≤ X' ^ ((1 : ℝ) / i) * (1 + ρ)

def BandExponent : Prop :=
  ∀ (X' ρ : ℝ) (p i : ℕ), 2 ≤ X' → ρ ≤ 1 → 8 ≤ p → (p : ℝ) ^ i ≤ X' * (1 + ρ) →
    (i : ℝ) ≤ Real.log X'

def HighBucket : Prop :=
  ∀ (a at_ w'' X'' th : ℝ) (s : Finset ℕ) (I : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
    0 < w'' → 0 ≤ th → th ≤ 1 → 2 ≤ X'' → X'' * w'' = a → 0 ≤ at_ → at_ ≤ a * (1 + th) →
    (∀ p ∈ s, X'' < p) → (∀ p ∈ s, ∀ i ∈ I p, 1 ≤ i) → (∀ p ∈ s, ∀ i ∈ I p, w'' ≤ w p i) →
    ∑ p ∈ s, 2 * Real.log p * askAt (I p) at_ p (w p) ≤
      2 * Real.log (2 * X'') * (a * th ^ 2 + w'' * th)

def flF (C f N a : ℝ) (p : ℕ) : ℝ :=
  C * f * N ^ 2 * Real.logb p a + C * f * Real.logb p a ^ 2

def cpF (C Sk a : ℝ) (p : ℕ) : ℝ := C * Sk * Real.logb p (2 * a)

def prF (p₀ : ℕ) (Q₁ Q₂ : ℝ) (p : ℕ) : ℝ := if p < p₀ then Q₁ else Q₂

def orF (C lx La a k : ℝ) (L₁ : ℕ → ℝ) (p₀ p : ℕ) : ℝ :=
  C * lx * (La * a / (p * k) + (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2))

def FloorBucket : Prop :=
  ∀ (C f N a X'' : ℝ) (s : Finset ℕ), 0 ≤ C → 0 ≤ f → 1 ≤ a → (∀ p ∈ s, 2 ≤ p) →
    (s.card : ℝ) ≤ X'' →
    ∑ p ∈ s, 2 * Real.log p * flF C f N a p ≤
      2 * C * f * X'' * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2)

def CpBucket : Prop :=
  ∀ (C Sk a mT X'' : ℝ) (s : Finset ℕ), 0 ≤ C → 0 ≤ Sk → 1 / 2 ≤ a → 0 ≤ mT →
    (∀ p ∈ s, 2 ≤ p) → (s.card : ℝ) ≤ X'' →
    ∑ p ∈ s, 2 * Real.log p * (mT * cpF C Sk a p) ≤ 2 * C * Sk * Real.log (2 * a) * mT * X''

def PrBucket : Prop :=
  ∀ (p₀ : ℕ) (X' Q₁ Q₂ : ℝ) (s : Finset ℕ), 0 ≤ X' → 0 ≤ Q₁ → 0 ≤ Q₂ →
    (∀ p ∈ s, p.Prime ∧ (p : ℝ) < X') →
    ∑ p ∈ s, 2 * Real.log p * prF p₀ Q₁ Q₂ p ≤ 2 * Real.log 4 * (p₀ * Q₁ + X' * Q₂)

def OrBucket : Prop :=
  ∀ (C lx La a k K₀ X' : ℝ) (L₁ : ℕ → ℝ) (p₀ : ℕ) (s : Finset ℕ), 0 ≤ C → 0 ≤ lx → 0 ≤ La → 0 ≤ a →
    0 < k → 0 < K₀ → 1 ≤ X' → 3 ≤ p₀ →
    (∀ p ∈ s, p.Prime ∧ (p : ℝ) < X') → (∀ p ∈ s, p < p₀ → K₀ ≤ (p : ℝ) ^ (L₁ p - 1)) →
    ∑ p ∈ s, 2 * Real.log p * orF C lx La a k L₁ p₀ p ≤
      2 * C * lx * a * ((La / k + 1 / K₀) * (Real.log X' + Real.log 4) +
        2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1))

def OrdersBucket : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y mTa : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y → 0 ≤ mTa →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧
      ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e l hl) ≤ J) →
    ∑ l ∈ s, 4 * mTa * (Real.log l / l) ≤ 4 * mTa * (C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e)

def FirstKindBucket : Prop :=
  ∃ C : ℝ, ∀ (e J I : ℕ) (Y X' c p₀ : ℝ) (P : ℕ → ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    0 ≤ c → c ≤ 1 / 2 → 1 ≤ p₀ → (∀ i < I, 1 ≤ P i ∧ P i ≤ X') →
    (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
      (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
        ∃ i < I, p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c))) →
    ∑ p ∈ s, Real.log p / p ≤
      C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e + I * ((4 * c + 1 / p₀) * Real.log (2 * X'))

def loF (C Sk a X' Q₁ Q₂ lx La k : ℝ) (L₁ : ℕ → ℝ) (p₀ p : ℕ) : ℝ :=
  cpF C Sk a p + (if (p : ℝ) < X' then prF p₀ Q₁ Q₂ p + orF C lx La a k L₁ p₀ p else 0)

def SecondKindLoss : Prop :=
  ∀ (ι κ τ : Type) (W : Finset ι) (below : ι → ℕ) (l : ι → ℝ) (Ps : Finset ℕ) (cl : ℕ → PClass)
    (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (Iex : κ → τ → ℕ → Finset ℕ) (at_ : τ → ℝ) (wz : κ → τ → ℕ → ℕ → ℝ)
    (Id : κ → τ → Finset ℕ) (wd : κ → τ → ℕ → ℝ) (d : ℕ)
    (gainW : κ → ι → ℝ) (tauW : ι → ℝ) (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ)
    (a th w'' X'' X' C f N Sk Q₁ Q₂ lx La k K₀ : ℝ) (L₁ : ℕ → ℝ) (p₀ : ℕ),
    UnitRule W below l Ps J gainW tauW gain tau → (∀ p ∈ Ps, p.Prime) →
    0 < w'' → 0 ≤ th → th ≤ 1 / 2 → 2 ≤ X'' → X'' * w'' = a → 1 ≤ a → 1 ≤ X' → 3 ≤ p₀ → 4 ≤ d →
    0 ≤ C → 0 ≤ f → 0 ≤ Sk → 0 ≤ Q₁ → 0 ≤ Q₂ → 0 ≤ lx → 0 ≤ La → 0 < k → 0 < K₀ →
    (∀ t ∈ TT, 0 ≤ at_ t ∧ at_ t ≤ a * (1 + th)) →
    (∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps, ∀ i ∈ Iex j t p, Odd i ∧ w'' ≤ wz j t p i) →
    (∀ j ∈ J, ∀ t ∈ TT, ∀ i ∈ Id j t, 1 ≤ i ∧ 0 ≤ wd j t i) →
    (∀ p ∈ Ps, cl p = PClass.served → (p : ℝ) ≤ X'') → (∀ p ∈ Ps, cl p = PClass.high → X'' < p) →
    (∀ p ∈ Ps, cl p = PClass.served →
      SizeData₂ J TT TTp (fun j t p => askAt (Iex j t p) (at_ t) p (wz j t p)) gain tau lo fl p) →
    (∀ p ∈ Ps, cl p ≠ PClass.served → (∀ j ∈ J, gain j p = 0) ∧ tau p = 0) →
    (∀ p ∈ Ps, cl p = PClass.served → fl p ≤ flF C f N a p) →
    (∀ p ∈ Ps, cl p = PClass.served → lo p ≤ loF C Sk a X' Q₁ Q₂ lx La k L₁ p₀ p) →
    (∀ p ∈ Ps, p < p₀ → K₀ ≤ (p : ℝ) ^ (L₁ p - 1)) →
    ASK Ps J TT (fun j t p => askAt (Iex j t p) (at_ t) p (wz j t p))
        (fun j t => Real.log d * askAt (Id j t) (at_ t) d (wd j t)) - GaW W J l gainW tauW ≤
      (J.card : ℝ) * (2 * C * f * X'' * (N ^ 2 * Real.log a + 2 * Real.log a ^ 2)) +
      2 * C * Sk * Real.log (2 * a) * ((J.card : ℝ) * TT.card) * X'' +
      (J.card : ℝ) * TT.card * (2 * Real.log 4 * (p₀ * Q₁ + X' * Q₂)) +
      (J.card : ℝ) * TT.card * (2 * C * lx * a * ((La / k + 1 / K₀) * (Real.log X' + Real.log 4) +
        2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1))) +
      (∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        4 * (J.card : ℝ) * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ)) +
      4 * (J.card : ℝ) * TT.card * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) +
      4 * (J.card : ℝ) * TT.card * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) +
      (J.card : ℝ) * TT.card * (2 * Real.log (2 * X'') * (a * th ^ 2 + w'' * th)) +
      (J.card : ℝ) * TT.card * (2 * a * Real.log d / d)

end

end Formalism.LFunctionChainParameters.DeficitSplitLemmas
end

-- bundled from Formalism.SizeWindowBrackets.SlopeExcessBoundExponentZero
section
open Real

namespace Formalism.LFunctionChainParameters.PhiMonotonicityLemmas

noncomputable section

def phi (H u : ℝ) : ℝ := u * Real.log (1 + H / u)

def ErrF (del u HH η e : ℝ) : ℝ :=
  (1 - del)⁻¹ * (4 * phi HH u + (η + 4 * Real.sqrt e) * HH)

def ConclF (s mu logI del u HH η e : ℝ) : Prop :=
  s - logI - ErrF del u HH η e ≤ mu


section SizeData₂

open Formalism.RankGapBounds.WeightedMeanData

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

end SizeData₂

end

end Formalism.LFunctionChainParameters.PhiMonotonicityLemmas
end

