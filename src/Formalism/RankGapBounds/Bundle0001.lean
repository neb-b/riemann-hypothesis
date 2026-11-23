module

public import Mathlib

@[expose] public section

-- bundled from Formalism.RankGapBounds.CloudMinFalse
section
namespace Formalism.RankGapBounds.JumpSetsAlt

open Finset

def maxVal (l n : ℕ) : ℕ := (Finset.range (n + 1)).sup fun i => (Nat.choose n i).factorization l

def posPairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

def eExp {N : ℕ} (U : Fin N → ℤ) (l : ℕ) : ℕ :=
  ∑ p ∈ posPairs N, maxVal l (U p.1 - U p.2 - 1).toNat

end Formalism.RankGapBounds.JumpSetsAlt
end

-- bundled from Formalism.RankGapBounds.LargePrimeFactor
section
open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

noncomputable section

def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime

structure Data (ι : Type) where

  T2 : Finset ι

  Nr : ℕ
  k : ℕ
  t : ℕ
  m : ℕ
  h : ℕ
  S : ℕ
  eta' : ℕ
  Wthin : ℕ
  D0 : ℕ
  lJ : ℝ
  Kexc : ℝ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  Exc : Finset ℕ
  Bad : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  erest : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ

namespace Data

end Data

def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)

end

end Formalism.RankGapBounds.ChebyshevFactorialBounds
end

-- bundled from Formalism.RankGapBounds.MeanBoundSecondForm
section
open Real

namespace Formalism.RankGapBounds.WeightedMeanData

noncomputable section

def ph (y : ℝ) : ℝ := y * Real.log y - y

def wmean {ι : Type} [Fintype ι] (d X : ι → ℝ) : ℝ := (∑ i, d i * X i) / (∑ i, d i)

structure Consts where

  cDiv : ℝ

  eDiv : ℝ

  cE : ℝ

  cH : ℝ

  cCount : ℝ

  cSlope : ℝ

  cSl1 : ℝ

  cLoss : ℝ

  eLoss : ℝ

  cHH : ℝ

structure Data (U0 : Type) (W : U0 → Type) (Top : Type) (m f : ℕ) where
  x : ℝ
  ε : ℝ
  a : ℝ
  b : ℝ
  b' : ℝ
  k : ℝ
  L : ℝ
  La : ℝ
  B0 : ℝ
  Nc : ℝ
  gam : ℝ
  LpL : ℝ
  v : ℝ
  lg : ℝ
  logGam : ℝ
  aT : Top → ℝ
  w : U0 → Fin m → Fin f → ℝ
  d : (u0 : U0) → W u0 → ℝ
  T : (u0 : U0) → W u0 → ℝ
  muN : (u0 : U0) → W u0 → ℝ
  muMaxN : (u0 : U0) → W u0 → ℝ
  h : (u0 : U0) → W u0 → ℝ
  muM : (u0 : U0) → W u0 → ℝ
  muMaxM : (u0 : U0) → W u0 → ℝ
  EeJ : (u0 : U0) → W u0 → Fin m → ℝ
  muCC : U0 → ℝ
  muMinCC : U0 → ℝ
  Fo : U0 → ℝ
  Ga : U0 → ℝ
  Ta : U0 → ℝ
  ASK : U0 → ℝ
  IO : U0 → ℝ
  HH : U0 → ℝ
  del : U0 → ℝ
  η : U0 → ℝ
  e : U0 → ℝ
  delBar : ℝ
  etaBar : ℝ
  eBar : ℝ

namespace Data

variable {U0 : Type} [Fintype U0] [Nonempty U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

def nT (_ : Data U0 W Top m f) : ℝ := (Fintype.card Top : ℝ)

def sumA : ℝ := ∑ t, D.aT t

def logOm : ℝ := D.gam + Real.log (π / D.v) - D.LpL

def Ee (u0 : U0) (u : W u0) : ℝ := ∑ j, D.EeJ u0 u j

def s (u0 : U0) : ℝ := wmean (D.d u0) (fun u => D.muN u0 u - D.h u0 u)

def uF (u0 : U0) : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u)) - D.s u0

def Tterm (u0 : U0) (u : W u0) : ℝ :=
  (4 * (f : ℝ) / D.T u0 u) *
    (|D.Ga u0| + D.Ta u0 + D.muMaxM u0 u - D.muM u0 u + 2 * (f : ℝ) * Real.log (D.T u0 u))

def LoP : ℝ := C.cLoss * D.nT * (m : ℝ) * D.b * D.x ^ (C.eLoss * D.ε)

def Main (u0 : U0) : ℝ :=
  ∑ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
    - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))

def HidaSetting : Prop :=
  0 < D.x ∧ 0 < D.b ∧ 0 ≤ D.a ∧ 0 ≤ D.b' ∧ 0 < D.k ∧ 0 < D.v ∧ 0 < f ∧
  (∀ t, 0 ≤ D.aT t) ∧ (∀ u0 j ρ, 0 < D.w u0 j ρ) ∧
  (∀ u0 (u : W u0), 0 < D.d u0 u) ∧ (∀ u0 (u : W u0), 0 < D.T u0 u) ∧
  (∀ u0 (u : W u0), D.muN u0 u ≤ D.muMaxN u0 u) ∧
  0 ≤ C.cSl1 ∧ D.delBar < 1 ∧ 0 ≤ D.etaBar ∧ 0 ≤ D.eBar ∧ D.eBar ≤ 1 / 4

def DIV : Prop :=
  ∀ u0 (u : W u0), D.muCC u0 + D.h u0 u - D.Fo u0 ≤
    (∑ t, ((m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm) - D.aT t * Real.log (D.T u0 u)))
      + C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)

def HComp : Prop :=
  ∀ u0 (u u' : W u0),
    |(D.h u0 u + ∑ t, D.aT t * Real.log (D.T u0 u)) - (D.h u0 u' + ∑ t, D.aT t * Real.log (D.T u0 u'))|
      ≤ C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)

def Slopes : Prop :=
  ∀ u0 (u : W u0), -(C.cSlope * D.nT * D.a * D.La * (1 + (m : ℝ) / D.k)) ≤ D.muM u0 u ∧
    D.muMaxM u0 u ≤ C.cSlope * D.nT * D.a * D.La

def SlopeIneq : Prop :=
  ∀ u0, 0 ≤ D.del u0 → D.del u0 < 1 → 0 ≤ D.η u0 → 0 ≤ D.e u0 → D.e u0 ≤ 1 / 4 →
    D.s u0 - D.muMinCC u0 ≤ D.HH u0 → 0 < D.HH u0 →
    D.s u0 - Real.log (Fintype.card (W u0) : ℝ)
      - (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) ≤ D.muCC u0

def HHBound : Prop :=
  ∀ u0, D.s u0 - D.muMinCC u0 ≤ D.HH u0 ∧ 0 < D.HH u0 ∧ D.HH u0 ≤ D.x ^ C.cHH * D.b

def FParams : Prop :=
  ∀ u0, 0 ≤ D.del u0 ∧ D.del u0 ≤ D.delBar ∧ 0 ≤ D.η u0 ∧ D.η u0 ≤ D.etaBar ∧
    0 ≤ D.e u0 ∧ D.e u0 ≤ D.eBar

def Vvar : ℝ :=
  2 * (m : ℝ) * C.cE * D.B0 + C.cH * (D.nT * D.a * D.La + (m : ℝ) * D.B0)
    + D.sumA * (C.cCount * Real.log D.k)

end Data

end

end Formalism.RankGapBounds.WeightedMeanData
end

-- bundled from Formalism.RankGapBounds.RandomSubsetCounterexample
section
namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

abbrev Hgrp (e : ℕ) := (ZMod (4 * 2 ^ e))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * 2 ^ e))ˣ)

def hOf (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Hgrp e :=
  QuotientGroup.mk (ZMod.unitOfCoprime l hl)

def OrdersIff : Prop :=
  ∀ (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), j ≤ e →
    ((hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))

def OrdersBound : Prop :=
  ∀ (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), 1 ≤ J → 1 < l →
    orderOf (hOf e l hl) ≤ J → (4 * 2 ^ e : ℝ) / J - 1 ≤ l

def OrdersSumY : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧
      ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e

end Formalism.RankGapBounds.LocalQuadraticParts
end

