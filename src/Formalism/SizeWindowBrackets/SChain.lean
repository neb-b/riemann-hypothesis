module

public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.SizeWindowBrackets.Bundle0003
public import Formalism.SizeWindowBrackets.Bundle0004

@[expose] public section

open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr

section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
  {Top : Type} [Fintype Top] {m f : ℕ}

def SizeData₂ (Dd : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : Prop :=
  Dd.HidaSetting C ∧ Dd.DIV C ∧ EComp5 Dd C ∧ Dd.HComp C ∧ Count5 Dd C ∧ Dd.Slopes C ∧
  QuotientSlopeBoundsWith Dd C Xpp ∧ LossBounds Dd C ∧ Dd.SlopeIneq ∧ Dd.HHBound C ∧ Dd.FParams

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def Ident {W : H → Type} {Top : Type} {m f : ℕ} (Dd : Data H W Top m f) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) : Prop :=
  (∀ τ, Dd.aT τ = a (eT τ)) ∧ (∀ u0 j ρ, Dd.w u0 j ρ = w u0 j (eP ρ)) ∧
  Dd.gam = Real.eulerMascheroniConstant ∧ Dd.LpL = (ell chC).re ∧
  (∀ u0, Dd.ASK u0 = ∑ t ∈ TT, ∑ j : Fin m, ASK D N (a t) t (w u0 j))

def BNBounds {W : H → Type} {Top : Type} {m f : ℕ} (Dd : Data H W Top m f) (T2 : Finset H) : Prop :=
  Dd.B0 ≤ (2 * (Fintype.card H : ℝ)) * m * Dd.b * Dd.x ^ Dd.ε ∧
  Dd.Nc ≤ (T2.card : ℝ) * Dd.k * Dd.b * Dd.x ^ Dd.ε
    / ((Fintype.card H : ℝ) * ((Fintype.card H : ℝ) * Dd.x ^ (-Dd.ε)))

def GrowthInequalitySizes {m : ℕ} (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (N : ℕ) (x b b' η X' θ : ℝ) : Prop :=
  0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N)

def GrowthInequalityRemainingHyps (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ CL : ℝ) : Prop :=
  GrowthInequalitySizes TT T2 a w N x b b' η X' θ ∧ ThinScales D ell X' θ ∧ ValuesAtX D ell x ε CL

end

def CostWindows (x f b η θ : ℝ) : Prop :=
  2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x

def RestSize (ε x : ℝ) (n nT nT2 m : ℕ) (b k aE : ℝ) : Prop :=
  aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧
  k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε)

def XLarge (K cHH eK Cd CL ε x : ℝ) : Prop :=
  3 ≤ x ∧ 26 ≤ x ^ (3 * ε / 8) ∧ LargeX x ε K cHH eK ∧ moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε)

def SizeWindowsSplit : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ),
    SizeWindows C ε x n nT nT2 m b k aE Err ↔
      (RestSize ε x n nT nT2 m b k aE ∧ Err ≤ x ^ (C * ε) * errorBracketSizeWindows x ε n nT nT2 m b k aE ∧
        (3 ≤ x ∧ 26 ≤ x ^ (3 * ε / 8)) ∧
        (0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ nT2 ≤ n ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧ x * m ≤ k))

end Formalism.LFunctionChainParameters.LChain
