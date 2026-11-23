module

public import Mathlib
public import Formalism.QuotientMetricDivisors.RatHermLcvTwist
public import Formalism.QuotientMetricDivisors.Bundle0002

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.EigenRatHermLcv
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def extSpan {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω) (Z : Submodule K (Fin n → K)) :
    Submodule Ω (Fin n → Ω) :=
  Submodule.span Ω ((fun z i => j (z i)) '' (Z : Set (Fin n → K)))

def IsAdjStable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (𝒯 : Set (Matrix (Fin n) (Fin n) K)) : Prop :=
  ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, ∀ x y : Fin n → K, hform H (T.mulVec x) y = hform H x (T'.mulVec y)

def IsCommStable {K : Type} [Field K] {n : ℕ} (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (Z : Submodule K (Fin n → K)) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → ∀ z ∈ Z, B.mulVec z ∈ Z

def CommTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ Z : Submodule K (Fin n → K), IsCommStable 𝒯 Z →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.StatementE
section
open Finset

noncomputable section

namespace Formalism.DivisionValues

def AbsorbE : Prop :=
  ∀ (J Pl : Type) [Fintype J] [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)]
    (x eps L b a rd La B0 Nc xe m f k N S t η w'' b' dC lam0 C0 Lpass Eb e6 eP logOm kk : ℝ)
    (eK pq : J → ℝ) (w eE δ : J → Pl → ℝ),

    1 ≤ x → 0 < eps → L = x ^ eps → b = Real.exp L → a = x * b →

    1 ≤ rd → Real.log rd ≤ L → Real.log x ≤ L → La = Real.log (a * rd) →

    B0 = f * m * b * x ^ eps → 0 ≤ Nc → x ^ eps ≤ xe →

    (Fintype.card J : ℝ) = m → (Fintype.card Pl : ℝ) ≤ f → 1 ≤ m → 1 ≤ f →

    1 ≤ k → 1 ≤ N → 0 ≤ S → 0 ≤ t → 0 ≤ η → 1 ≤ dC →

    (∀ j ρ, 0 ≤ w j ρ ∧ w j ρ ≤ 2 * b) →

    (∀ j, |pq j - kk| ≤ m) → |logOm| ≤ La →

    lam0 ≤ b → N ^ 2 * dC ≤ b → m ^ 3 * N ^ 2 * L ≤ b → m * η * N * L ≤ b → k * N ≤ b →
    k * S ≤ w'' → m * (t + 1) * η ≤ w'' → N * w'' ≤ b → b' * N ≤ a → m * k * b' ≤ a →

    0 ≤ C0 →
    Lpass ≤ 1 + C0 * lam0 →
    Eb ≤ C0 * m * xe * (B0 + Nc) →
    (∀ j, eK j ≤ C0 * (f * N ^ 2 * (La + dC) + f * m ^ 3 * N ^ 2 * L)) →
    e6 ≤ C0 * m * f * N ^ 2 * La →
    eP ≤ C0 * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La →
    (∀ j ρ, eE j ρ ≤ C0 * (w j ρ + S + N ^ 2 + m * (t + 1) * η) * La) →
    (∀ j ρ, |δ j ρ| ≤
      C0 * (w j ρ + k * (N + S) + m * (t + 1) * η + (if ρ ∈ TT then k * b' else 0))) →
      (Lpass + Eb + (∑ j, eK j) + e6 + eP + (∑ j, ∑ ρ, eE j ρ)) +
        (∑ j, ∑ ρ, |pq j - kk| * |w j ρ| * |logOm|) + (∑ j, ∑ ρ, |δ j ρ| * |logOm|) ≤
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * xe)

end Formalism.DivisionValues
end
end

