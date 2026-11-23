module

public import Mathlib
public import Formalism.LogVandermondeBounds.Bundle0001
public import Formalism.LandauZeroFreeBounds.Statement

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.ConcavityEquidistribution
section
namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)

noncomputable def mean {σ : Type} [Fintype σ] (F : σ → ℝ) : ℝ := (∑ s, F s) / (Fintype.card σ : ℝ)

noncomputable def weylDim {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ univ.filter (fun j => i < j),
    (((lam i - lam j + (j : ℤ) - (i : ℤ) : ℤ) : ℝ) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)))

def Wnum {n : ℕ} (lam : Fin (n + 1) → ℤ) : ℤ := lam 0 - lam (Fin.last n) + n + 1

def degZ {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) : ℤ := ∑ i, lam i - ∑ i, nu i

noncomputable def MeanSquareTwistBound {n : ℕ} (lam : Fin (n + 1) → ℤ) (nu : Fin n → ℤ) (logT : ℝ) : ℝ :=
  -(degZ lam nu : ℝ) * logT
    + 2 * (n : ℝ) * Real.log (Wnum lam : ℝ) * (∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ))
    + Real.log (weylDim lam)

def wt {k : ℕ} (lam : Fin k → ℤ) : ℤ := ∑ i, lam i

def plus {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : Fin (κ + 1) → ℤ := fun i => lam i - lam (Fin.last κ)

noncomputable def MeanSquareWeightBound {κ : ℕ} (lam : Fin (κ + 1) → ℤ) : ℝ :=
  (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1)
    + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1)

structure Numbers (C₀ a b' L v logT logg eta S : ℝ) (k m t N : ℕ) : Prop where
  one_le_L : 1 ≤ L
  one_le_v : 1 ≤ v
  log_av : Real.log (a * v) ≤ L
  one_le_b' : 1 ≤ b'
  b'_le_a : b' ≤ a
  logT_nonneg : 0 ≤ logT
  logT_le : logT ≤ C₀ * m * L
  logg_nonneg : 0 ≤ logg
  logg_le : logg ≤ C₀ * L
  one_le_k : 1 ≤ k
  one_le_m : 1 ≤ m
  N_eq : N = k + m * (t + 1)
  eta_nonneg : 0 ≤ eta
  S_nonneg : 0 ≤ S
  small : S + eta + (m : ℝ) * t ≤ b'
  sq : (N : ℝ) ^ 2 * (L + logT) ≤ N * b'
  lin : (N : ℝ) * L + logT ≤ b'
  pow : (1 + 2 * C₀) * (m : ℝ) ^ 3 * N ≤ b'

def ZetaBoundApplication : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (TT : Finset ι) (n : ℕ)
    (lam : ι → Fin (n + 1) → ℤ) (sg : ι → Fin n → ℤ) (A bt : ι → ℝ)
    (b' L logT eta S mt logP : ℝ),
    1 ≤ L → 0 ≤ logT → 0 ≤ b' → 0 ≤ eta → 0 ≤ S → 0 ≤ mt →
    (∀ ρ, Interlace (lam ρ) (sg ρ)) → (∀ ρ, Real.log (Wnum (lam ρ) : ℝ) ≤ C₀ * L) →
    (∀ ρ ∈ TT, bt ρ ≤ 2 * b') →
    (∀ ρ ∈ TT, (B0 (lam ρ) (sg ρ) : ℝ) ≤ bt ρ + eta + S) →
    (∀ ρ, ρ ∉ TT → (B0 (lam ρ) (sg ρ) : ℝ) ≤ eta + S) →
    (∀ ρ, ∃ X : Finset (Fin n), X.card ≤ 3 ∧ ((∑ i ∈ Xᶜ, len (lam ρ) i : ℤ) : ℝ) ≤ eta + S) →
    (∀ ρ ∈ TT, A ρ - bt ρ - C₀ * (S + eta + mt) ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    (∀ ρ, ρ ∉ TT → -(S + eta) - C₀ * mt ≤ (degZ (lam ρ) (sg ρ) : ℝ)) →
    logP ≤ ∑ ρ, MeanSquareTwistBound (lam ρ) (sg ρ) logT →
    logP ≤ -(∑ ρ ∈ TT, A ρ) * logT + C * TT.card * b' * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * (eta + 3 * S + mt) * (logT + ((n : ℝ) + 1) * L)
        + C * Fintype.card ι * ((n : ℝ) + 1) ^ 2 * L

def LastColumnBound : Prop :=
  ∀ (κ : ℕ) (lam : Fin (κ + 1 + 1) → ℤ) (A bt S : ℤ), 0 ≤ bt → 0 ≤ S →
    lam 0 = A → lam (Fin.last (κ + 1)) = -bt →
    (∀ i, i ≠ 0 → i ≠ Fin.last (κ + 1) → 0 ≤ lam i ∧ lam i ≤ S) →
    wt lam ≤ A + (κ + 2) * S ∧ wt (plus lam) ≤ A + (κ + 2) * (bt + S)

def PropZ_ii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muM : ℝ) (muV : X → ℝ) (muDelta muNabla muMaxNabla : ι → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (lam τ) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * S) →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → (wt (lam ρ) : ℝ) ≤ C₀ * ((κ : ℝ) + 1) * S) →
    muM = mean muV →
    (∀ c, muV c = -(∑ ρ, (wt (lam ρ) : ℝ) / ((κ : ℝ) + 1) * logT) + ∑ ρ, muDelta ρ) →
    (∀ ρ, muDelta ρ = -muNabla ρ) → (∀ ρ, muNabla ρ ≤ muMaxNabla ρ) →
    (∀ ρ, muMaxNabla ρ ≤ MeanSquareWeightBound (lam ρ)) →
    -(∑ τ ∈ TT, A τ / ((κ : ℝ) + 1) * logT) - C * TT.card * a * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * ((κ : ℝ) + 1) * (b' + S) * Real.log ((κ : ℝ) + 1)
        - C * Fintype.card ι * S * logT - C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L ≤ muM

def PropZ_iii : Prop :=
  ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ (ι X : Type) [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X]
    (TT : Finset ι) (κ m t N : ℕ) (lam : ι → Fin (κ + 1) → ℤ) (A bt : ι → ℝ)
    (a b' L v logT logg eta S muMaxM : ℝ) (muMaxV : X → ℝ),
    Numbers C₀ a b' L v logT logg eta S (κ + 1) m t N →
    (∀ ρ, Antitone (lam ρ)) →
    (∀ τ ∈ TT, a ≤ A τ ∧ A τ ≤ 2 * a ∧ b' ≤ bt τ ∧ bt τ ≤ 2 * b') →
    (∀ τ ∈ TT, (wt (plus (lam τ)) : ℝ) ≤ A τ + ((κ : ℝ) + 1) * (bt τ + S)) →
    (∀ τ ∈ TT, |(lam τ (Fin.last κ) : ℝ)| ≤ bt τ) →
    (∀ ρ, ρ ∉ TT → (wt (plus (lam ρ)) : ℝ) ≤ ((κ : ℝ) + 1 + 3) * S) →
    (∀ ρ, ρ ∉ TT → |(lam ρ (Fin.last κ) : ℝ)| ≤ C₀ * S) →
    (∃ c, muMaxM ≤ muMaxV c) →
    (∀ c, muMaxV c ≤ ∑ ρ, ((wt (plus (lam ρ)) : ℝ) * (C₀ * Real.log (((κ : ℝ) + 1) * v))
        + ((κ : ℝ) + 1) ^ 2 * Real.log ((plus (lam ρ) 0 : ℝ) + (κ : ℝ) + 1)
        + |(lam ρ (Fin.last κ) : ℝ)| * logT)) →
    muMaxM ≤ C * TT.card * a * Real.log (((κ : ℝ) + 1) * v)
        + C * Fintype.card ι * (b' + S) * (((κ : ℝ) + 1) * Real.log (((κ : ℝ) + 1) * v) + logT)
        + C * Fintype.card ι * ((κ : ℝ) + 1) ^ 2 * L

end Formalism.HermitianLattices.TraceIntegrality
end

-- bundled from Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
section
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2PrimeSums

def psum (a : ℕ → ℂ) (u : ℝ) : ℂ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def psumR (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊u⌋₊, a n

def Gchi (a : ℕ → ℂ) (S : ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * ((y / (n : ℝ) - 1 : ℝ) : ℂ) - (y : ℂ) * S

def Gone (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊y⌋₊, a n * (y / (n : ℝ) - 1) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def SmoothedRemainderIntegralFormula : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℂ,
      Tendsto (fun U : ℝ => ∫ u in y..U, psum a u / (u : ℂ) ^ 2) atTop (𝓝 I) ∧
      Gchi a S y = -(y : ℂ) * I

def SmoothedRemainderRealIntegralFormula : Prop :=
  ∀ a : ℕ → ℝ,
    Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR a u - u) / u ^ 2) atTop
      (𝓝 (-1 - Real.eulerMascheroniConstant)) →
    ∀ y : ℝ, 1 ≤ y → ∃ I : ℝ,
      Tendsto (fun U : ℝ => ∫ u in y..U, (psumR a u - u) / u ^ 2) atTop (𝓝 I) ∧
      Gone a y = -y * I

def SmoothedRemainderScaledDiffBound : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), (∀ y : ℝ, 0 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, ‖a n‖ ≤ 2 * y) →
    ∀ A w₁ w₂ : ℝ, 0 < A → 0 < w₁ → w₁ ≤ w₂ →
      ‖(w₂ : ℂ) * Gchi a S (A / w₂) - (w₁ : ℂ) * Gchi a S (A / w₁)‖ ≤ 3 * A * Real.log (w₂ / w₁)

def GoodFor (Q : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → ¬ Formalism.ZeroFreeDirichlet.IsLZero χ s

def ZeroPairs (σ Q : ℝ) : Set ((Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ) :=
  {p | ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧ σ < p.2.re ∧ |p.2.im| ≤ Q ∧
    Formalism.ZeroFreeDirichlet.IsLZero p.1.2 p.2}

def ZeroDensityBound (σ Q : ℝ) : Prop :=
  (((ZeroPairs σ Q).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (10 ^ 88 * (10 ^ 421 * Q ^ 99) ^ (1 - σ))

def BadChars (Q : ℝ) : Set (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) :=
  {c | ((c.1 + 1 : ℕ) : ℝ) ≤ Q ∧ c.2.IsPrimitive ∧ c.2 ^ 2 = 1 ∧ ¬ GoodFor Q c.2}

def ExceptionalCharacterCountBound : Prop :=
  (∀ Q : ℝ, 3 ≤ Q → ZeroDensityBound (1 - 1 / 400) Q) →
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q →
      (((BadChars Q).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (C * Q ^ ((1 : ℝ) / 4))

def TailSumBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ C₁ c₁ CM : ℝ, 0 < C₁ → 0 < c₁ → 0 ≤ CM →
    ∃ x₀ C : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ Q : ℝ, 0 < Q → x ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ x ^ (ε / 4) →
      ∀ (a : ℕ → ℂ) (S : ℂ),
        Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S) →
        (∀ y : ℝ, 1 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, ‖a n‖ / (n : ℝ) ≤ Real.log y + CM) →
        (∀ u : ℝ, 2 ≤ u → ‖psum a u‖ ≤
          C₁ * (u ^ (1 - (1 : ℝ) / 400) * Real.log (u * Q) ^ 2 + u / Q * Real.log (u * Q) ^ 2)) →
        (∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u →
          ‖psum a u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u))) →
        ‖(x : ℂ) * (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))‖ ≤ x ^ ε ∧
        ‖S‖ ≤ C * Real.log x

def Li (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

def Emain (θ : ℤ) (β X : ℝ) : ℝ := Li X - θ * Li (X ^ β)

def rhoErr (C c B X : ℝ) : ℝ :=
  C * Real.exp (-c * Real.log X / Real.log B) + C * Real.exp (-c * Real.sqrt (Real.log X))

def ShortIntervalLowerBound : Prop :=
  ∀ C₀ Cr cr cb : ℝ, 0 < C₀ → 0 < Cr → 0 < cr → 0 < cb →
    ∃ C₀' c : ℝ, C₀ ≤ C₀' ∧ 0 < c ∧
      ∀ (B G β : ℝ) (θ : ℤ) (π₁ π₂ : ℝ → ℕ),
        4 ≤ B → 1 ≤ G → G ≤ B → θ ∈ ({-1, 0, 1} : Set ℤ) →
        (θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β) →
        (∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y) →
        (∀ Y : ℝ, B ^ C₀ ≤ Y →
          |G * ((π₁ Y : ℝ) + π₂ Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y) →
        ∀ X : ℝ, B ^ C₀' ≤ X →
          c * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X ∧
          ∀ h : ℝ, h ≤ 1 → rhoErr Cr cr B X ≤ h / 100 → B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3) →
            c * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X

def PrimesAPInterval (C₀ Cr cr c : ℝ) : Prop :=
  ∀ (m a : ℕ), 3 ≤ m → Nat.Coprime a m → ∀ Y h : ℝ, (4 * (m : ℝ)) ^ C₀ ≤ Y → h ≤ 1 →
    rhoErr Cr cr (4 * m) Y ≤ h / 100 → (4 * (m : ℝ)) ^ (7 : ℝ) ≤ h * Y ^ ((1 : ℝ) / 3) →
    c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])).card : ℝ)

def PP (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Ioc ⌊Real.sqrt X⌋₊ ⌊X⌋₊).filter (fun q => q.Prime ∧ q ≡ a₀ [MOD m₀])

end Formalism.HermitianLattices.GL2PrimeSums
end
end

