module

public import Mathlib
public import Formalism.SubspaceCounting.GoodOrbitIntervalTileCondition
public import Formalism.GrowthSums.StatementA

@[expose] public section

-- bundled from Formalism.GrowthSums.StatementB
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

open Formalism.G0

def SegmentBound : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ) (hr : 1 ≤ r), 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ (s s' : ℕ) (f f' : Fin (3 * r) → ℕ),
      s < n / ((6 * r + 1) * u) → s' < n / ((6 * r + 1) * u) →
      Marked T r u s → Marked T r u s' →
      (∀ j, 0 < j →
        j < (if s < s' then s' - s else s' + n / ((6 * r + 1) * u) - s) →
        ¬ Marked T r u ((s + j) % (n / ((6 * r + 1) * u)))) →
      StrictMono f → T ∩ Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) = univ.image f →
      StrictMono f' → T ∩ Ico (s' * ((6 * r + 1) * u)) ((s' + 1) * ((6 * r + 1) * u)) = univ.image f' →
      let a := f ⟨r, by omega⟩
      let b := f' ⟨2 * r - 1, by omega⟩
      let D := if s < s' then b - a else b + n - a
      D < G' ∧ (a + D) % n = b ∧
        (T ∩ (range (D + 1)).image (fun j => (a + j) % n)).card ≤ N₁

def NextEvenTop : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    ∀ i < n, ∃ D ∈ Icc 1 G', (i + D) % n ∈ T ∧ Even ((i + D) % n)

def TopCount : Prop :=
  ∀ (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ), 1 ≤ r → 1 ≤ u →
    (M₀ + 1) * ((6 * r + 1) * u) ≤ n → (M₀ + 5) * ((6 * r + 1) * u) ≤ G' →
    T ⊆ range n → GoodOrbitIntervalTileCondition n T L₂ K r u M₀ G' N₁ →
    n ≤ T.card * G' ∧ T.card * G' ≤ N₁ * (n + G')

end Formalism.GrowthSums
end
end

-- bundled from Formalism.GrowthSums.StatementC
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def LogCoefVal : Prop :=
  ∀ p t s : ℕ, p.Prime → 5 ≤ p → 1 ≤ s →
    ((s : ℝ) + 1) / 4 ≤
      (padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) / s) : ℝ)
        - 1 / ((p : ℝ) - 1)

end Formalism.GrowthSums
end
end

-- bundled from Formalism.GrowthSums.StatementG
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def CappedGainSubLE : Prop :=
  ∀ (n : ℕ) (p : ℝ) (TT TTodd : Finset (ZMod n)) (al cap : ZMod n → ℝ) (de v i₀ : ℝ)
    (i : ZMod n → ℕ → ℝ) (E : Finset ℕ),
    1 < p → TTodd ⊆ TT → (∀ s, 0 ≤ al s) → (∀ s, 0 ≤ cap s) →
    (∀ s e, 0 ≤ i s e) → (∀ s e, e ∉ E → i s e = 0) →
    gamP p * ∑ s ∈ TT, al s - i₀ - ∑ s ∈ TT, ∑ e ∈ E, i s e - de ≤ v →
    i₀ + ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e ≤ ∑ s ∈ TT \ TTodd, al s →
    (∀ s ∈ TTodd, ∀ e, i s e ≤ min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) →
    gainG p TT TTodd al cap de - ∑ s ∈ TT \ TTodd, al s ≤ v

end Formalism.GrowthSums
end
end

