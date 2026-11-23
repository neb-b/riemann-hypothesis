module

public import Formalism.SubspaceCounting.Bundle0001

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Formalism.G0

def cell (r u s c : ℕ) : Finset ℕ :=
  Finset.Ico (s * ((6 * r + 1) * u) + (c - 1) * u) (s * ((6 * r + 1) * u) + c * u)

def Marked (T : Finset ℕ) (r u s : ℕ) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 6 * r + 1 →
    (Odd c → T ∩ cell r u s c = ∅) ∧
    (Even c → ∃ x, T ∩ cell r u s c = {x} ∧ Even x)

def CondTiles (n : ℕ) (T : Finset ℕ) (r u M₀ : ℕ) : Prop :=
  ∀ s₀ < n / ((6 * r + 1) * u), ∃ j ≤ M₀, Marked T r u ((s₀ + j) % (n / ((6 * r + 1) * u)))

def CondIntervals (n : ℕ) (T : Finset ℕ) (G' N₁ : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i G').card ≤ N₁

def GoodOrbitIntervalTileCondition (n : ℕ) (T : Finset ℕ) (L₂ K r u M₀ G' N₁ : ℕ) : Prop :=
  CondA n T L₂ K ∧ CondTiles n T r u M₀ ∧ CondIntervals n T G' N₁

def binUpper (G : ℕ) (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc N G, (G.choose j : ℝ) * δ ^ j * (1 - δ) ^ (G - j)

def markedBound (δ : ℝ) (r u : ℕ) : ℝ :=
  ((1 - δ) ^ u) ^ (3 * r + 1) * (((u / 2 : ℕ) : ℝ) * δ * (1 - δ) ^ (u - 1)) ^ (3 * r)

def MarkedRun : Prop :=
  ∀ (T : Finset ℕ) (r u s : ℕ), 1 ≤ u → Marked T r u s →
    ∃ f : Fin (3 * r) → ℕ, StrictMono f ∧
      T ∩ Finset.Ico (s * ((6 * r + 1) * u)) ((s + 1) * ((6 * r + 1) * u)) =
        Finset.univ.image f ∧
      (∀ i, Even (f i)) ∧
      (∀ (i : Fin (3 * r)) (h : i.val + 1 < 3 * r), f i + u < f ⟨i.val + 1, h⟩) ∧
      (∀ i, s * ((6 * r + 1) * u) + u ≤ f i ∧ f i + u < (s + 1) * ((6 * r + 1) * u))

end Formalism.G0
