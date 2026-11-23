module

public import Mathlib
public import Formalism.PieriBlockIdeals.Bundle0001
public import Formalism.RankGapBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.ContentDistanceBounds
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

def NoResidue : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ),
    (∀ u ∈ U, u ∉ Finset.Icc b (b + t - 1) → ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)) →
    mwCount l b t κ U = 0

def PrimeCount : Prop :=
  ∀ (L : ℝ) (T : Finset ℤ) (P : Finset ℕ), 0 ≤ L → (∀ n ∈ T, n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < L ^ 2) →
    (∀ l ∈ P, l.Prime ∧ L < (l : ℝ) ∧ ∃ n ∈ T, (l : ℤ) ∣ n) → P.card ≤ T.card

def ISum : Prop :=
  ∀ (h : ℕ) (L : ℝ) (xm xp mB : ℤ) (P : Finset ℕ), 0 ≤ L → (h : ℝ) < L ^ 2 → 0 ≤ mB → mB < xm →
    xm ≤ xp → xp ≤ (h : ℤ) → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, IlInd l xm xp mB * Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ)

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.ParamsWindow
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

def lamOf (N : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U i - ((N : ℤ) - 1 - (i : ℤ))

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.WEChain
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

def WEChain : Prop :=
  ∀ (k j t q l h κ : ℕ) (K : Type) [Field K] [CharP K l]
    (U U' V V' : Fin (k + j + t + q) → ℤ) (b b' c c' : ℤ) (kc kp : Fin t → ℤ),
    l.Prime → t + 2 * κ < l →
    StrictAnti U → StrictAnti U' → StrictAnti V → StrictAnti V' →
    (∀ a, 0 ≤ U a) → (∀ a, U' a ≤ (h : ℤ)) → ∑ a, U a = ∑ a, U' a →
    (∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) →
    (∀ s : Fin t, ∃ a, V a = b' + ((s : ℕ) : ℤ)) →
    (∏ a, (X + C (((U a + c : ℤ)) : K))) = ∏ a, (X + C (((U' a + c : ℤ)) : K)) →
    (∏ a, (X + C (((V a + c' : ℤ)) : K))) = ∏ a, (X + C (((V' a + c' : ℤ)) : K)) →
    (∀ s, |kc s| ≤ (κ : ℤ)) → (∀ s, |kp s| ≤ (κ : ℤ)) →
    Multiset.map (fun s : Fin t => ((b + ((s : ℕ) : ℤ) - kc s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((U' a : ℤ) : ZMod l)) Finset.univ.val →
    Multiset.map (fun s : Fin t => ((b' + ((s : ℕ) : ℤ) - kp s : ℤ) : ZMod l)) Finset.univ.val ≤
      Multiset.map (fun a => ((V' a : ℤ) : ZMod l)) Finset.univ.val →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ) + (l : ℤ) * kp s - kc s) →
    ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), (U a - U' a) ≤
      (q : ℤ) * h +
        ((l : ℤ) * (mwCount l b' t κ (Finset.univ.image V) : ℤ) +
          (mwCount l b t κ (Finset.univ.image U) : ℤ)) * ((t : ℤ) + 2 * κ)

end Formalism.CohomologicalDescent
end
end

