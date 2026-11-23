module

public import Formalism.LogVandermondeBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.LogVandermondeBounds.GaussOperatorProductFormula
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Ops

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

def opGs (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, ψ (c : k) * φ ((c : k) • f)

def opGsStar (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (f : Fin r → k) : ℂ :=
  ∑ c : kˣ, (starRingEnd ℂ) (ψ (c : k)) * φ (((c⁻¹ : kˣ) : k) • f)

def opFF (ψ : AddChar k ℂ) (φ : (Fin r → k) → ℂ) (x : Fin r → k) : ℂ :=
  ∑ f ∈ univ.filter (fun f => f ≠ 0), ψ (pair f x) * φ f

end Ops

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

-- bundled from Formalism.LogVandermondeBounds.LogRatioUpperBound
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def plusSign (k i : ℕ) : Bool := decide (i < k - 1 ∨ (i - (k - 1)) % 2 = 0)

def nBetween (k a b : ℕ) : ℕ := ((Ioo a b).filter (fun c => plusSign k c ≠ plusSign k a)).card

noncomputable def dTau (k m : ℕ) (lam : ℕ → ℝ) : ℝ :=
  (∏ a ∈ range (k - 1 + m), ∏ b ∈ (Ico (a + 1) (k - 1 + m)).filter (fun b => plusSign k b = plusSign k a),
      (lam a - lam b + nBetween k a b)) /
    ((∏ i ∈ range (k - 1 + m / 2), ((i.factorial : ℕ) : ℝ)) * ∏ i ∈ range (m / 2), ((i.factorial : ℕ) : ℝ))

end Formalism.LogVandermondeBounds.StandardLattice
end

-- bundled from Formalism.LogVandermondeBounds.VandPlace
section
namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def VandPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ), 2 ≤ k → 1 ≤ m → 1 ≤ Δ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧
    ((k : ℝ) - 1) * ∑ j ∈ range m, Real.log (b j)
      - 2 * k * Real.log (8 * (x * Real.exp (x ^ ε))) - 2 * k * (1 + Real.log k)
      ≤ Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k)

end Formalism.LogVandermondeBounds.StandardLattice
end

