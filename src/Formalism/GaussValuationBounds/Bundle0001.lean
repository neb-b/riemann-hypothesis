module

public import Mathlib
public import Formalism.GaussValuationBounds.Statement

@[expose] public section

-- bundled from Formalism.GaussValuationBounds.GaussUnit
section
noncomputable section

namespace Formalism.NOK

open scoped ENNReal

def gaussV {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ)
    (f : PowerSeries O) : ℝ≥0∞ :=
  ⨅ n : ℕ, (((IsDiscreteValuationRing.addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) +
    ENNReal.ofReal (x * n)

def GaussMul : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 < x →
    ∀ f g : PowerSeries O, gaussV x (f * g) = gaussV x f + gaussV x g

def GaussAdd : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ),
    ∀ f g : PowerSeries O, min (gaussV x f) (gaussV x g) ≤ gaussV x (f + g)

def GaussC : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ c : O, gaussV x (PowerSeries.C c) =
      ((IsDiscreteValuationRing.addVal O c : ℕ∞) : ℝ≥0∞)

def GaussUnit : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (x : ℝ), 0 ≤ x →
    ∀ u : PowerSeries O, IsUnit u → gaussV x u = 0

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.KapBound3
section
noncomputable section

namespace Formalism.NOK

def Trunc : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (p : ℕ → A) (y M j : ℕ), 1 ≤ j →
      p (j - 1) ∈ Ideal.span {(ℓ : A), X ^ (ℓ ^ (j - 1))} →
      ∀ r : ℕ,
        (ℓ : A) ^ sigNOK ℓ y M j * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r ∈
          Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊,
            X ^ M * ∏ s ∈ Finset.range j, p s ^ y}

end Formalism.NOK
end
end

