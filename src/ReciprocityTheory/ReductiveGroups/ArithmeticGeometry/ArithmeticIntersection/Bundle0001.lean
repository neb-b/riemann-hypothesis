module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.IndexSt
section
namespace ReciprocityTheory.ChartRestriction.G.AI

def IndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subring K),
    Module.Free ℤ O → Module.Finite ℤ O → Module.finrank ℤ O = Module.finrank ℚ K →
    ∀ f : O, f ≠ 0 →
      (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| ∧
      Real.log (Nat.card (O ⧸ Ideal.span {f})) = ∑ σ : K →+* ℂ, Real.log ‖σ f‖

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open MeasureTheory

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def sphereMeasure : Measure S2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

noncomputable def gPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 * ∑ j ∈ Finset.range (2 * k),
    (-1 : ℝ) ^ j • (MvPolynomial.X 0 ^ (2 * k - 1 - j) * MvPolynomial.X 1 ^ j)

noncomputable def dgPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (gPoly k))

noncomputable def kappa (k : ℕ) : ℝ :=
  -∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
      MvPolynomial.eval ![(n₁ : E3) 2, (n₂ : E3) 2] (dgPoly k) ∂sphereMeasure ∂sphereMeasure

def SphereInvStatement : Prop :=
  IsProbabilityMeasure sphereMeasure ∧
  ∀ L : E3 ≃ₗᵢ[ℝ] E3,
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2)) sphereMeasure sphereMeasure

def ArchimedesStatement : Prop :=
  ∀ (u v w : E3) (f : ℝ → ℝ), ‖u‖ = 1 → IntervalIntegrable f volume (-1) 1 →
    Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * t * inner ℝ u v) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)))

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
section
namespace ReciprocityTheory.ChartRestriction.G.AI

universe u v

open Module

noncomputable def ordMod {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (A ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal x)

noncomputable def ordLoc {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap A (Localization.AtPrime p.asIdeal) x)

def LocalLengthAdditivity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ →
    length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            ordMod p x

def LocalLengthAdditivityTorsionFree : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] (x : A),
    ringKrullDim A = 1 → x ≠ 0 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) = (finrank A M : ℕ∞) * Ring.ord A x

def LocalLengthMultiplicativity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 →
    length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    (length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b) ∧
    (length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧
     length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤) ∧
    (∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ b ∈ p.asIdeal), ordLoc p b * ordMod p a

end ReciprocityTheory.ChartRestriction.G.AI
end

