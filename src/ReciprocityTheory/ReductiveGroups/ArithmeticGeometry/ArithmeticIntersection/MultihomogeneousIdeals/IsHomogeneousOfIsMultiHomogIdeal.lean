module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

def formsDeg (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (d : K → ℕ) :
    Submodule F (MRingOver F ι) :=
  Submodule.span F {f | ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, m ⟨k, i⟩ = d k) ∧ f = monomial m 1}

def hilbFn (J : Ideal (MRingOver F ι)) (d : K → ℕ) : ℕ :=
  Module.finrank F ((formsDeg F ι d).map (Ideal.Quotient.mkₐ F J).toLinearMap)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section SupSpan

variable [DecidableEq K]

end SupSpan

end ReciprocityTheory.ChartRestriction.G.AI.I1
