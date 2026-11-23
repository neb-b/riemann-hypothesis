module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0017

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaValueIdentityCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

attribute [local instance] Over.cartesianMonoidalCategory

section Valuations

open IsLocalRing Polynomial

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem vV_zpow (x : K) (n : ℤ) : vV V (x ^ n) = n * vV V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem exists_unit {x : K} (hx : x ≠ 0) (h : vV V x = 0) : ∃ u : V, IsUnit u ∧ algebraMap V K u = x := by
  have h1 : valV V x = 1 := by
    have h2 : WithZero.log (valV V x) = 0 := by simp only [vV] at h; omega
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h2, WithZero.exp_zero]
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) (x := x) h1.le
  refine ⟨u, ?_, rfl⟩
  by_contra hu
  exact ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) (IsDiscreteValuationRing.maximalIdeal V) u).2 hu).ne h1

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

end Valuations

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)]

end Clauses

end GlobalTheory.ThetaValueIdentityCompare
