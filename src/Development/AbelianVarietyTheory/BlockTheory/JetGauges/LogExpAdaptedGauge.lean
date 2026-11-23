module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge

section Chart

variable {k : Type} [CommRing k] {d : ℕ}

def linMap (U : Matrix (Fin d) (Fin d) k) : Pt k 1 d :=
  fun i => ∑ j : Fin d, MvPowerSeries.C (U i j) * X ((0 : Fin 1), j)

end Chart

section Gauges

variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

variable {O : Type} [CommRing O] [StarRing O]

end Gauges

section Integrality

variable {C : Type} [NormedField C] {d : ℕ}

end Integrality

section Letters

variable {C : Type} [NormedField C] [IsUltrametricDist C] [CharZero C]
  {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {d : ℕ}

end Letters

end GlobalTheory.IndefiniteRowSideFullHecke.LogExpAdaptedGauge
