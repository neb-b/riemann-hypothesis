module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lattice

end Lattice

section Fibre

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))

abbrev univG : Over Xo.X := Xo.univ.t.G

end Fibre

section Component

variable {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))

end Component

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
