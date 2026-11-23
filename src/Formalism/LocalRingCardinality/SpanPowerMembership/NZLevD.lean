module

public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002
public import Formalism.LocalToGlobal.GroupLattices.FockModels.SpanTopOf
public import Formalism.SharpRestriction.GrowthBounds.DataG

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

section Rename₂

variable {R σ τ M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

end Rename₂

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

instance : Infinite Kf := Infinite.of_injective (Nat.cast : ℕ → Kf) Nat.cast_injective

end Formalism.BasicNotions.Examples₂.NZ
