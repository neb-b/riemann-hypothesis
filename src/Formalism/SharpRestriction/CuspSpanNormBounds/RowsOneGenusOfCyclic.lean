module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfLiftNumberGenus
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeRowsGenus

open NumberField Formalism.HermitianLatticesTheory

section Cyc

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem cyc_star_int (o : 𝓞 E) : star (algebraMap (𝓞 E) E o) ∈ Set.range (algebraMap (𝓞 E) E) := by
  have h : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

end Cyc

section Rows

open Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Rows

end Formalism.MainNotions.BridgeRowsGenus

end
