module

public import Mathlib
public import Formalism.HermitianLattices.StatementLat
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataCoeff
public import Formalism.LocalRingCardinality.DataArith
public import Formalism.LocalRingCardinality.DataKernels
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.SharpRestriction.GrowthBounds.DataG
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.FrobeniusOrbits.Bundle0001
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.CoboundaryTransfers.Statement
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0001
public import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
public import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois

@[expose] public section

namespace Bl.general_b_fact_left_alt

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] {S : Formalism.BasicNotions.HSpace E}
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsFullLattice.{0, 0, 0} E Λ →
    ∀ (v : S.V),
      Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} c 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} c v)) := by
  intro E _ _ _ S Λ hΛ v
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]; trivial
  obtain ⟨y, hy, z, rfl⟩ :=
    (IsLocalization.mem_span_iff (R := NumberField.RingOfIntegers E)
      (M := nonZeroDivisors (NumberField.RingOfIntegers E)) (S := E)).mp hv
  rw [Submodule.span_eq] at hy
  refine ⟨z, nonZeroDivisors.coe_ne_zero z, ?_⟩
  rw [← IsScalarTower.algebraMap_smul E (z : NumberField.RingOfIntegers E), smul_smul,
    IsLocalization.mk'_spec', map_one, one_smul]
  exact hy

end Bl.general_b_fact_left_alt
