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

namespace Bl.general_b_fact_third''''

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsFullLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) := by
  intro E _ _ _ S Λ hL x
  have hx : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • (a • y) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem b hay) (Λ.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨w, hw⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(w.2 : NumberField.RingOfIntegers E) * a, mul_ne_zero (nonZeroDivisors.ne_zero w.2.2) ha, ?_⟩
    have key : ((w.2 : NumberField.RingOfIntegers E) * a) • (c • y) = w.1 • (a • y) := by
      rw [← algebraMap_smul E ((w.2 : NumberField.RingOfIntegers E) * a), ← algebraMap_smul E w.1,
        ← algebraMap_smul E a, smul_smul, smul_smul, ← hw, map_mul]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem w.1 hay

end Bl.general_b_fact_third''''
