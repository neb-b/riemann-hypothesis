module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  (j : Ω →+* PadicAlgCl l)

def jE : E →+* PadicAlgCl l := j.comp (algebraMap E Ω)

def KwF : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => jE (E := E) j (Module.finBasis ℚ E i))

instance KwF_fin : FiniteDimensional ℚ_[l] (KwF (E := E) j) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem jE_mem (x : E) : jE j x ∈ KwF (E := E) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (Module.finBasis ℚ E).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin ℚ_[l] _ ⟨i, rfl⟩)

theorem mem_GK_of_fix (σ : GQ l) (h : ∀ x : E, σ (jE j x) = jE j x) :
    σ ∈ (KwF (E := E) j).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hle : KwF (E := E) j ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    rw [KwF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have hst : Subgroup.zpowers σ ≤
        MulAction.stabilizer (GQ l) (jE (E := E) j (Module.finBasis ℚ E i)) :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (h _))
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hx) σ (Subgroup.mem_zpowers σ)

theorem norm_aut (σ : GQ l) (x : PadicAlgCl l) : ‖σ x‖ = ‖x‖ := by
  have h1 : ∀ y : PadicAlgCl l, ‖y‖ = spectralNorm ℚ_[l] (PadicAlgCl l) y := fun y => rfl
  rw [h1, h1, ← spectralNorm_eq_of_equiv]

end Formalism.BasicNotions.Examples₂.LB
