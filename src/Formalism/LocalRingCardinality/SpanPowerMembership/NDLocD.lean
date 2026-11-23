module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocC
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovariantDegrees

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {j : Ω →+* PadicAlgCl l}
  {A : ValuationSubring Ω} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)

theorem continuous_rHom : Continuous (rHom (E := E) hj) :=
  by apply _root_.UpperTheory.Reformulated.B.CovariantDegrees.continuous_rHom <;> assumption

instance compact_GK (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    CompactSpace ↥K.fixingSubgroup :=
  isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K).isCompact

def eDec : ↥(Dec (F := E) A) ≃* ↥(KwF (E := E) j).fixingSubgroup :=
  (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).symm

theorem eDec_comm (g : ↥(Dec (F := E) A)) (x : Ω) :
    ((eDec hj g : ↥(KwF (E := E) j).fixingSubgroup) : GQ l) (j x) = j ((g : G E Ω) x) := by
  rw [← j_rHom hj]
  congr 2
  exact congrArg Subtype.val ((MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).apply_symm_apply g)

theorem continuous_eDec_symm : Continuous (eDec (E := E) hj).symm := continuous_rHom hj

theorem continuous_eDec : Continuous (eDec (E := E) hj) :=
  Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := (MulEquiv.ofBijective (rHom hj) ⟨rHom_injective hj, rHom_surjective hj⟩).toEquiv)
    (continuous_rHom hj)

end Formalism.BasicNotions.Examples₂.LB

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc LB

end Formalism.BasicNotions.Examples₂
