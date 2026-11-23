module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume
open scoped InnerProductSpace

namespace GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem finiteDimensional_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] :
    FiniteDimensional ℂ (L2 (latticeGL E 0) μ) := by
  have : Subsingleton (Quot (latticeGL E 0)) := ⟨fun p q => Quotient.inductionOn₂ p q fun x y => by
    rw [Subsingleton.elim x y]⟩
  refine FiniteDimensional.of_injective (V₂ := ℂ) (K := ℂ)
    { toFun := fun F : L2 (latticeGL E 0) μ => lift (latticeGL E 0) F 1
      map_add' := fun F F' => ?_
      map_smul' := fun c F => ?_ } fun F F' e => l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (.of_forall fun x => by rw [Subsingleton.elim x 1]; exact e)
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx

end GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

end
