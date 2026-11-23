module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0004
public import Mathlib

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

theorem eq_top_of_nU_nL (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hl : ∀ c, nL c ∈ H) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨x, hx⟩ := cellGeneric F {g}
  obtain ⟨b₁, a, b₂, h⟩ := (mem_cell_iff _).1 (hx g (Finset.mem_singleton_self g))
  rw [← H.mul_mem_cancel_right (hl x), h, mul_assoc (nU b₁), mD_mul_wW]
  exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
theorem eq_top_of_nU_wW (H : Subgroup (G1 F)) (hn : ∀ b, nU b ∈ H) (hw : wW F ∈ H) : H = ⊤ :=
  eq_top_of_nU_nL H hn fun c => by rw [nL_eq]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)

theorem Gam_le (H : Subgroup (G1 F)) (hn : ∀ b : F, nU (rt b) ∈ H) (hw : wW F ∈ H) : Gam F ≤ H := by
  have hl : ∀ c : F, nL (rt c) ∈ H := fun c => by
    rw [nL_eq, rt, ← map_neg]; exact mul_mem (mul_mem hw (hn _)) (inv_mem hw)
  have key : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, γ 1 0 ≠ 0 → ratS F γ ∈ H := fun γ hc => by
    have e : ((IdeleGroup.diagonal F (Units.mk0 _ hc))⁻¹ : (A F)ˣ).val = rt (γ 1 0)⁻¹ := rfl
    have e' : (IdeleGroup.diagonal F (Units.mk0 _ hc) : (A F)ˣ).val = rt (γ 1 0) := rfl
    rw [cell_normal (ratS F γ) (IdeleGroup.diagonal F (Units.mk0 _ hc)) rfl, mul_assoc (nU _), mD_mul_wW, inv_neg, inv_inv,
      Units.val_neg, Units.val_neg, neg_neg, e, e', ratS_apply, ratS_apply]
    simp only [rt, ← map_mul, ← map_neg]
    exact mul_mem (mul_mem (hn _) (mul_mem (mul_mem (hn _) (hl _)) (hn _))) (hn _)
  rintro _ ⟨γ, rfl⟩
  by_cases hc : γ 1 0 = 0
  · obtain ⟨w, hw'⟩ := wW_mem (F := F)
    have h10 : w 1 0 = -1 := by
      haveI := AdeleBaseChange.nontrivial_adeleRing F
      apply (algebraMap F (A F)).injective
      simpa using (ratS_apply w 1 0).symm.trans (congrArg (fun g : G1 F => g 1 0) hw')
    rw [← H.mul_mem_cancel_right hw, ← hw', ← map_mul]
    refine key _ ?_
    have hd := γ.det_coe
    rw [Matrix.det_fin_two, hc] at hd
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hc, h10]
    intro h
    have : γ.1 1 1 = 0 := by simpa using h
    simp [this] at hd
  · exact key γ hc

end UpperTheory.ConvolutionTheory.R2

end
