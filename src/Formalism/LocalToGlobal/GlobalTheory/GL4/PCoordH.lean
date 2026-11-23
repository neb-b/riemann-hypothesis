module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PFrLoc
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.GL3MeanSquares.Bundle0001

@[expose] public section

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

section Norm

variable {E : Type} [Field E] [NumberField E]

end Norm

section Had

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions

end Had

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem hT_equivFun_symm (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i : Fin S.rank)
    (z : Fin S.rank → E) :
    S.hT (b i) (b.equivFun.symm z) = ((fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) *ᵥ z) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem gram_det_ne (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) :
    Matrix.det (fun i j ↦ S.hT (b i) (b j) : Matrix (Fin S.rank) (Fin S.rank) E) ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hy0 : b.equivFun.symm z ≠ 0 := by
    intro h
    apply hz
    have := b.equivFun.apply_symm_apply z
    rw [h, map_zero] at this
    exact this.symm
  apply hy0
  apply S.nondeg.2
  intro x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hT_equivFun_symm, hGz]
  simp

end Coord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc

end
