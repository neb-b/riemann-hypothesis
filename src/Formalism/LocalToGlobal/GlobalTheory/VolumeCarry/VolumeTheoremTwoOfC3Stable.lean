module

public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Mathlib
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sig_apply (D : D7) (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hE_repr (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (W.frame.repr x) (W.frame.repr y) = W.hT x y := by
  conv_rhs => rw [← W.frame.sum_repr x, ← W.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
    map_smul, smul_eq_mul, sig_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
