module

public import Mathlib
public import GroundTheory.GlobalFields.HasseNorm

@[expose] public section

namespace GroundTheory.Automorphic

open Module TensorProduct

section QuadAlg

variable {R : Type*} [CommRing R]

end QuadAlg

section BaseChange

variable {L : Type*} [Field L] (d : L) (R : Type*) [CommRing R] [Algebra L R]

theorem algebraMap_quadraticAlgebra_apply (x : L) :
    algebraMap L (QuadraticAlgebra R (algebraMap L R d) 0) x = ⟨algebraMap L R x, 0⟩ := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_re_one (a : R) : (1 : QuadraticAlgebra R a 0).re = 1 := rfl

omit [Algebra L R] in
theorem quadraticAlgebra_im_one (a : R) : (1 : QuadraticAlgebra R a 0).im = 0 := rfl

def omegaRoot : {u : QuadraticAlgebra R (algebraMap L R d) 0 //
    u * u = d • 1 + (0 : L) • u} :=
  ⟨QuadraticAlgebra.omega, by
    rw [QuadraticAlgebra.omega_mul_omega_eq_mk]
    ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]⟩

noncomputable def quadMap : QuadraticAlgebra L d 0 →ₐ[L] QuadraticAlgebra R (algebraMap L R d) 0 :=
  QuadraticAlgebra.lift (omegaRoot d R)

theorem quadMap_apply (z : QuadraticAlgebra L d 0) :
    quadMap d R z = ⟨algebraMap L R z.re, algebraMap L R z.im⟩ := by
  simp only [quadMap, QuadraticAlgebra.lift_apply_apply, omegaRoot]
  ext <;> simp [Algebra.smul_def, algebraMap_quadraticAlgebra_apply]

noncomputable def quadTensorHom :
    R ⊗[L] QuadraticAlgebra L d 0 →ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) (quadMap d R) (fun _ _ => Commute.all _ _)

theorem quadTensorHom_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorHom d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ := by
  simp only [quadTensorHom, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, quadMap_apply]
  ext <;> simp [QuadraticAlgebra.algebraMap_eq, -QuadraticAlgebra.C_eq_algebraMap]

noncomputable def quadTensorInv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    R ⊗[L] QuadraticAlgebra L d 0 :=
  z.re ⊗ₜ 1 + z.im ⊗ₜ QuadraticAlgebra.omega

theorem quadTensorHom_inv (z : QuadraticAlgebra R (algebraMap L R d) 0) :
    quadTensorHom d R (quadTensorInv d R z) = z := by
  simp only [quadTensorInv, map_add (f := _), quadTensorHom_tmul]
  ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]

theorem quadTensorInv_hom (z : R ⊗[L] QuadraticAlgebra L d 0) :
    quadTensorInv d R (quadTensorHom d R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [quadTensorInv]
  | tmul r q =>
    rw [quadTensorHom_tmul, quadTensorInv]
    dsimp only
    have hq : q = q.re • (1 : QuadraticAlgebra L d 0) + q.im • QuadraticAlgebra.omega := by
      ext <;> simp [quadraticAlgebra_re_one, quadraticAlgebra_im_one]
    conv_rhs => rw [hq]
    have h1 : ∀ c : L, r * algebraMap L R c = c • r := fun c => by
      rw [Algebra.smul_def, mul_comm]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, h1, h1,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  | add x y hx hy =>
    have hadd : quadTensorInv d R (quadTensorHom d R (x + y)) =
        quadTensorInv d R (quadTensorHom d R x) + quadTensorInv d R (quadTensorHom d R y) := by
      simp only [map_add (f := _), quadTensorInv, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
        TensorProduct.add_tmul]
      abel
    rw [hadd, hx, hy]

noncomputable def quadTensorEquiv :
    R ⊗[L] QuadraticAlgebra L d 0 ≃ₐ[R] QuadraticAlgebra R (algebraMap L R d) 0 :=
  AlgEquiv.ofBijective (quadTensorHom d R)
    ⟨Function.LeftInverse.injective (quadTensorInv_hom d R),
      Function.RightInverse.surjective (quadTensorHom_inv d R)⟩

theorem quadTensorEquiv_tmul (r : R) (z : QuadraticAlgebra L d 0) :
    quadTensorEquiv d R (r ⊗ₜ z) = ⟨r * algebraMap L R z.re, r * algebraMap L R z.im⟩ :=
  quadTensorHom_tmul d R r z

end BaseChange

section Bridge

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal
open scoped NumberField.LiesOver

variable {L : Type*} [Field L] [NumberField L] (d : L) [Fact (∀ r : L, r ^ 2 ≠ d + 0 * r)]



end Bridge

section HasseNorm

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Filter

universe u

variable {L : Type u} [Field L] [NumberField L]

end HasseNorm

end GroundTheory.Automorphic
