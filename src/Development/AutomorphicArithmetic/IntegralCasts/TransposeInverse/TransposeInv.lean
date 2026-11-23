module

public import Mathlib

@[expose] public section

namespace Reformulated.TransposeInverseTheory

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

def transposeInvFun (g : GL n R) : GL n R where
  val := ((g⁻¹ : GL n R) : Matrix n n R)ᵀ
  inv := (g : Matrix n n R)ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]

theorem transposeInvFun_involutive :
    Function.Involutive (transposeInvFun : GL n R → GL n R) := by
  intro g
  apply Units.ext
  exact transpose_transpose _

def transposeInv : GL n R ≃* GL n R where
  toFun := transposeInvFun
  invFun := transposeInvFun
  left_inv := transposeInvFun_involutive
  right_inv := transposeInvFun_involutive
  map_mul' g h := by
    apply Units.ext
    change (((g * h)⁻¹ : GL n R) : Matrix n n R)ᵀ =
      ((g⁻¹ : GL n R) : Matrix n n R)ᵀ * ((h⁻¹ : GL n R) : Matrix n n R)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]

end Reformulated.TransposeInverseTheory
