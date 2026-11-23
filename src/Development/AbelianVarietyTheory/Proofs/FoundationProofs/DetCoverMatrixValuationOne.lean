module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.UG (GLint)

noncomputable section
namespace GlobalTheory.GLintCover

section
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

theorem v_eq_one_of_mul {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1

theorem det_v {n : ℕ} {X : GL (Fin n) (v.adicCompletion F)} (hX : X ∈ GLint (Fin n) (Formalism.UG.Ov F v)) :
    Valued.v (X : Matrix (Fin n) (Fin n) (v.adicCompletion F)).det = 1 := by
  obtain ⟨y, rfl⟩ := hX
  have hd : ∀ z : GL (Fin n) (Formalism.UG.Ov F v),
      ((Formalism.UG.bc (n := Fin n) (Formalism.UG.Ov F v).subtype z : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)).det
      = (((z : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det : Formalism.UG.Ov F v) : v.adicCompletion F) := by
    intro z
    rw [← (Formalism.UG.Ov F v).subtype_apply, RingHom.map_det]; rfl
  have hdi : (y : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det *
      ((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [hd]
  refine v_eq_one_of_mul (SetLike.coe_mem _)
    (SetLike.coe_mem (((y⁻¹ : GL (Fin n) (Formalism.UG.Ov F v)) : Matrix (Fin n) (Fin n) (Formalism.UG.Ov F v)).det)) ?_
  have := congrArg (fun z : Formalism.UG.Ov F v => (z : v.adicCompletion F)) hdi
  exact_mod_cast this

variable {n : ℕ} {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Count
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}

variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Count
end GlobalTheory.GLintCover

noncomputable section
namespace GlobalTheory.GLintCover

section Main
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
variable {ϖ : v.adicCompletion F} {a : Fin n → ℤ}

end Main

end GlobalTheory.GLintCover
