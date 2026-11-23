module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open scoped TensorProduct ContDiff

namespace GlobalTheory.WeilTieCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hHom_add_left (V W : HSp D) (x x' y : WA V W) : hHom V W (x + x') y = hHom V W x y + hHom V W x' y := by
  unfold hHom
  split_ifs <;> simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hHom_add_right (V W : HSp D) (x y y' : WA V W) : hHom V W x (y + y') = hHom V W x y + hHom V W x y' := by
  unfold hHom
  split_ifs <;> simp [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem symplH_add_left (V W : HSp D) (x x' y : WA V W) :
    symplH V W (x + x') y = symplH V W x y + symplH V W x' y := by
  unfold symplH sympl
  rw [hHom_add_right, mul_add, map_add (f := _), mul_add]

theorem symplH_add_right (V W : HSp D) (x y y' : WA V W) :
    symplH V W x (y + y') = symplH V W x y + symplH V W x y' := by
  unfold symplH sympl
  rw [hHom_add_left, mul_add, map_add (f := _), mul_add]

theorem heis_heis (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w w' : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W w (Heisenberg₂ ψ V W w' f) = ψ (symplH V W w w') • Heisenberg₂ ψ V W (w + w') f := by
  funext x
  simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul, symplH_add_left, symplH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heis_quasi (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (w₀ : WA V W) (f : WA V W → ℂ)
    (hf : ∀ γ w, f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * f w) (γ) (w : WA V W) :
    Heisenberg₂ ψ V W w₀ f (ratW V W γ + w) = ψ (-(symplH V W (ratW V W γ) w)) * Heisenberg₂ ψ V W w₀ f w := by
  simp only [Heisenberg₂]
  rw [add_assoc, hf, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    symplH_add_left, symplH_add_right]
  congr 2
  ring

theorem symplH_transpose (V W : HSp D) (hne : V.rank ≠ W.rank) (x y : WA V W) :
    symplH W V x.transpose y.transpose = symplH V W x y := by
  unfold symplH sympl
  rw [hHom_transpose V W hne]

theorem isThetaFun_transpose (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (hne : V.rank ≠ W.rank) (f : WA V W → ℂ)
    (hf : IsThetaFun ψ V W f) : IsThetaFun ψ W V (fun y : WA W V => f y.transpose) := by
  have ct : Continuous fun y : WA W V => (y.transpose : WA V W) := continuous_id.matrix_transpose
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp ct, fun k L hL h0 w => ?_⟩
  · have e : (ratW W V γ).transpose = ratW V W γ.transpose := rfl
    have := hf.quasi γ.transpose w.transpose
    rw [← e, symplH_transpose W V hne.symm] at this
    simpa [Matrix.transpose_add] using this
  · obtain ⟨U, hU, hfix⟩ := hf.level
    let τ : WA W V →+ WA V W := (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom
    refine ⟨U.comap τ, hU.preimage ct, fun u hu h0 => ?_⟩
    have h1 : (u.transpose : WA V W).map (infPart D) = 0 := by
      ext i j; exact congrFun (congrFun h0 j) i
    funext y
    have := congrFun (hfix u.transpose hu h1) y.transpose
    simp only [Heisenberg₂] at this ⊢
    rw [symplH_transpose W V hne.symm] at this
    simpa [Matrix.transpose_add] using this
  · let τ : WA W V →+ WA V W := (Matrix.transposeAddEquiv _ _ _).toAddMonoidHom
    have := hf.smooth k (τ.comp L) (ct.comp hL) (fun t => by
      ext i j; exact congrFun (congrFun (h0 t) j) i) w.transpose
    exact this

variable {X : ThetaX D} {T : ThetaTied D X}


end GlobalTheory.WeilTieCheck

end
