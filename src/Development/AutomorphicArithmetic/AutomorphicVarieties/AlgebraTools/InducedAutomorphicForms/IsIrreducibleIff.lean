module

public import Mathlib

@[expose] public section

noncomputable section

namespace UpperTheory.V.AlgebraTools

section Irr

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]

def StableOn (ρ : Representation k G V) (H : Subgroup G) (W : Submodule k V) : Prop :=
  ∀ h ∈ H, ∀ v ∈ W, ρ h v ∈ W

def IrrOn (ρ : Representation k G V) (H : Subgroup G) : Prop :=
  ∀ W : Submodule k V, StableOn ρ H W → W = ⊥ ∨ W = ⊤

def matRep {n : Type} [Fintype n] [DecidableEq n] (r : G →* GL n k) : Representation k G (n → k) where
  toFun g := Matrix.toLin' (r g : Matrix n n k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

end Irr

def subst {k n : Type} [CommRing k] [Fintype n] (A : Matrix n n k) : MvPolynomial n k →ₐ[k] MvPolynomial n k :=
  MvPolynomial.aeval fun i => ∑ j, A j i • MvPolynomial.X j

end UpperTheory.V.AlgebraTools
