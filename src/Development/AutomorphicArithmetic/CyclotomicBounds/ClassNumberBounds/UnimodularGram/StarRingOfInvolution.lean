module

public import Mathlib

@[expose] public section

namespace KStar.Cstarloc

structure UnramDatum (R : Type*) [CommRing R] [StarRing R] : Prop where
  trace_one : ∃ e : R, e + star e = 1
  norm_onto : ∀ u : R, IsUnit u → star u = u → ∃ a : R, a * star a = u

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

abbrev Sesq (R : Type*) [CommRing R] [StarRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

def IsHerm (h : Sesq R M) : Prop := ∀ x y, h y x = star (h x y)

def IsUnimod (h : Sesq R M) : Prop := Function.Bijective (h.flip : M → Module.Dual R M)

def gram {ι : Type*} (h : Sesq R M) (b : ι → M) : Matrix ι ι R := Matrix.of fun i j => h (b i) (b j)

def IsOrthonormal {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι → M) : Prop := gram h b = 1

def perp (h : Sesq R M) (x : M) : Submodule R M := LinearMap.ker (h.flip x)

def restr (h : Sesq R M) (N : Submodule R M) : Sesq R N := h.domRestrict₁₂ N N

theorem mem_perp (h : Sesq R M) (x y : M) : y ∈ perp h x ↔ h y x = 0 := by
  rw [perp, LinearMap.mem_ker, LinearMap.flip_apply]

end KStar.Cstarloc
