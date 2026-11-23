module

public import Mathlib

@[expose] public section

namespace KStar.Selmer

open Matrix Module

section Minors

variable {R : Type*} [CommRing R] {m n : Type*}

def minorIdeal (k : ℕ) (A : Matrix m n R) : Ideal R :=
  Ideal.span {x | ∃ (r : Fin k → m) (c : Fin k → n), x = (A.submatrix r c).det}

end Minors

section Complex

variable {R : Type*} [CommRing R] {m n m' n' : Type*}

def coefMap [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    (n → M) →ₗ[R] (m → M) :=
  LinearMap.pi fun i => ∑ j, Φ i j • LinearMap.proj j

theorem coefMap_apply [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M]
    (v : n → M) (i : m) : coefMap Φ M v i = ∑ j, Φ i j • v j := by
  simp [coefMap, LinearMap.sum_apply]

def H1c [Fintype n] (Φ : Matrix m n R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R (n → M) :=
  LinearMap.ker (coefMap Φ M)

abbrev H2 [Fintype n] (Φ : Matrix m n R) : Type _ :=
  (m → R) ⧸ LinearMap.range Φ.mulVecLin

def IsMinimal (Φ : Matrix m n R) : Prop :=
  ∀ i j, Φ i j ∈ Ideal.jacobson (⊥ : Ideal R)

def IsHtpyEquiv [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq m] [DecidableEq n]
    [DecidableEq m'] [DecidableEq n'] (Φ : Matrix m n R) (Φ' : Matrix m' n' R)
    (f₁ : Matrix n' n R) (f₂ : Matrix m' m R) : Prop :=
  Φ' * f₁ = f₂ * Φ ∧ ∃ (g₁ : Matrix n n' R) (g₂ : Matrix m m' R) (h : Matrix n m R)
    (h' : Matrix n' m' R), Φ * g₁ = g₂ * Φ' ∧ g₁ * f₁ = 1 + h * Φ ∧ g₂ * f₂ = 1 + Φ * h ∧
      f₁ * g₁ = 1 + h' * Φ' ∧ f₂ * g₂ = 1 + Φ' * h'

end Complex

section Special

variable {Λ O : Type*} [CommRing Λ] [CommRing O] {m n : Type*}

abbrev FracMod (O K : Type*) [CommRing O] [Field K] [Algebra O K] : Type _ :=
  K ⧸ (1 : Submodule O K)

end Special

section Koszul

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

end Koszul

section Lagrangian

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

def IsHalfIsotropic (B : LinearMap.BilinForm k V) (L : Submodule k V) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ 2 * finrank k L = finrank k V

variable {H H' : Type*} [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']

def hyperbolic (β : H →ₗ[k] H' →ₗ[k] k) : LinearMap.BilinForm k (H × H') :=
  β.compl₁₂ (LinearMap.fst k H H') (LinearMap.snd k H H') +
    β.flip.compl₁₂ (LinearMap.snd k H H') (LinearMap.fst k H H')

theorem hyperbolic_apply (β : H →ₗ[k] H' →ₗ[k] k) (v w : H × H') :
    hyperbolic β v w = β v.1 w.2 + β w.1 v.2 := by
  simp [hyperbolic]

end Lagrangian

end KStar.Selmer
