module

public import Mathlib

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

def Ed (K : Type) [Field K] (k d : ℕ) (a b : Fin k) :
    ↥(homogeneousSubmodule (Fin k) K d) →ₗ[K] ↥(homogeneousSubmodule (Fin k) K d) where
  toFun F := ⟨X a * pderiv b (F : MvPolynomial (Fin k) K), by
    have hF : (F : MvPolynomial (Fin k) K).IsHomogeneous d := (mem_homogeneousSubmodule d _).1 F.2
    rw [mem_homogeneousSubmodule]
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      have : (F : MvPolynomial (Fin k) K) = C (AddMonoidAlgebra.coeff (F : MvPolynomial (Fin k) K) 0) :=
        (totalDegree_eq_zero_iff_eq_C).1 (Nat.le_zero.1 hF.totalDegree_le)
      rw [this, pderiv_C, mul_zero]
      exact isHomogeneous_zero _ _ _
    · have h1 := hF.pderiv (i := b)
      have h2 := (isHomogeneous_X K a).mul h1
      have e : 1 + (d - 1) = d := by omega
      rw [e] at h2
      exact h2⟩
  map_add' F G := by
    apply Subtype.ext
    simp [mul_add]
  map_smul' t F := by
    apply Subtype.ext
    simp [mul_smul_comm]

def EdWord (K : Type) [Field K] (k d : ℕ) (l : List (Fin k × Fin k)) :
    Module.End K ↥(homogeneousSubmodule (Fin k) K d) :=
  (l.map fun y => Ed K k d y.1 y.2).prod

def OpBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k d c : ℕ)
    (WW : Submodule K (Module.End K ↥(homogeneousSubmodule (Fin k) K d)))
    (Sg : Set (Module.End K ↥(homogeneousSubmodule (Fin k) K d))),
    (∀ A ∈ WW, ∀ a b : Fin k, Ed K k d a b * A - A * Ed K k d a b ∈ WW) →
    WW = Submodule.span K Sg →
    (∀ A ∈ Sg, ∃ ω : Fin k → ℤ, (∀ a, Ed K k d a a * A - A * Ed K k d a a = (ω a : K) • A) ∧ ∀ a, ω a ≤ c) →
    ∀ A ∈ WW, A ∈ Submodule.span K {B | ∃ l : List (Fin k × Fin k), l.length ≤ c ∧ B = EdWord K k d l}

end Formalism.MainNotions.TestSideCounting
