module

public import Mathlib

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix Real

noncomputable section

structure SiegelPt (g : ℕ) where

  τ : Matrix (Fin g) (Fin g) ℂ
  isSymm : τ.IsSymm
  im_posDef : (τ.map Complex.im).PosDef

def intVec {g : ℕ} (v : Fin g → ℤ) : Fin g → ℂ := fun i => (v i : ℂ)

structure HalfChar (g : ℕ) where

  ε : Fin g → Fin 2

  ε' : Fin g → Fin 2

namespace HalfChar

variable {g : ℕ} (m : HalfChar g)

def a : Fin g → ℂ := fun i => ((m.ε i : ℕ) : ℂ) / 2

def b : Fin g → ℂ := fun i => ((m.ε' i : ℕ) : ℂ) / 2

end HalfChar

def autFactor {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) (u : Fin g → ℤ) (z : Fin g → ℂ) :
    ℂ :=
  cexp (-(π * I * n * (intVec u ⬝ᵥ P.τ *ᵥ intVec u)) - 2 * π * I * n * (intVec u ⬝ᵥ (z + m.b)))

def perFactor {g : ℕ} (m : HalfChar g) (n : ℕ) (v : Fin g → ℤ) : ℂ :=
  cexp (2 * π * I * n * (m.a ⬝ᵥ intVec v))

def thetaSec {g : ℕ} (P : SiegelPt g) (m : HalfChar g) (n : ℕ) :
    Submodule ℂ ((Fin g → ℂ) → ℂ) where
  carrier := {f | Differentiable ℂ f ∧
    (∀ (v : Fin g → ℤ) (z : Fin g → ℂ), f (z + intVec v) = perFactor m n v * f z) ∧
    ∀ (u : Fin g → ℤ) (z : Fin g → ℂ), f (z + P.τ *ᵥ intVec u) = autFactor P m n u z * f z}
  add_mem' := by
    rintro f h ⟨hf, hf1, hf2⟩ ⟨hh, hh1, hh2⟩
    refine ⟨hf.add hh, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.add_apply, hf1, hh1]; ring
    · simp only [Pi.add_apply, hf2, hh2]; ring
  zero_mem' := ⟨differentiable_const 0, fun _ _ => by simp, fun _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hf2⟩
    refine ⟨hf.const_smul c, fun v z => ?_, fun u z => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf1]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, hf2]; ring

structure RigSymForm (K : Type) [Field K] [Algebra K ℂ] where

  g : ℕ

  pt : SiegelPt g

  ch : HalfChar g

  S : ℕ → Submodule K ((Fin g → ℂ) → ℂ)
  S_le : ∀ n, ∀ f ∈ S n, f ∈ thetaSec pt ch n
  one_mem : (fun _ => (1 : ℂ)) ∈ S 0
  mul_mem : ∀ k n f h, f ∈ S k → h ∈ S n → f * h ∈ S (k + n)
  span_eq : ∀ n, Submodule.span ℂ (S n : Set ((Fin g → ℂ) → ℂ)) = thetaSec pt ch n
  linIndep : ∀ (n : ℕ) (s : Finset ((Fin g → ℂ) → ℂ)), (↑s : Set ((Fin g → ℂ) → ℂ)) ⊆ S n →
    LinearIndependent K (fun f : s => (f : (Fin g → ℂ) → ℂ)) →
    LinearIndependent ℂ (fun f : s => (f : (Fin g → ℂ) → ℂ))

  rig : ℂˣ
  rig_mem : ∀ n, ∀ f ∈ S n, ∃ c : K, (rig : ℂ) ^ n * f 0 = algebraMap K ℂ c

end

end GroundTheory.Heights₂.Heights.KeyFormula
