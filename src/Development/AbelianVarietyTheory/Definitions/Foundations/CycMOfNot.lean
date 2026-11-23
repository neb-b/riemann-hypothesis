module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def cycM (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : (ZMod M)ˣ :=
  open Classical in
  if h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val then h.choose else 1

def repM (M : ℕ) (y : (ZMod M)ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val

def topM (l n r N : ℕ) : ℕ := l ^ (r + n) * N

instance topM.neZero (l n r N : ℕ) [Fact l.Prime] [NeZero N] : NeZero (topM l n r N) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) (NeZero.ne N)⟩

def redM (l n r N : ℕ) (y : (ZMod (topM l n r N))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom y

def redL (l r : ℕ) (y : (ZMod (l ^ (r + 1)))ˣ) : (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom y

theorem cycM_spec (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω)
    (h : ∃ y : (ZMod M)ˣ, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → s z = z ^ (cycM M s : ZMod M).val := by
  classical
  unfold cycM
  rw [dite_eq_left h]
  exact h.choose_spec

theorem repM_spec (M : ℕ) (y : (ZMod M)ˣ)
    (h : ∃ s : Ω ≃ₐ[ℚ] Ω, ∀ z : Ω, z ^ M = 1 → s z = z ^ (y : ZMod M).val) :
    ∀ z : Ω, z ^ M = 1 → (repM M y : Ω ≃ₐ[ℚ] Ω) z = z ^ (y : ZMod M).val :=
  Classical.epsilon_spec h

end GlobalTheory.K4
