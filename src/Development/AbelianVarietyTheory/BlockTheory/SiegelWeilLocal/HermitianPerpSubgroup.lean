module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers

section Unip

variable {A : Type} [CommRing A] {n : ℕ}

def stabAdd (M : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | ∀ v, v ∈ M ↔ (g : Matrix (Fin n) (Fin n) A) *ᵥ v ∈ M}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := by
    intro g hg x
    have := hg (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def unip (M M' : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | g ∈ stabAdd M ∧ g ∈ stabAdd M' ∧
    ∀ v ∈ M, (g : Matrix (Fin n) (Fin n) A) *ᵥ v - v ∈ M'}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨Subgroup.mul_mem _ ha1 hb1, Subgroup.mul_mem _ ha2 hb2, fun v hv => ?_⟩
    have h := M'.add_mem (ha3 _ ((hb1 v).1 hv)) (hb3 v hv)
    simpa only [Units.val_mul, ← Matrix.mulVec_mulVec, sub_add_sub_cancel] using h
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    refine ⟨Subgroup.inv_mem _ h1, Subgroup.inv_mem _ h2, fun v hv => ?_⟩
    have h := M'.neg_mem (h3 _ ((Subgroup.inv_mem _ h1 v).1 hv))
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub] at h
    exact h

end Unip

section Groups

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n r : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

end Groups

section Lattices

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  Nat.card {w : HeightOneSpectrum (𝓞 E) // (p : 𝓞 E) ∈ w.asIdeal} = Module.finrank ℚ E

def gammaOne (SG : Finset (HeightOneSpectrum (𝓞 E))) (k : ℕ) : ℝ≥0∞ :=
  ∏ w ∈ SG, (Nat.card (GL (Fin k) (𝓞 E ⧸ w.asIdeal)) : ℝ≥0∞) /
    (Nat.card (Formalism.L2.Col.HU (𝓞 E ⧸ w.asIdeal) k) : ℝ≥0∞)

end Lattices

section Levels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
  (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E)

end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers
