module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.AntisymmetrizedProductEqFactorialSmulQdet

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature

section Grp

variable {k r : ℕ}

theorem unitary_group_mul_mem {a b : Mat k r} (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : a * b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

theorem cayley_conj_mem_diagonal_model {ε : Fin (2 * r + k + 1) → Bool} {P a : Mat k r} (hP : IsCayleyU k r ε P)
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    P * a * P⁻¹ ∈ UJset ε ∧ P⁻¹ * (P * a * P⁻¹) * P = a := by
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hH : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.1.2
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  constructor
  · show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
    calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
        = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hH, ha']
      _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2]; simp
  · calc P⁻¹ * (P * a * P⁻¹) * P = (P⁻¹ * P) * a * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp

theorem discrete_series_map_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {a b : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hb : b ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    σ (a * b) = (σ a).comp (σ b) := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hrep := hDS.2.2.1.1.2 _ (cayley_conj_mem_diagonal_model hP ha).1 _ (cayley_conj_mem_diagonal_model hP hb).1
  have hu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det _).1 hP.1.1
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  have e1 : P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = a * b := by
    calc P⁻¹ * (P * a * P⁻¹ * (P * b * P⁻¹)) * P = (P⁻¹ * P) * a * (P⁻¹ * P) * b * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = a * b := by rw [h1]; simp
  simp only [e1, (cayley_conj_mem_diagonal_model hP ha).2, (cayley_conj_mem_diagonal_model hP hb).2] at hrep
  exact hrep

end Grp

structure BData : Type 1 where
  k : ℕ
  r : ℕ
  z : Fin (2 * r + k + 1) → ℂ
  c : Fin r → ℂ
  u : Fin k → ℝ
  v : Fin (k - 1) → ℝ
  b : Fin (2 * r + 2) → ℝ
  H : Type
  [hN : NormedAddCommGroup H]
  [hI : InnerProductSpace ℂ H]
  [hC : CompleteSpace H]
  σ : Mat k r → (H →L[ℂ] H)
  Vp : Type
  [vN : NormedAddCommGroup Vp]
  [vI : InnerProductSpace ℂ Vp]
  [vF : FiniteDimensional ℂ Vp]
  π : Mat k r → (Vp →L[ℂ] Vp)
  w : H
  μG : Measure (Formalism.QuantumDeterminants.Mt k r)
  μS : Measure (Formalism.QuantumDeterminants.Mt k r)
  ν : Measure (Formalism.QuantumDeterminants.Mt k r)

attribute [instance] BData.hN BData.hI BData.hC BData.vN BData.vI BData.vF

namespace BData

variable (X : BData)

variable {X}

end BData

end Formalism.MainNotions.LeviCoordinates

end
