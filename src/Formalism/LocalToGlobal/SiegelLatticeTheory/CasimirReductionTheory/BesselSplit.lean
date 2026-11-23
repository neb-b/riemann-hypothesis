module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SmoothTranslationMeasure.SmoothTranslate

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.BesselSplit

open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature MeasureTheory Finset
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Period

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end Period

section Chain

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

end Chain

section Smooth

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
    (hPu : IsUnit P) (hPJ : Matrix.conjTranspose P * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) {a : Mat k r}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hJ : Formalism.REAL.Jm ε = Matrix.conjTranspose P⁻¹ * Formalism.QuantumDeterminants.Hpk k r * P⁻¹ := by
    rw [← hPJ]
    rw [show Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose P * Formalism.REAL.Jm ε * P) * P⁻¹ = Matrix.conjTranspose (P * P⁻¹) * Formalism.REAL.Jm ε * (P * P⁻¹) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hPP : Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have ha' : Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  calc Matrix.conjTranspose (P * a * P⁻¹) * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = Matrix.conjTranspose P⁻¹ * Matrix.conjTranspose a * (Matrix.conjTranspose P * Matrix.conjTranspose P⁻¹) * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * P) * a * P⁻¹ := by
        rw [hJ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.conjTranspose P⁻¹ * (Matrix.conjTranspose a * Formalism.QuantumDeterminants.Hpk k r * a) * P⁻¹ := by
        rw [hPP, h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hJ]

theorem mulOnUH_of_dsHpk {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) :
    PI.PhMeasCore.UnitaryGroupMassFormula.MulOnUH (Formalism.QuantumDeterminants.Hpk k r) σ := by
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, -⟩, hDS⟩ := hσ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  obtain ⟨⟨hone, hmul⟩, -, -⟩ := hDS.2.2.1
  have conj : ∀ a : Mat k r, P⁻¹ * (P * a * P⁻¹) * P = a := fun a => by
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have mem : ∀ a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), P * a * P⁻¹ ∈ UJset ε := fun a ha => conjTranspose_conj_mul_Jm_mul_conj_eq_Jm_of_mem_UH hPu hPJ ha
  refine ⟨?_, fun a ha b hb => ?_⟩
  · simpa [h1] using hone
  · have e := hmul _ (mem a ha) _ (mem b hb)
    have e3 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, h1, Matrix.one_mul]
    simp only [e3, conj] at e
    exact e

theorem smooth_translate_ds {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {w : H} (hw : w ∈ smoothVecs (k := k) (r := r) σ)
    {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : σ x w ∈ smoothVecs (k := k) (r := r) σ := by
  exact PI.PhMeasCore.UnitaryGroupMassFormula.smooth_translate (mulOnUH_of_dsHpk hσ) hw hx

end Smooth

section GGP

end GGP

end Formalism.L2.SG.BesselSplit
