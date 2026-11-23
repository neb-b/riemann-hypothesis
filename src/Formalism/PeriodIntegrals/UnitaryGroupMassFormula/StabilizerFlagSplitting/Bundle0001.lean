module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.PrjMulVecOfL
section
open Matrix

noncomputable section

namespace PI.StabSplit.Proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def prj (H : Matrix n n ℂ) (Y : Matrix n ι ℂ) : Matrix n n ℂ := Y * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H)

variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)

lemma prj_Y (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * Y = Y := by
  calc prj H Y * Y = Y * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H * Y)) := by simp only [prj, Matrix.mul_assoc]
    _ = Y := by rw [nonsing_inv_mul _ hG, Matrix.mul_one]

lemma L_prj (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * prj H Y = Yᴴ * H := by
  calc (Yᴴ * H) * prj H Y = ((Yᴴ * H * Y) * (Yᴴ * H * Y)⁻¹) * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = Yᴴ * H := by rw [mul_nonsing_inv _ hG, Matrix.one_mul]

lemma prj_sq (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * prj H Y = prj H Y := by
  calc prj H Y * prj H Y = (prj H Y * Y) * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = prj H Y := by rw [prj_Y H Y hG]; rfl

lemma prj_star (hH : Hᴴ = H) : (prj H Y)ᴴ * H = H * prj H Y := by
  simp only [prj, conjTranspose_mul, conjTranspose_nonsing_inv, hH, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma L_one_sub (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * (1 - prj H Y) = 0 := by
  rw [Matrix.mul_sub, L_prj H Y hG, Matrix.mul_one, sub_self]

lemma prj_mulVec_of_L {v : n → ℂ} (hv : (Yᴴ * H) *ᵥ v = 0) : prj H Y *ᵥ v = 0 := by
  rw [prj, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma prj_mul_of_L {m : Type*} [Fintype m] (A : Matrix n m ℂ) (hA : (Yᴴ * H) * A = 0) :
    prj H Y * A = 0 := by
  rw [prj, Matrix.mul_assoc, hA, Matrix.mul_zero]

lemma presM (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (C : Matrix ι ι ℂ) (hC : g * Y = Y * C) :
    (1 - prj H Y) * g * prj H Y = 0 := by
  have : g * prj H Y = Y * C * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H)) := by
    rw [prj, Matrix.mul_assoc Y, ← Matrix.mul_assoc g, hC]
  rw [Matrix.mul_assoc, this, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc (prj H Y),
    ← Matrix.mul_assoc (prj H Y), prj_Y H Y hG, sub_self]

lemma presU (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (hg : gᴴ * H * g = H)
    (hdet : IsUnit g.det) (C : Matrix ι ι ℂ) (hC : g⁻¹ * Y = Y * C) :
    prj H Y * g * (1 - prj H Y) = 0 := by
  have hgs : IsUnit gᴴ.det := by rw [det_conjTranspose]; exact hdet.star
  have hHg : H * g = (g⁻¹)ᴴ * H := by
    rw [conjTranspose_nonsing_inv]
    calc H * g = (gᴴ)⁻¹ * (gᴴ * H * g) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hgs, Matrix.one_mul]
      _ = (gᴴ)⁻¹ * H := by rw [hg]
  have hL : (Yᴴ * H) * g = Cᴴ * (Yᴴ * H) := by
    rw [Matrix.mul_assoc, hHg, ← Matrix.mul_assoc, ← conjTranspose_mul, hC, conjTranspose_mul,
      Matrix.mul_assoc]
  have : (Yᴴ * H) * (g * (1 - prj H Y)) = 0 := by
    rw [← Matrix.mul_assoc, hL, Matrix.mul_assoc, L_one_sub H Y hG, Matrix.mul_zero]
  rw [Matrix.mul_assoc, prj_mul_of_L H Y _ this]

lemma exists_C (A : Matrix n ι ℂ)
    (hA : ∀ j, (fun i => A i j) ∈ Submodule.span ℂ (Set.range fun l => fun i => Y i l)) :
    ∃ C : Matrix ι ι ℂ, A = Y * C := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hA j)
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have h := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Matrix.mul_apply, ← h]
  simp [mul_comm]

lemma Y_inj (hG : IsUnit (Yᴴ * H * Y).det) (c : ι → ℂ) (hc : Y *ᵥ c = 0) : c = 0 := by
  have h1 : (Yᴴ * H * Y) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have h2 := congrArg (fun v => (Yᴴ * H * Y)⁻¹ *ᵥ v) h1
  simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hG] using h2

end PI.StabSplit.Proj
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerFlagSplitting.UnitR
section
namespace PI.StabSplit.Alg

variable {R : Type*} [Ring R]

theorem decomp (h P : R) (hPP : P * P = P) (hU : P * h * (1 - P) = 0) :
    (h * P + (1 - P)) * (h * (1 - P) + P) = h := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have e : (h * P + (1 - P)) * (h * (1 - P) + P) - h =
      h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) := by
    noncomm_ring
  have z : h * (P * h * (1 - P)) + h * (P * P - P) - P * h * (1 - P) - (P * P - P) = 0 := by
    simp only [hU, r, mul_zero, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem uniq (h P ρ κ : R) (hρκ : ρ * κ = h) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hκU : P * κ * (1 - P) = 0) :
    ρ = h * P + (1 - P) ∧ κ = h * (1 - P) + P := by
  have a : ρ * κ - h = 0 := sub_eq_zero.mpr hρκ
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  constructor
  · have e : ρ - (h * P + (1 - P)) = (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) := by
      noncomm_ring
    have z : (ρ * κ - h) * P - ρ * (κ * P - P) + (ρ * (1 - P) - (1 - P)) = 0 := by
      simp only [a, b, c, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)
  · have e : κ - (h * (1 - P) + P) = (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) := by
      noncomm_ring
    have z : (κ * P - P) + P * κ * (1 - P) + (ρ * κ - h) * (1 - P)
        - ρ * (P * κ * (1 - P)) - (ρ * (1 - P) - (1 - P)) * κ * (1 - P) = 0 := by
      simp only [a, b, c, hκU, mul_zero, zero_mul, add_zero, sub_zero]
    exact sub_eq_zero.mp (e.trans z)

theorem comm (P ρ κ : R) (hρ : ρ * (1 - P) = 1 - P) (hκ : κ * P = P)
    (hρM : (1 - P) * ρ * P = 0) (hκU : P * κ * (1 - P) = 0) : ρ * κ = κ * ρ := by
  have b : ρ * (1 - P) - (1 - P) = 0 := sub_eq_zero.mpr hρ
  have c : κ * P - P = 0 := sub_eq_zero.mpr hκ
  have e : ρ * κ - κ * ρ = ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) := by
    noncomm_ring
  have z : ρ * (κ * P - P) + ρ * (P * κ * (1 - P)) - P * κ * (1 - P)
      + (ρ * (1 - P) - (1 - P)) * κ * (1 - P) + (1 - P) * ρ * P - (κ * P - P) * ρ * P
      - κ * ((1 - P) * ρ * P) - κ * (ρ * (1 - P) - (1 - P)) = 0 := by
    simp only [b, c, hρM, hκU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

theorem nilp (P g : R) (m : ℕ) (hPP : P * P = P) (hgQ : (g - 1) * (1 - P) = 0)
    (hgM : (1 - P) * g * P = 0) (hm : (g - 1) ^ m * P = 0) : (g - 1) ^ (m + 1) = 0 := by
  have r : P * P - P = 0 := sub_eq_zero.mpr hPP
  have h1 : (g - 1) * P = P * ((g - 1) * P) := by
    have e : (g - 1) * P - P * ((g - 1) * P) = (1 - P) * g * P + (P * P - P) := by noncomm_ring
    rw [hgM, r, add_zero] at e
    exact sub_eq_zero.mp e
  have h2 : g - 1 = (g - 1) * P := by
    have e : (g - 1) - (g - 1) * P = (g - 1) * (1 - P) := by noncomm_ring
    rw [hgQ] at e
    exact sub_eq_zero.mp e
  calc (g - 1) ^ (m + 1) = (g - 1) ^ m * (g - 1) := pow_succ _ _
    _ = (g - 1) ^ m * ((g - 1) * P) := by rw [← h2]
    _ = (g - 1) ^ m * (P * ((g - 1) * P)) := by rw [← h1]
    _ = ((g - 1) ^ m * P) * ((g - 1) * P) := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hm, zero_mul]

variable [StarRing R]

theorem unitK (H P h : R) (hH : star H = H) (hPH : star P * H = H * P) (hPP : P * P = P)
    (hh : star h * H * h = H) (hU : P * h * (1 - P) = 0) :
    star (h * (1 - P) + P) * H * (h * (1 - P) + P) = H := by
  have r1 : star P * H - H * P = 0 := sub_eq_zero.mpr hPH
  have r2 : P * P - P = 0 := sub_eq_zero.mpr hPP
  have r3 : star h * H * h - H = 0 := sub_eq_zero.mpr hh
  have r5 : (1 - star P) * (star h * star P) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_zero] using congrArg star hU
  have e : star (h * (1 - P) + P) * H * (h * (1 - P) + P) - H =
      H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P := by
    simp only [star_add, star_mul, star_sub, star_one]
    noncomm_ring
  have z : H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P = 0 := by
    simp only [r1, r2, r3, r5, hU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)

end PI.StabSplit.Alg
end

