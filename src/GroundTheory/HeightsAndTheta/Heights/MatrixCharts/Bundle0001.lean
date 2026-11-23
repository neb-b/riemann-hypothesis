module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.BoundsY
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCBounds

open Matrix

noncomputable section

theorem dot_self_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

theorem quad_smul_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((l • (1 : Matrix ι ι ℝ) - A) *ᵥ x) = l * (x ⬝ᵥ x) - x ⬝ᵥ (A *ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem quad_sub_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (l : ℝ)
    (x : ι → ℝ) : x ⬝ᵥ ((A - l • (1 : Matrix ι ι ℝ)) *ᵥ x) = x ⬝ᵥ (A *ᵥ x) - l * (x ⬝ᵥ x) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]

theorem posSemidef_of_real {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A)
    (h : ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x)) : A.PosSemidef :=
  PosSemidef.of_dotProduct_mulVec_nonneg
    ((conjTranspose_eq_transpose_of_trivial A).trans hs) (by simpa using h)

theorem quad_nonneg {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

theorem transpose_of_posSemidef {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.PosSemidef) : Aᵀ = A :=
  (conjTranspose_eq_transpose_of_trivial A).symm.trans hA.isHermitian

theorem quad_symm {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hs : Aᵀ = A) (u v : ι → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hs]

theorem quad_cs {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (u v : ι → ℝ) :
    (u ⬝ᵥ (A *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (A *ᵥ u)) * (v ⬝ᵥ (A *ᵥ v)) := by
  have hvu := quad_symm (transpose_of_posSemidef hA) u v
  have key : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ (A *ᵥ v)) * (t * t) + (2 * (u ⬝ᵥ (A *ᵥ v))) * t +
      u ⬝ᵥ (A *ᵥ u) := by
    intro t
    have h := quad_nonneg hA (u + t • v)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem posDef_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) : A.PosDef := by
  have hs : Aᵀ = A := by
    have := transpose_of_posSemidef h
    rw [transpose_sub, transpose_smul, transpose_one] at this
    exact sub_left_injective this
  refine posDef_iff_dotProduct_mulVec.mpr ⟨(conjTranspose_eq_transpose_of_trivial A).trans hs,
    fun x hx => ?_⟩
  have h1 := quad_nonneg h x
  rw [quad_sub_smul_one] at h1
  have h2 : 0 < x ⬝ᵥ x := by
    rcases (dot_self_nonneg x).lt_or_eq with h3 | h3
    · exact h3
    · exact absurd (dotProduct_self_eq_zero.mp h3.symm) hx
  simpa using (by nlinarith : 0 < x ⬝ᵥ (A *ᵥ x))

theorem inv_le_of_ge {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {c : ℝ}
    (hc : 0 < c) (h : (A - c • (1 : Matrix ι ι ℝ)).PosSemidef) :
    (c⁻¹ • (1 : Matrix ι ι ℝ) - A⁻¹).PosSemidef := by
  have hA : A.PosDef := posDef_of_ge hc h
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_smul_one_sub]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := quad_nonneg h y
      rw [quad_sub_smul_one, hx, dotProduct_comm] at this
      linarith
    have h3 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := dot_self_nonneg _
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h3
    have key : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    have := mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hc.le)
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
    linarith

theorem inv_ge_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {l : ℝ}
    (hl : 0 < l) (hA : A.PosDef) (h : (l • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    (A⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hs : Aᵀ = A := transpose_of_posSemidef hA.posSemidef
  refine posSemidef_of_real ?_ fun x => ?_
  · rw [transpose_sub, transpose_smul, transpose_one, transpose_nonsing_inv, hs]
  · rw [quad_sub_smul_one]
    set y := A⁻¹ *ᵥ x with hy
    have hx : A *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have hcs := quad_cs hA.posSemidef y x
    have e1 : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ x := by rw [← quad_symm hs, hx]
    have e2 : y ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by rw [hx, dotProduct_comm]
    rw [e1, e2] at hcs
    have hxy : 0 ≤ x ⬝ᵥ y := e2 ▸ quad_nonneg hA.posSemidef y
    have hlx : x ⬝ᵥ (A *ᵥ x) ≤ l * (x ⬝ᵥ x) := by
      have := quad_nonneg h x
      rw [quad_smul_one_sub] at this
      linarith
    have hxx := dot_self_nonneg x
    rcases hxx.lt_or_eq with hpos | hzero
    · have h4 : (x ⬝ᵥ x) * (x ⬝ᵥ x) ≤ (l * (x ⬝ᵥ y)) * (x ⬝ᵥ x) := by
        nlinarith [mul_le_mul_of_nonneg_left hlx hxy]
      have h5 : x ⬝ᵥ x ≤ l * (x ⬝ᵥ y) := le_of_mul_le_mul_right h4 hpos
      have := mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr hl.le)
      rw [← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul] at this
      linarith
    · rw [← hzero]; simpa using hxy


open scoped ComplexOrder in
theorem posSemidef_map_ofReal {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (A.map (fun x : ℝ => (x : ℂ))).PosSemidef := by
  have hs : ∀ j k, A k j = A j k := fun j k => by
    simpa using congrFun (congrFun (transpose_of_posSemidef hA) j) k
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext j k
    simp [conjTranspose_apply, hs]
  · set a : ι → ℝ := fun k => (w k).re
    set b : ι → ℝ := fun k => (w k).im
    have ha := quad_nonneg hA a
    have hb := quad_nonneg hA b
    have hre : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).re =
        a ⬝ᵥ (A *ᵥ a) + b ⬝ᵥ (A *ᵥ b) := by
      simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Complex.mul_re,
        Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
        Complex.ofReal_im, a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have him : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im = 0 := by
      have e : (star w ⬝ᵥ (A.map (fun x : ℝ => (x : ℂ)) *ᵥ w)).im =
          ∑ j, ∑ k, (w j).re * (A j k * (w k).im) - ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.mul_im, Complex.mul_re,
          Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.im_sum, Complex.ofReal_re,
          Complex.ofReal_im, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      have hsw : ∑ j, ∑ k, (w j).re * (A j k * (w k).im) =
          ∑ j, ∑ k, (w j).im * (A j k * (w k).re) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
      rw [e, hsw, sub_self]
    exact Complex.nonneg_iff.mpr ⟨hre ▸ add_nonneg ha hb, him.symm⟩

end

end GroundTheory.Heights₂.Heights.MCBounds
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.MCDet

open Matrix
open scoped MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

theorem det_eq_ofReal_re {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A.det = (RCLike.re A.det : 𝕜) := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]

theorem re_det_nonneg {A : Matrix n n 𝕜} (hA : A.PosSemidef) : 0 ≤ RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_nonneg fun i _ => hA.eigenvalues_nonneg i

theorem re_det_pos {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod, RCLike.ofReal_re]
  exact Finset.prod_pos fun i _ => hA.eigenvalues_pos i

theorem one_le_re_det_one_add {Q : Matrix n n 𝕜} (hQ : Q.PosSemidef) :
    1 ≤ RCLike.re (1 + Q).det := by
  have hspec := hQ.isHermitian.spectral_theorem
  set U := hQ.isHermitian.eigenvectorUnitary
  have hUU : (U : Matrix n n 𝕜) * star (U : Matrix n n 𝕜) = 1 := Unitary.coe_mul_star_self U
  have h1 : 1 + Q = (U : Matrix n n 𝕜) *
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)) *
        star (U : Matrix n n 𝕜) := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU]
  have hdet : (1 + Q).det =
      ((1 : Matrix n n 𝕜) + diagonal (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues)).det := by
    rw [h1, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      Unitary.coe_star_mul_self, det_one, one_mul]
  rw [hdet, ← diagonal_one, diagonal_add, det_diagonal]
  have : ∏ i, ((1 : 𝕜) + (RCLike.ofReal ∘ hQ.isHermitian.eigenvalues) i) =
      ((∏ i, (1 + hQ.isHermitian.eigenvalues i) : ℝ) : 𝕜) := by
    rw [RCLike.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [this, RCLike.ofReal_re]
  exact Finset.one_le_prod₀ fun i _ => by linarith [hQ.eigenvalues_nonneg i]

theorem re_det_le_re_det_add {A P : Matrix n n 𝕜} (hA : A.PosSemidef) (hP : P.PosSemidef) :
    RCLike.re A.det ≤ RCLike.re (A + P).det := by
  by_cases h0 : A.det = 0
  · rw [h0, map_zero]
    exact re_det_nonneg (hA.add hP)
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose] at hB
  have hBdet : B.det ≠ 0 := by
    intro hb
    apply h0
    rw [hB, det_mul, hb, mul_zero]
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBHu : IsUnit Bᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hBdet)
  set Q := (B⁻¹)ᴴ * P * B⁻¹ with hQdef
  have hQ : Q.PosSemidef := by
    have := hP.mul_mul_conjTranspose_same ((B⁻¹)ᴴ)
    simpa [hQdef, conjTranspose_conjTranspose] using this
  have hAP : A + P = Bᴴ * (1 + Q) * B := by
    rw [hQdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← hB]
    congr 1
    rw [conjTranspose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hBHu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hBu, Matrix.mul_one]
  have hdet : (A + P).det = A.det * (1 + Q).det := by
    rw [hAP, hB, det_mul, det_mul, det_mul]
    ring
  have h1 := one_le_re_det_one_add hQ
  have h2 := re_det_nonneg hA
  obtain ⟨a, ha⟩ : ∃ a : ℝ, A.det = a := ⟨_, det_eq_ofReal_re hA⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (1 + Q).det = b := ⟨_, det_eq_ofReal_re (PosSemidef.one.add hQ)⟩
  rw [hdet, ha, hb, ← RCLike.ofReal_mul]
  simp only [RCLike.ofReal_re]
  rw [ha, RCLike.ofReal_re] at h2
  rw [hb, RCLike.ofReal_re] at h1
  nlinarith

theorem re_det_mono {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hAB : (B - A).PosSemidef) :
    RCLike.re A.det ≤ RCLike.re B.det := by
  have := re_det_le_re_det_add hA hAB
  rwa [add_sub_cancel] at this

end GroundTheory.Heights₂.Heights.MCDet
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Metric Real

noncomputable section

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det

def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Fin (g + g) → Fin g → ℂ :=
  Fin.append (fun k => Pi.single k 1) (fun k => τ *ᵥ Pi.single k 1)

def periodGram {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin (g + g)) (Fin (g + g)) ℝ :=
  Matrix.of fun i j => hermPair (τ.map Complex.im)⁻¹ (periodBasis τ i) (periodBasis τ j)

end

end GroundTheory.Heights₂.Heights
end

