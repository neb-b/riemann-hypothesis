module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartDensityIntegrableAlt

theorem exists_conjTranspose_mul_self {e : ℕ} {N : Matrix (Fin e) (Fin e) ℂ} (hN : N.PosDef) :
    ∃ C : Matrix (Fin e) (Fin e) ℂ, N = Cᴴ * C ∧ C.det ≠ 0 := by
  obtain ⟨U, l, hl, hspec⟩ : ∃ (U : Matrix (Fin e) (Fin e) ℂ) (l : Fin e → ℝ), (∀ k, 0 ≤ l k) ∧
      N = U * diagonal (fun k => (l k : ℂ)) * star U := by
    refine ⟨(hN.1.eigenvectorUnitary : Matrix (Fin e) (Fin e) ℂ), hN.1.eigenvalues,
      fun k => (hN.eigenvalues_pos k).le, ?_⟩
    have h := hN.1.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h
    exact h
  set s : Fin e → ℂ := fun k => ((Real.sqrt (l k) : ℝ) : ℂ) with hs
  have hss : (fun i => star s i * s i) = fun k => (l k : ℂ) := by
    funext k
    simp only [hs, Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hl k)]
  have hNC : N = (diagonal s * star U)ᴴ * (diagonal s * star U) := by
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose, diagonal_conjTranspose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal (star s)), diagonal_mul_diagonal, hss, hspec,
      star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨diagonal s * star U, hNC, fun h => ?_⟩
  have hdet := (hN.det_pos).ne'
  rw [hNC, det_mul, h, mul_zero] at hdet
  exact hdet rfl

theorem chart_quad_eq {e : ℕ} {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hH : M.IsHermitian)
    {C : Matrix (Fin e) (Fin e) ℂ} (hNC : M.submatrix Fin.succ Fin.succ = Cᴴ * C) {d : Fin e → ℂ}
    (hd : Cᴴ *ᵥ d = fun i => M i.succ 0) (y : Fin e → ℂ) :
    star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ (M *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (M 0 0 - star d ⬝ᵥ d) + star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) := by
  have h1 : star (C *ᵥ y + d) ⬝ᵥ (C *ᵥ y + d) =
      star y ⬝ᵥ ((Cᴴ * C) *ᵥ y) + star y ⬝ᵥ (Cᴴ *ᵥ d) + star (Cᴴ *ᵥ d) ⬝ᵥ y + star d ⬝ᵥ d := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec, dotProduct_mulVec (star d) C y]
    ring
  rw [h1, ← hNC, hd]
  have hw : ∀ j : Fin e, M 0 j.succ = star (M j.succ 0) := fun j => (hH.apply 0 j.succ).symm
  simp only [dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.star_apply, star_one,
    one_mul, mul_one, submatrix_apply, hw, mul_add, Finset.sum_add_distrib]
  ring

theorem re_star_dotProduct_self {e : ℕ} (z : Fin e → ℂ) : (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem hermChartPot_eq_gbPot_affine {e : ℕ} (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ∃ (c : Fin e → ℂ) (P : Matrix (Fin e) (Fin e) ℂ) (κ : ℝ), P.det ≠ 0 ∧
      hermChartPot M = fun y => gbPot (c + P *ᵥ y) + κ := by
  obtain ⟨C, hNC, hC⟩ := exists_conjTranspose_mul_self (hM.submatrix (Fin.succ_injective e))
  have hCH : Cᴴ.det ≠ 0 := by rw [det_conjTranspose]; exact star_ne_zero.mpr hC
  set w : Fin e → ℂ := fun i => M i.succ 0 with hw
  set d : Fin e → ℂ := (Cᴴ)⁻¹ *ᵥ w with hd'
  have hd : Cᴴ *ᵥ d = w := by
    rw [hd', mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hCH), one_mulVec]
  have hq := fun y => chart_quad_eq hM.1 hNC hd y
  set s : ℝ := (M 0 0 - star d ⬝ᵥ d).re with hs
  have hspos : 0 < s := by
    have hy0 : C *ᵥ (-(C⁻¹ *ᵥ d)) + d = 0 := by
      rw [mulVec_neg, mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC), one_mulVec, neg_add_cancel]
    have hx : (Fin.cons 1 (-(C⁻¹ *ᵥ d)) : Fin (e + 1) → ℂ) ≠ 0 := fun h => by
      have := congr_fun h 0
      simp at this
    have hpos := hM.re_dotProduct_pos hx
    rw [hq, hy0] at hpos
    simpa [hs] using hpos
  set r : ℝ := Real.sqrt s with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hspos
  refine ⟨((r⁻¹ : ℝ) : ℂ) • d, ((r⁻¹ : ℝ) : ℂ) • C, Real.log r, ?_, ?_⟩
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast (inv_pos.mpr hrpos).ne')) hC
  · funext y
    have hX : 0 ≤ ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hcy : ((r⁻¹ : ℝ) : ℂ) • d + (((r⁻¹ : ℝ) : ℂ) • C) *ᵥ y = ((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d) := by
      rw [smul_mulVec, smul_add, add_comm]
    have hnorm : ∑ i, ‖(((r⁻¹ : ℝ) : ℂ) • (C *ᵥ y + d)) i‖ ^ 2 = (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hrpos), mul_pow]
    have hsq : s = r ^ 2 := (Real.sq_sqrt hspos.le).symm
    have h1pos : 0 < 1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 := by positivity
    have hsplit : s + ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2 = r ^ 2 * (1 + (r⁻¹) ^ 2 * ∑ i, ‖(C *ᵥ y + d) i‖ ^ 2) := by
      rw [hsq]; field_simp
    simp only [hermChartPot, gbPot]
    rw [hq, Complex.add_re, ← hs, re_star_dotProduct_self, hcy, hnorm, hsplit,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le,
      Real.log_mul hrpos.ne' (Real.sqrt_pos.mpr h1pos).ne']
    ring

theorem integrable_fsDens (D : ℕ) :
    Integrable (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
  have hcont : Continuous (fun y : Fin D → ℂ => ((1 + ∑ i, ‖y i‖ ^ 2) ^ (D + 1))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
    positivity
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by
    simp only [Pi.zero_apply]; positivity)]
  have h := gaM_lintegral_pi D 1 one_pos 0
  simp only [add_zero] at h
  rw [h]
  exact ENNReal.ofReal_lt_top

theorem integrable_comp_affine {D : ℕ} {f : (Fin D → ℂ) → ℝ} (hf : Integrable f) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : Integrable (fun y => f (c + P *ᵥ y)) := by
  set L := ChartMongeAmpereAffineInvariance.realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)))
    (by rw [ChartMongeAmpereAffineInvariance.det_realCLE]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe] at hmap
  have hg : Integrable (fun w => f (c + w)) (Measure.map L volume) := by
    rw [hmap]
    exact (hf.comp_add_left c).smul_measure ENNReal.ofReal_ne_top
  exact L.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hg

end ChartDensityIntegrableAlt


open ChartDensityIntegrableAlt in
theorem ChartDensityIntegrable.proof : ChartDensityIntegrable.Statement := by
  intro e M hM
  obtain ⟨c, P, κ, hP, hpot⟩ := hermChartPot_eq_gbPot_affine M hM
  have h : (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y) = fun y =>
      (Complex.normSq P.det * ((e.factorial : ℝ) / Real.pi ^ e)) *
        ((1 + ∑ i, ‖(c + P *ᵥ y) i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [hpot, ChartMongeAmpereAffineInvariance.maDensity_comp_affine gbPot c P hP κ y, maDensity_gbPot]
    ring
  rw [h]
  exact (integrable_comp_affine (integrable_fsDens e) c P hP).const_mul _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCongruence

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_star_mul_self {U : Matrix n n ℂ} (hU : star U * U = 1) : U.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hU
  rw [det_mul, h, mul_zero, det_one] at this
  exact zero_ne_one this

theorem exists_congr_eq_one {N : Matrix n n ℂ} (hN : N.PosDef) :
    ∃ C : Matrix n n ℂ, C.det ≠ 0 ∧ Cᴴ * N * C = 1 := by
  set U : Matrix n n ℂ := (hN.1.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set μ := hN.1.eigenvalues
  set d : n → ℂ := fun j => (((Real.sqrt (μ j))⁻¹ : ℝ) : ℂ) with hd
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hN' : N = U * diagonal (fun j => (μ j : ℂ)) * star U := hN.1.spectral_theorem
  have hμ : ∀ j, 0 < μ j := hN.eigenvalues_pos
  refine ⟨U * diagonal d, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine mul_ne_zero (det_ne_zero_of_star_mul_self hU) (Finset.prod_ne_zero_iff.mpr fun j _ => ?_)
    have := Real.sqrt_pos.mpr (hμ j)
    simp only [hd, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact this.ne'
  · have hstar : Uᴴ = star U := rfl
    rw [hN', conjTranspose_mul, diagonal_conjTranspose, hstar]
    calc diagonal (star d) * star U * (U * diagonal (fun j => (μ j : ℂ)) * star U) * (U * diagonal d)
        = diagonal (star d) * (star U * U) * diagonal (fun j => (μ j : ℂ)) * (star U * U) * diagonal d := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU, Matrix.mul_one, Matrix.mul_one, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext j
          have hs := Real.sqrt_pos.mpr (hμ j)
          have hsq := Real.sq_sqrt (hμ j).le
          simp only [hd, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
          congr 1
          field_simp
          linarith

theorem det_congr (C X : Matrix n n ℂ) :
    (Cᴴ * X * C).det = (Complex.normSq C.det : ℂ) * X.det := by
  rw [det_mul, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end ChartEnergyCongruence


open ChartEnergyCongruence in
theorem ChartEnergy.proof (hI : ChartEnergyLinearInvariant.Statement) (hD : ChartEnergyDiagonal.Statement) :
    ChartEnergy.Statement := by
  intro e M N hM hN
  obtain ⟨C, hC, hCN⟩ := exists_congr_eq_one hN
  have hCu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)
  have hM' : (Cᴴ * M * C).PosDef := hM.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hCu)
  set M' := Cᴴ * M * C with hM'def
  set V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := (hM'.1.eigenvectorUnitary : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
  set Λ := hM'.1.eigenvalues
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVd : V.det ≠ 0 := det_ne_zero_of_star_mul_self hVV
  have hdiag : Vᴴ * M' * V = diagonal (fun j => (Λ j : ℂ)) := by
    have := hM'.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    exact this
  have hone : Vᴴ * 1 * V = 1 := by rw [Matrix.mul_one]; exact hVV
  have hterm : ∀ k, chartMixedEnergy M N k = chartMixedEnergy (diagonal fun j => (Λ j : ℂ)) 1 k := by
    intro k
    rw [← hI e M N C hM hN hC k, hCN, ← hI e M' 1 V hM' PosDef.one hVd k, hdiag, hone]
  rw [Finset.sum_congr rfl fun k _ => hterm k, hD e Λ hM'.eigenvalues_pos]

  have hMpos := (Complex.pos_iff.mp hM.det_pos).1
  have hNpos := (Complex.pos_iff.mp hN.det_pos).1
  have hns : 0 < Complex.normSq C.det := Complex.normSq_pos.mpr hC
  have hM're : M'.det.re = Complex.normSq C.det * M.det.re := by
    rw [hM'def, det_congr, Complex.re_ofReal_mul]
  have hN're : 1 = Complex.normSq C.det * N.det.re := by
    have := congrArg Complex.re (det_congr C N)
    rw [hCN, det_one, Complex.one_re, Complex.re_ofReal_mul] at this
    exact this
  have hprod : M'.det.re = ∏ j, Λ j := by
    rw [hM'.1.det_eq_prod_eigenvalues]
    change (∏ j, ((Λ j : ℝ) : ℂ)).re = _
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have hlog : ∑ j, Real.log (Λ j) = Real.log M.det.re - Real.log N.det.re := by
    rw [← Real.log_prod fun j _ => (hM'.eigenvalues_pos j).ne', ← hprod, hM're,
      Real.log_mul hns.ne' hMpos.ne']
    have h1 : Real.log (Complex.normSq C.det) + Real.log N.det.re = 0 := by
      rw [← Real.log_mul hns.ne' hNpos.ne', ← hN're, Real.log_one]
    linarith
  rw [hlog]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyDiagonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDiagonalAlt

def diagEnergy {e : ℕ} (l : Fin (e + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (e + 1),
    chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k

theorem diag_posDef {e : ℕ} {l : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

theorem diag_congr {e : ℕ} (s d : Fin (e + 1) → ℝ) :
    (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (d j : ℂ)) *
        Matrix.diagonal (fun j => (s j : ℂ)) =
      Matrix.diagonal fun j => ((s j * d j * s j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem diagEnergy_mul (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {l l' : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) (hl' : ∀ j, 0 < l' j) :
    diagEnergy (l * l') = diagEnergy l + diagEnergy l' := by
  have hll' : ∀ j, 0 < (l * l') j := fun j => mul_pos (hl j) (hl' j)
  set s : Fin (e + 1) → ℝ := fun j => (Real.sqrt (l' j))⁻¹ with hs
  have hss : ∀ j, s j * s j * l' j = 1 := fun j => by
    simp only [hs]
    rw [← mul_inv, Real.mul_self_sqrt (hl' j).le, inv_mul_cancel₀ (hl' j).ne']
  have hsd : (Matrix.diagonal fun j => (s j : ℂ)).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have : (Real.sqrt (l' j)) ≠ 0 := (Real.sqrt_pos.mpr (hl' j)).ne'
    simpa [hs] using this
  have h1 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => ((l * l') j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = Matrix.diagonal fun j => (l j : ℂ) := by
    rw [diag_congr]
    congr 1
    funext j
    congr 1
    simp only [Pi.mul_apply]
    linear_combination (l j) * hss j
  have h2 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (l' j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = 1 := by
    rw [diag_congr, ← diagonal_one]
    congr 1
    funext j
    rw [show s j * l' j * s j = 1 by linarith [hss j]]
    simp
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => ((l * l') j : ℂ))
      (Matrix.diagonal fun j => (l' j : ℂ)) k = chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ _ (diag_posDef hll') (diag_posDef hl') hsd k, h1, h2]
  unfold diagEnergy
  rw [hC e _ (Matrix.diagonal fun j => (l' j : ℂ)) 1 (diag_posDef hll') (diag_posDef hl') PosDef.one,
    Finset.sum_congr rfl fun k _ => hterm k]

theorem diagEnergy_perm (hI : ChartEnergyLinearInvariant.Statement) {e : ℕ} {l : Fin (e + 1) → ℝ}
    (hl : ∀ j, 0 < l j) (σ : Equiv.Perm (Fin (e + 1))) : diagEnergy (l ∘ σ) = diagEnergy l := by
  set C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := σ.symm.toPEquiv.toMatrix with hCdef
  have hCH : Cᴴ = σ.toPEquiv.toMatrix := by
    ext i j
    rw [hCdef, conjTranspose_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.symm_apply_eq]
    by_cases h : σ i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hconj : ∀ A : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, Cᴴ * A * C = A.submatrix σ σ := by
    intro A
    rw [hCH, PEquiv.toMatrix_toPEquiv_mul, hCdef, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
    rfl
  have hCd : C.det ≠ 0 := by
    rw [hCdef, show (σ.symm.toPEquiv.toMatrix : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      Equiv.Perm.permMatrix ℂ σ.symm from rfl, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k =
      chartMixedEnergy (Matrix.diagonal fun j => ((l ∘ σ) j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ C (diag_posDef hl) PosDef.one hCd k, hconj, hconj, submatrix_diagonal_equiv,
      submatrix_one_equiv]
    rfl
  unfold diagEnergy
  exact (Finset.sum_congr rfl fun k _ => hterm k).symm

theorem cxHessian_add_const {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    cxHessian (fun y => φ y + κ) = cxHessian φ := by
  have h : fderiv ℝ (fun y => φ y + κ) = fderiv ℝ φ := funext fun x => fderiv_add_const κ
  funext z
  unfold cxHessian
  simp only [h]
  rfl

theorem maDensity_congr {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (h : ∀ j, cxHessian (φ j) = cxHessian (ψ j))
    (z : Fin D → ℂ) : maDensity φ z = maDensity ψ z := by
  unfold maDensity
  simp only [h]

theorem hermChartPot_const {e : ℕ} {c : ℝ} (hc : 0 < c) (y : Fin e → ℂ) :
    hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) y =
      hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c := by
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hv0 : v ≠ 0 := fun h => by
    have := congr_fun h 0
    simp [hv] at this
  have hx : 0 < (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re :=
    PosDef.one.re_dotProduct_pos hv0
  have hq : (star v ⬝ᵥ ((Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) *ᵥ v)).re =
      c * (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re := by
    rw [← smul_one_eq_diagonal, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  unfold hermChartPot
  rw [← hv, hq, Real.sqrt_mul hc.le, Real.log_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hx).ne',
    Real.log_sqrt hc.le]
  ring

theorem diagEnergy_const {e : ℕ} {c : ℝ} (hc : 0 < c) :
    diagEnergy (fun _ : Fin (e + 1) => c) =
      (e + 1) * (1 / 2 * Real.log c) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have hpot : hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) =
      fun y => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c :=
    funext (hermChartPot_const hc)
  have hk : ∀ k, chartMixedEnergy (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) 1 k =
      1 / 2 * Real.log c * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
    intro k
    have hd : ∀ y, maDensity (fun j : Fin e => if (j : ℕ) < k then
        hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ))
        else hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y =
        maDensity (fun _ : Fin e => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y := by
      refine maDensity_congr _ _ fun j => ?_
      split_ifs
      · rw [hpot, cxHessian_add_const]
      · rfl
    unfold chartMixedEnergy chartMass
    simp_rw [hd]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [hpot]
    ring
  unfold diagEnergy
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem diagEnergy_one {e : ℕ} : diagEnergy (1 : Fin (e + 1) → ℝ) = 0 := by
  calc diagEnergy (1 : Fin (e + 1) → ℝ) = diagEnergy (fun _ : Fin (e + 1) => (1 : ℝ)) := rfl
    _ = 0 := by rw [diagEnergy_const one_pos, Real.log_one]; ring

theorem diagEnergy_prod (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Fin (e + 1) → ℝ) (hf : ∀ t j, 0 < f t j) :
    diagEnergy (∏ t ∈ s, f t) = ∑ t ∈ s, diagEnergy (f t) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact diagEnergy_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      diagEnergy_mul hI hC (hf a) (fun j => by rw [Finset.prod_apply]; exact Finset.prod_pos fun t _ => hf t j),
      ih]

end ChartEnergyDiagonalAlt


open ChartEnergyDiagonalAlt in
theorem ChartEnergyDiagonal.proof (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement) :
    ChartEnergyDiagonal.Statement := by
  intro e l hl
  change diagEnergy l = _
  set f : Fin (e + 1) → Fin (e + 1) → ℝ := fun t => l ∘ (Equiv.addRight t) with hf
  have hfpos : ∀ t j, 0 < f t j := fun t j => hl _
  have hprod : (∏ t, f t) = fun _ => ∏ j, l j := by
    funext i
    rw [Finset.prod_apply]
    exact Equiv.prod_comp (Equiv.addLeft i) l
  have key := diagEnergy_prod hI hC Finset.univ f hfpos
  rw [hprod, diagEnergy_const (Finset.prod_pos fun j _ => hl j),
    Finset.sum_congr rfl fun t _ => diagEnergy_perm hI hl (Equiv.addRight t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.log_prod (fun j _ => (hl j).ne')] at key
  push_cast at key
  have he : (0 : ℝ) < e + 1 := by positivity
  have h2 : ((e : ℝ) + 1) * (diagEnergy l - 1 / 2 * (∑ j, Real.log (l j)) *
      chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) = 0 := by
    linear_combination -key
  have := (mul_eq_zero.mp h2).resolve_left he.ne'
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSemipositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem FsLineSemipositive.proof (h₁ : FsLineSmooth.Statement) (h₂ : FsLineLevi.Statement) :
    FsLineSemipositive.Statement := by
  intro K _ ι _ P
  exact ⟨h₁ K ι, fun z hz w _ => h₂ K ι z w hz.1⟩

end GroundTheory.Heights₂.Heights
end

