module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1442
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1430
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDeterminantJensenChangeOfWeight
section
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.GramJensen

variable {S : Type} {Y : S → Type} [∀ σ, MeasurableSpace (Y σ)] {ι : Type} [Fintype ι] [DecidableEq ι]

def twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) : ∀ σ, Y σ → ι → ℂ :=
  fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)

def col (T : Matrix ι ι ℂ) (a : ι) : ι → ℂ := fun i => star (T i a)

theorem exp_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem cmb_twist (v : ∀ σ, Y σ → ι → ℂ) (w : ∀ σ, Y σ → ℝ) (c : ι → ℂ) (σ : S) (y : Y σ) :
    cmb (twist v w) c σ y = cmb v c σ y * Real.exp (-(w σ y)) := by
  have h : ∑ i, c i * twist v w σ y i = (∑ i, c i * v σ y i) * (Real.exp (-(w σ y) / 2) : ℝ) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; simp only [twist]; ring
  rw [cmb, cmb, h, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, exp_half_sq]

theorem cmb_nonneg (v : ∀ σ, Y σ → ι → ℂ) (c : ι → ℂ) (σ : S) (y : Y σ) : 0 ≤ cmb v c σ y := by
  unfold cmb; positivity

theorem exp_neg_le {C t : ℝ} (h : |t| ≤ C) : Real.exp (-t) ≤ Real.exp C :=
  Real.exp_le_exp.2 (by linarith [neg_le_abs t])

theorem exp_neg_ge {C t : ℝ} (h : |t| ≤ C) : Real.exp (-C) ≤ Real.exp (-t) :=
  Real.exp_le_exp.2 (by linarith [le_abs_self t])

variable {μ : ∀ σ, Measure (Y σ)} {v : ∀ σ, Y σ → ι → ℂ} {w : ∀ σ, Y σ → ℝ} {C : ℝ}

theorem isFam_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) := by
  refine ⟨h.finite, fun σ i j => ?_⟩
  have e : (fun y => twist v w σ y i * (starRingEnd ℂ) (twist v w σ y j)) =
      fun y => ((Real.exp (-(w σ y)) : ℝ) : ℂ) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    funext y
    simp only [twist, map_mul, Complex.conj_ofReal]
    rw [← exp_half_sq]; push_cast; ring
  rw [e]
  refine (h.integrable σ i j).bdd_mul (c := Real.exp C) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hw σ).neg)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact exp_neg_le (hC σ y)

theorem l2_twist_eq_finsum_integral_mul_exp_neg (c : ι → ℂ) :
    l2 μ (twist v w) c = ∑ᶠ σ, ∫ y, cmb v c σ y * Real.exp (-(w σ y)) ∂μ σ := by
  simp only [l2, cmb_twist]

theorem quad (M T : Matrix ι ι ℂ) (a : ι) :
    ∑ i, ∑ j, col T a i * (starRingEnd ℂ) (col T a j) * M i j = (Tᴴ * M * T) a a := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, col]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]; ring

theorem quad_vec (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, star x i * (starRingEnd ℂ) (star x j) * M i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

theorem exp_neg_bound_mul_l2_le_l2_twist (h : IsFam μ v) (hw : ∀ σ, Measurable (w σ)) (hC : ∀ σ y, |w σ y| ≤ C) (c : ι → ℂ) :
    Real.exp (-C) * l2 μ v c ≤ l2 μ (twist v w) c := by
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨-, hc⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [l2_twist_eq_finsum_integral_mul_exp_neg]
  simp only [l2, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_le_sum fun σ _ => ?_
  rw [← integral_const_mul]
  refine integral_mono (((hc c).1 σ).const_mul _) ?_ fun y => ?_
  · exact ((hc c).1 σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  · have h0 := cmb_nonneg v c σ y
    have h1 := exp_neg_ge (hC σ y)
    simp only
    nlinarith

theorem posDef_twist (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) : (gram μ (twist v w)).PosDef := by
  refine _root_.GlobalTheory.HSAmp.gram_posDef S Y ι μ _ (isFam_twist h hw hC) fun c hc0 => ?_
  by_contra hne
  have hx : star c ≠ 0 := fun h' => hne (by simpa using congrArg star h')
  have hpos := hG.dotProduct_mulVec_pos hx
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  rw [quad_vec, star_star, ← (hl c).2.2] at hpos
  have hp : 0 < l2 μ v c := by exact_mod_cast hpos
  have := exp_neg_bound_mul_l2_le_l2_twist h hw hC c
  rw [hc0] at this
  nlinarith [Real.exp_pos (-C)]

theorem jensen (hS : Finite S) (f : ∀ σ, Y σ → ℝ) (hf0 : ∀ σ y, 0 ≤ f σ y)
    (hfi : ∀ σ, Integrable (f σ) (μ σ)) (hf1 : ∑ᶠ σ, ∫ y, f σ y ∂μ σ = 1) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    Real.exp (-(∑ᶠ σ, ∫ y, w σ y * f σ y ∂μ σ)) ≤ ∑ᶠ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ := by
  haveI := Fintype.ofFinite S
  simp only [finsum_eq_sum_of_fintype] at hf1 ⊢
  obtain ⟨m, hm⟩ : ∃ m, m = ∑ σ, ∫ y, w σ y * f σ y ∂μ σ := ⟨_, rfl⟩
  rw [← hm]
  have hwi : ∀ σ, Integrable (fun y => w σ y * f σ y) (μ σ) := fun σ =>
    (hfi σ).bdd_mul (c := C) (hw σ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)
  have hei : ∀ σ, Integrable (fun y => f σ y * Real.exp (-(w σ y))) (μ σ) := fun σ =>
    (hfi σ).mul_bdd (c := Real.exp C) (Real.measurable_exp.comp (hw σ).neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact exp_neg_le (hC σ y))
  have pt : ∀ σ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ≤ f σ y * Real.exp (-(w σ y)) := by
    intro σ y
    have h1 := Real.add_one_le_exp (m - w σ y)
    have h2 : Real.exp (-m) * Real.exp (m - w σ y) = Real.exp (-(w σ y)) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-m) * (m - w σ y + 1) ≤ Real.exp (-(w σ y)) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (hf0 σ y)
    nlinarith
  have e : ∀ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ =
      Real.exp (-m) * ((1 + m) * ∫ y, f σ y ∂μ σ - ∫ y, w σ y * f σ y ∂μ σ) := by
    intro σ
    rw [integral_const_mul, integral_sub ((hfi σ).mul_const _) (hwi σ), integral_mul_const]; ring
  calc Real.exp (-m) = Real.exp (-m) * ((1 + m) * ∑ σ, ∫ y, f σ y ∂μ σ - ∑ σ, ∫ y, w σ y * f σ y ∂μ σ) := by
        rw [hf1, ← hm]; ring
    _ = ∑ σ, ∫ y, Real.exp (-m) * (f σ y * (1 + m) - w σ y * f σ y) ∂μ σ := by
        rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ ≤ ∑ σ, ∫ y, f σ y * Real.exp (-(w σ y)) ∂μ σ :=
        Finset.sum_le_sum fun σ _ => integral_mono ((((hfi σ).mul_const _).sub (hwi σ)).const_mul _) (hei σ) (pt σ)

theorem berg_sum (T : Matrix ι ι ℂ) (hT : Tᴴ * gram μ v * T = 1) (σ : S) (y : Y σ) :
    ∑ a, cmb v (col T a) σ y = bergmanDensity μ v σ y := by
  have hinv : (gram μ v)⁻¹ = T * Tᴴ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.mul_assoc]
    exact mul_eq_one_comm.1 hT
  have hn : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key : ((∑ a, cmb v (col T a) σ y : ℝ) : ℂ) =
      ∑ i, ∑ j, (gram μ v)⁻¹ j i * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
    have ha : ∀ a, ((cmb v (col T a) σ y : ℝ) : ℂ) =
        ∑ i, ∑ j, T j a * star (T i a) * (v σ y i * (starRingEnd ℂ) (v σ y j)) := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [cmb, hn, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [col, map_mul, Complex.star_def, Complex.conj_conj]; ring
    rw [hinv, Complex.ofReal_sum]
    simp only [ha, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [bergmanDensity, ← key, Complex.ofReal_re]

theorem jensen_gram (h : IsFam μ v) (hG : (gram μ v).PosDef) (hw : ∀ σ, Measurable (w σ))
    (hC : ∀ σ y, |w σ y| ≤ C) :
    IsFam μ (twist v w) ∧ (gram μ (twist v w)).PosDef ∧
      Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤
        Real.log (gram μ (twist v w)).det.re := by
  have hF := isFam_twist h hw hC
  have hG' := posDef_twist h hG hw hC
  refine ⟨hF, hG', ?_⟩
  have hS := h.finite
  haveI := Fintype.ofFinite S
  obtain ⟨T, d, -, hT, hT'⟩ := _root_.GlobalTheory.HSAmp.simultaneous_diagonalisation ι _ _ hG hG'.1
  obtain ⟨-, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v h
  obtain ⟨-, hl'⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ _ hF
  have hl1 : ∀ a, l2 μ v (col T a) = 1 := fun a => by
    have := (hl (col T a)).2.2
    rw [quad, hT, Matrix.one_apply_eq] at this; exact_mod_cast this
  have hld : ∀ a, l2 μ (twist v w) (col T a) = d a := fun a => by
    have := (hl' (col T a)).2.2
    rw [quad, hT', Matrix.diagonal_apply_eq] at this; exact_mod_cast this
  have hj : ∀ a, Real.exp (-(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ)) ≤ d a := fun a => by
    rw [← hld a, l2_twist_eq_finsum_integral_mul_exp_neg]
    exact jensen hS (cmb v (col T a)) (cmb_nonneg v _) (hl (col T a)).1 (hl1 a) hw hC
  have hd : ∀ a, 0 < d a := fun a => (Real.exp_pos _).trans_le (hj a)
  have hdet : (gram μ (twist v w)).det = (gram μ v).det * ∏ a, (d a : ℂ) := by
    have e1 := congrArg Matrix.det hT
    have e2 := congrArg Matrix.det hT'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at e2
    linear_combination (gram μ v).det * e2 - (gram μ (twist v w)).det * e1
  have hpos := Complex.pos_iff.1 (Matrix.PosDef.det_pos hG)
  have hre : (gram μ (twist v w)).det.re = (gram μ v).det.re * ∏ a, d a := by
    rw [hdet, ← Complex.ofReal_prod, Complex.re_mul_ofReal]
  rw [hre, Real.log_mul hpos.1.ne' (Finset.prod_pos fun a _ => hd a).ne', Real.log_prod fun a _ => (hd a).ne']
  have hsum : ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ = ∑ a, ∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ := by
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← integral_finsetSum Finset.univ fun a _ => ((hl (col T a)).1 σ).bdd_mul (c := C)
      (hw σ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC σ y)]
    congr 1; funext y; rw [← Finset.mul_sum, berg_sum T hT]
  have hlog : ∀ a, -(∑ᶠ σ, ∫ y, w σ y * cmb v (col T a) σ y ∂μ σ) ≤ Real.log (d a) := fun a => by
    have := Real.log_le_log (Real.exp_pos _) (hj a); rwa [Real.log_exp] at this
  rw [hsum]
  have := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hlog a
  rw [Finset.sum_neg_distrib] at this
  linarith

theorem gram_det_jensen : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).PosDef → ∀ (w : ∀ σ, Y σ → ℝ) (C : ℝ), (∀ σ, Measurable (w σ)) → (∀ σ y, |w σ y| ≤ C) → IsFam μ (fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)) ∧ (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).PosDef ∧ Real.log (gram μ v).det.re - ∑ᶠ σ, ∫ y, w σ y * bergmanDensity μ v σ y ∂μ σ ≤ Real.log (gram μ fun σ y i => v σ y i * (Real.exp (-(w σ y) / 2) : ℝ)).det.re := by
  intro S Y _ ι _ _ μ v h hG w C hw hC
  exact jensen_gram h hG hw hC

end GlobalTheory.GramJensen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasKernelOrderPPowerDegreeCompLeAdd
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_comp_le {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] (ψ : B →ₐc[k] A) (φ : C →ₐc[k] B) :
    Module.finrank k (A ⧸ kerIdeal (ψ.comp φ)) ≤
      Module.finrank k (A ⧸ kerIdeal ψ) * Module.finrank k (B ⧸ kerIdeal φ) := by
  have hHopf (X Y : Type) [CommRing X] [CommRing Y] [HopfAlgebra k X]
      [HopfAlgebra k Y] (f : Y →ₐc[k] X) : (kerIdeal f).IsHopfIdeal k := by
    refine {
    counit_eq_zero := by
      intro x hx
      exact (kerIdeal_le_ker_iff f (counitAlgHom k X)).2 (fun c => by simp) hx
    map_mkQ_comul_eq_zero := by
      intro x hx
      have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      have h : kerIdeal f ≤ RingHom.ker
          ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k X)) := by
        refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
        have key : ∀ t : Y ⊗[k] Y, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
            (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
            algebraMap k _ (counit (R := k)
              (TensorProduct.lid k Y (LinearMap.rTensor Y (counit (R := k) (A := Y)) t))) := by
          intro t
          induction t with
          | add x y hx hy => simp only [map_add (f := _), hx, hy]
          | tmul x y =>
            rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
              TensorProduct.lid_tmul, map_smul]
            erw [h0, h0]
            simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
              smul_smul, mul_comm]
        rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
          TensorProduct.lid_tmul, one_smul]
      exact h hx
    antipode_mem := by
      intro x hx
      have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k X) := by
        refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
        have ha' : counit (R := k) a = 0 := ha
        change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
        rw [← bialgHom_map_antipode]
        exact Ideal.mem_map_of_mem (f : Y →ₐ[k] X) (by simp [RingHom.mem_ker, ha'])
      exact h hx
    }
  haveI := hHopf A C (ψ.comp φ)
  haveI := hHopf B C φ
  let πA : A →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) := Bialgebra.Quotient.mkBialgHom (kerIdeal (ψ.comp φ))
  let πB : B →ₐc[k] B ⧸ kerIdeal φ := Bialgebra.Quotient.mkBialgHom (kerIdeal φ)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ c, πA (ψ (φ c)) = algebraMap k _ (counit c) :=
    (kerIdeal_le_ker_iff (ψ.comp φ) (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal φ ≤ RingHom.ker (πA.comp ψ : B →ₐ[k] A ⧸ kerIdeal (ψ.comp φ)) :=
    (kerIdeal_le_ker_iff φ _).2 fun c => hA c
  let m' : (B ⧸ kerIdeal φ) →ₐc[k] A ⧸ kerIdeal (ψ.comp φ) :=
    liftSurj πB hπB (πA.comp ψ) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : ∀ b, m' (πB b) = πA (ψ b) := fun b =>
    liftSurj_apply πB hπB (πA.comp ψ) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal (ψ.comp φ))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h0 := (kerIdeal_le_ker_iff m' (Ideal.Quotient.mkₐ k (kerIdeal m'))).1
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h4 : kerIdeal ψ ≤ RingHom.ker q := (kerIdeal_le_ker_iff ψ q).2 fun b => by
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (ψ b)) = _
    rw [← hm', h0, CoalgHomClass.counit_comp_apply]
  let q'' : (A ⧸ kerIdeal ψ) →ₐ[k] (A ⧸ kerIdeal (ψ.comp φ)) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal ψ) q h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace Dieu

theorem hasLogDeg_comp_le : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K) (a b c : ℕ),
    HasLogDeg f a → HasLogDeg g b → HasLogDeg (f ≫ g) c → c ≤ a + b := by
  intro p _ k _ _ G H K f g a b c ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ ⟨N₃, h₃⟩
  let n := max N₁ (max N₂ N₃)
  have e₁ := h₁ n (le_max_left _ _)
  have e₂ := h₂ n (le_trans (le_max_left _ _) (le_max_right _ _))
  have e₃ := h₃ n (le_trans (le_max_right _ _) (le_max_right _ _))
  have hle := finrank_quot_kerIdeal_comp_le (f.app n) (g.app n)
  rw [← comp_app, e₃, e₁, e₂, ← pow_add] at hle
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hle

end Dieu

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMul
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem trace_map_id {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (A : M →ₗ[ℂ] M) :
    LinearMap.trace ℂ (M ⊗[ℂ] W) (TensorProduct.map A LinearMap.id) =
      LinearMap.trace ℂ M A * Module.finrank ℂ W := by
  rw [GlobalTheory.trace_tensorProduct_map_complex, LinearMap.trace_id]

theorem trOn_forms_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  intro E _ _ _ hE n hn S hS lam K' hK f hf
  have hinj := _root_.GlobalTheory.BCT.TrKer.Phi_injective E hE n hn S hS lam K' hK
  have hrange : LinearMap.range (Phi S lam K') = forms S lam K' :=
    le_antisymm (_root_.GlobalTheory.BCT.TrKer.range_Phi_le_forms E hE n hn S hS lam K' hK) (_root_.GlobalTheory.BCT.TrKer.forms_le_range E hE n hn S hS lam K' hK)
  have hM := _root_.GlobalTheory.BCT.TrKer.HopStab.hopM_mem_vecM E n S lam K' hK f hf
  let A := (hopM S lam K' f).restrict hM
  have hcomm : ∀ x, hop S K' f (Phi S lam K' x) = Phi S lam K' (TensorProduct.map A LinearMap.id x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul F w =>
      rw [TensorProduct.map_tmul, Phi_tmul, Phi_tmul, GlobalTheory.T.unitaryHeckeOperator_commute_weightVectorFunction_explicit]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have hF : ∀ v ∈ forms S lam K', hop S K' f v ∈ forms S lam K' := by
    intro v hv
    rw [← hrange] at hv ⊢
    obtain ⟨x, rfl⟩ := hv
    exact ⟨_, (hcomm x).symm⟩
  obtain ⟨e, hev⟩ : ∃ e : (vecM S lam K' ⊗[ℂ] Wsp lam) ≃ₗ[ℂ] forms S lam K',
      ∀ y, ((e y : forms S lam K') : UA E n → ℂ) = Phi S lam K' y :=
    ⟨(LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange), fun y => rfl⟩
  have he : (hop S K' f).restrict hF = e.conj (TensorProduct.map A LinearMap.id) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv : (v : UA E n → ℂ) = Phi S lam K' (e.symm v) :=
      (congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (e.apply_symm_apply v)).symm.trans (hev _)
    calc (((hop S K' f).restrict hF v : forms S lam K') : UA E n → ℂ) = hop S K' f v :=
          LinearMap.restrict_coe_apply _ _ v
      _ = hop S K' f (Phi S lam K' (e.symm v)) := congrArg _ hv
      _ = Phi S lam K' (TensorProduct.map A LinearMap.id (e.symm v)) := hcomm _
      _ = ((e (TensorProduct.map A LinearMap.id (e.symm v)) : forms S lam K') : UA E n → ℂ) := (hev _).symm
      _ = ((e.conj (TensorProduct.map A LinearMap.id) v : forms S lam K') : UA E n → ℂ) :=
          congrArg (fun u : forms S lam K' => (u : UA E n → ℂ)) (LinearEquiv.conj_apply_apply _ _ _).symm
  have h1 : trOn (forms S lam K') (hop S K' f) = LinearMap.trace ℂ _ ((hop S K' f).restrict hF) := dif_pos hF
  have h2 : trOn (vecM S lam K') (hopM S lam K' f) = LinearMap.trace ℂ _ A := dif_pos hM
  rw [h1, h2]
  exact (congrArg (LinearMap.trace ℂ _) he).trans
    ((LinearMap.trace_conj' _ e).trans ((trace_map_id A).trans (mul_comm _ _)))

end GlobalTheory.BCT.TrKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTens
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefTens

theorem isNef_tens : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ L M : HermLB p, L.IsNef D → M.IsNef D → (L.tens M).IsNef D := by
  intro HC k _ X _ p D hX L M NL NM
  have HE := HC.arExists
  have hex (L : HermLB p) : ∃ h, L.IsArithHeight h := (HE k X p D hX).1 L
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  refine ⟨NL.semiPos.tens NM.semiPos, ?_, fun Z i _ _ _ hc hd => ?_⟩
  · intro Z i _ _ κ _ _ _ hd
    rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
    exact add_nonneg (NL.vertical Z i κ hd) (NM.vertical Z i κ hd)
  · obtain ⟨h, H⟩ := hex L
    obtain ⟨h', H'⟩ := hex M
    obtain ⟨h'', H''⟩ := hex (L.tens M)
    obtain ⟨r, hr⟩ := exists_isRatSec ((L.tens M).restr i).isLB
    obtain ⟨r₁, hr₁, h1⟩ := NL.horizontal Z i hc hd
    obtain ⟨r₂, hr₂, h2⟩ := NM.horizontal Z i hc hd
    refine ⟨r, hr, ?_⟩
    rw [← H''.point Z i hc hd r hr,
      PtHtComb.height_tens hX H H' H'' (HtSelfInter.isAlgPt_genericPoint i hc hd),
      H.point Z i hc hd r₁ hr₁, H'.point Z i hc hd r₂ hr₂]
    exact add_nonneg h1 h2

end GlobalTheory.NefTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSphericalOfHasSatGL
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TempSatUnr

open GlobalTheory.TempSat

theorem isSpherical_of_hasSatGL {E : Type} [Field E] [NumberField E] {a : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    {S : Multiset ℂˣ} (hS : GlobalTheory.LFun.HasSatGL w ρ S) : GlobalTheory.SmGL.IsSpherical ρ := by
  have hK : GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL w (n := a) :=
    GlobalTheory.SmGL.SphCompletion.KO_completion w a
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [hK]
  exact hS.1

end GlobalTheory.TempSatUnr
end
end

