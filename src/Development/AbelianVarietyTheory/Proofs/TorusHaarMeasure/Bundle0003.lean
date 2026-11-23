module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetFromColsEqZero
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

namespace GramSubmodular

variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]


end GramSubmodular

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_re_nonneg_and_im_eq_zero (X : Matrix m α ℂ) : 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
  have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
  exact ⟨by simpa using h.1, by simpa using h.2.symm⟩

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_fromCols_eq_fromBlocks (X : Matrix m α ℂ) (N : Matrix m n ℂ) :
    (fromCols X N)ᴴ * fromCols X N = fromBlocks (Xᴴ * X) (Xᴴ * N) (Nᴴ * X) (Nᴴ * N) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_projection_residual_eq [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N) =
      Nᴴ * N - Nᴴ * X * (Xᴴ * X)⁻¹ * (Xᴴ * N) := by
  have hG : (Xᴴ * X)⁻¹ᴴ = (Xᴴ * X)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGG : (Xᴴ * X)⁻¹ * (Xᴴ * X) = 1 := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)
  have hQ : X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) = X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [show X * (Xᴴ * X)⁻¹ * Xᴴ * (X * (Xᴴ * X)⁻¹ * Xᴴ) =
      X * ((Xᴴ * X)⁻¹ * (Xᴴ * X)) * (Xᴴ * X)⁻¹ * Xᴴ by simp only [Matrix.mul_assoc], hGG,
      Matrix.mul_one]
  have hP : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * (1 - X * (Xᴴ * X)⁻¹ * Xᴴ) =
      1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [sub_mul, mul_sub, mul_sub, hQ]
    simp only [Matrix.one_mul, Matrix.mul_one]
    abel
  have hPh : (1 - X * (Xᴴ * X)⁻¹ * Xᴴ)ᴴ = 1 - X * (Xᴴ * X)⁻¹ * Xᴴ := by
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, hG, Matrix.mul_assoc]
  rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ N, hP]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_eq_mul_residual [DecidableEq m] (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det ≠ 0) :
    ((fromCols X N)ᴴ * fromCols X N).det = (Xᴴ * X).det *
      (((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)ᴴ * ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * N)).det := by
  haveI := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr h)
  rw [gram_fromCols_eq_fromBlocks, det_fromBlocks₁₁, invOf_eq_nonsing_inv, gram_projection_residual_eq X N h]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma re_mul_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) : (z * w).re = z.re * w.re := by
  simp [Complex.mul_re, hz]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_eq_zero_of_gram_det_eq_zero (X : Matrix m α ℂ) (N : Matrix m n ℂ)
    (h : (Xᴴ * X).det = 0) : ((fromCols X N)ᴴ * fromCols X N).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
  have hXv : X *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero X v).mp hv
  refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, fun hw => hv0 ?_, ?_⟩
  · funext a
    simpa using congrFun hw (Sum.inl a)
  · rw [conjTranspose_mul_self_mulVec_eq_zero, fromCols_mulVec]
    simp [Function.comp_def, hXv]
    exact N.mulVec_zero

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_fromCols_le_mul
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    ((fromCols Y Z)ᴴ * fromCols Y Z).det.re ≤ (Yᴴ * Y).det.re * (Zᴴ * Z).det.re := by
  classical
  by_cases h : (Yᴴ * Y).det = 0
  · rw [gram_det_fromCols_eq_zero_of_gram_det_eq_zero Y Z h, h]
    simp
  · rw [gram_det_fromCols_eq_mul_residual Y Z h, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero Y).2]
    refine mul_le_mul_of_nonneg_left ?_ (gram_det_re_nonneg_and_im_eq_zero Y).1
    have hQ : ((Yᴴ * Z)ᴴ * (Yᴴ * Y)⁻¹ * (Yᴴ * Z)).PosSemidef :=
      (posSemidef_conjTranspose_mul_self Y).inv.conjTranspose_mul_mul_same _
    have hmono' := (hmono γ _ _ (posSemidef_conjTranspose_mul_self
      ((1 - Y * (Yᴴ * Y)⁻¹ * Yᴴ) * Z)) hQ).2.1
    refine hmono'.trans (le_of_eq ?_)
    rw [gram_projection_residual_eq Y Z h, conjTranspose_mul, conjTranspose_conjTranspose, sub_add_cancel]

open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
private lemma gram_det_koteljanskii_inequality
    (hmono : ∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0))
    (X : Matrix m α ℂ) (Y : Matrix m β ℂ) (Z : Matrix m γ ℂ) :
    (Xᴴ * X).det.re * ((fromCols X (fromCols Y Z))ᴴ * fromCols X (fromCols Y Z)).det.re ≤
      ((fromCols X Y)ᴴ * fromCols X Y).det.re * ((fromCols X Z)ᴴ * fromCols X Z).det.re := by
  classical
  by_cases h : (Xᴴ * X).det = 0
  · rw [h]
    simpa using mul_nonneg (gram_det_re_nonneg_and_im_eq_zero (fromCols X Y)).1 (gram_det_re_nonneg_and_im_eq_zero (fromCols X Z)).1
  · rw [gram_det_fromCols_eq_mul_residual X _ h, gram_det_fromCols_eq_mul_residual X Y h, gram_det_fromCols_eq_mul_residual X Z h, mul_fromCols,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2, re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2,
      re_mul_of_im_eq_zero (gram_det_re_nonneg_and_im_eq_zero X).2]
    have hF := gram_det_fromCols_le_mul hmono ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Y)
      ((1 - X * (Xᴴ * X)⁻¹ * Xᴴ) * Z)
    nlinarith [mul_le_mul_of_nonneg_left hF (mul_self_nonneg (Xᴴ * X).det.re)]


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
variable {m α β γ n : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [Fintype n]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq n] in
theorem _root_.GlobalTheory.gram_det_submodular :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) := by
  intro hmono m α β γ _ _ _ _ _ _ _ M
  have key := gram_det_koteljanskii_inequality hmono (M.submatrix id Sum.inl)
    (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))
  have hM : fromCols (M.submatrix id Sum.inl)
      (fromCols (M.submatrix id (Sum.inr ∘ Sum.inl)) (M.submatrix id (Sum.inr ∘ Sum.inr))) = M := by
    ext x (a | b | c) <;> rfl
  have hXY : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inl)) =
      M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) := by
    ext x (a | b) <;> rfl
  have hXZ : fromCols (M.submatrix id Sum.inl) (M.submatrix id (Sum.inr ∘ Sum.inr)) =
      M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ) := by
    ext x (a | c) <;> rfl
  rwa [hM, hXY, hXZ] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetRePosIffInjective
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.sum_log_gramDet_ratio_pos : (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hCS r S hS hirr i hi0 hir M hM
  have hG0 : ∀ X : Matrix (Fin r) (Fin i) ℂ, 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
    intro X
    have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hnorm : ∀ X : Matrix (Fin r) (Fin i) ℂ, ‖(Xᴴ * X).det‖ = (Xᴴ * X).det.re := by
    intro X
    have h : (Xᴴ * X).det = (((Xᴴ * X).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hG0 X).2])
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by simpa using (hG0 X).1)]
    simp
  have hunit : ∀ a ∈ S, IsUnit a.det := fun a ha => isUnit_iff_ne_zero.mpr (hS a ha).2.1
  have hmul : ∀ a ∈ S, (a * M)ᴴ * (a⁻¹ * M) = Mᴴ * M := by
    intro a ha
    rw [conjTranspose_mul, (hS a ha).1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc a,
      mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
  have hpair : ∀ a ∈ S, ((Mᴴ * M).det.re) ^ 2 ≤
      ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re := by
    intro a ha
    have h := (hCS (Fin r) (Fin i) (a * M) (a⁻¹ * M)).1
    rwa [hmul a ha, hnorm] at h
  have hMsq : 0 < ((Mᴴ * M).det.re) ^ 2 := pow_pos hM 2
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    refine lt_of_le_of_ne (hG0 _).1 fun h => ?_
    have h' := hpair a ha
    rw [← h, zero_mul] at h'
    linarith
  refine ⟨hpos, ?_⟩
  have hinvinv : ∀ a ∈ S, a⁻¹⁻¹ = a := fun a ha => nonsing_inv_nonsing_inv a (hunit a ha)
  have hsum_inv : ∑ a ∈ S, Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) :=
    Finset.sum_nbij' (·⁻¹) (·⁻¹) (fun a ha => (hS a ha).2.2) (fun a ha => (hS a ha).2.2)
      (fun a ha => hinvinv a ha) (fun a ha => hinvinv a ha) (fun a _ => rfl)
  have hterm : ∀ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      Real.log (((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re /
        ((Mᴴ * M).det.re) ^ 2) := by
    intro a ha
    rw [← Real.log_mul (div_pos (hpos a ha) hM).ne' (div_pos (hpos _ (hS a ha).2.2) hM).ne']
    congr 1
    field_simp
  have hnonneg : ∀ a ∈ S, 0 ≤ Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    intro a ha
    rw [hterm a ha]
    exact Real.log_nonneg ((one_le_div hMsq).mpr (hpair a ha))
  have hstrict : ∃ a ∈ S, 0 < Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    by_contra hcon
    push_neg at hcon
    have hle : ∀ a ∈ S, ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re ≤
        ((Mᴴ * M).det.re) ^ 2 := by
      intro a ha
      refine (div_le_one hMsq).mp (not_lt.mp fun h => ?_)
      have h' := hcon a ha
      rw [hterm a ha] at h'
      exact absurd h' (not_le.mpr (Real.log_pos h))
    have hdet : (Mᴴ * M).det ≠ 0 := by
      intro h
      rw [h] at hM
      simp at hM
    have hcol : ∀ a ∈ S, ∃ C : Matrix (Fin i) (Fin i) ℂ, a * a * M = M * C := by
      intro a ha
      have ha' := (hS a ha).2.2
      have h := (hCS (Fin r) (Fin i) (a⁻¹ * M) (a⁻¹⁻¹ * M)).2
      rw [hmul _ ha', hnorm] at h
      obtain ⟨C, hC⟩ := h hdet (hle _ ha')
      rw [hinvinv a ha] at hC
      refine ⟨C, ?_⟩
      rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
    have hW : ∀ a ∈ S, ∀ v ∈ LinearMap.range (Matrix.mulVecLin M), (a * a).mulVec v ∈
        LinearMap.range (Matrix.mulVecLin M) := by
      rintro a ha v ⟨w, rfl⟩
      obtain ⟨C, hC⟩ := hcol a ha
      refine ⟨C *ᵥ w, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hC]
    rcases hirr _ hW with h | h
    · have hM0 : M = 0 := by
        ext x l
        have h2 := congrArg (fun f => f (Pi.single l 1) x) (LinearMap.range_eq_bot.mp h)
        simpa [Matrix.mulVecLin_apply] using h2
      haveI : Nonempty (Fin i) := ⟨⟨0, hi0⟩⟩
      rw [hM0] at hM
      simp at hM
    · have h1 := LinearMap.finrank_range_le (Matrix.mulVecLin M)
      rw [h, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
      omega
  have htot : 0 < ∑ a ∈ S, (Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re))) :=
    Finset.sum_pos' hnonneg hstrict
  rw [Finset.sum_add_distrib, hsum_inv] at htot
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_of_conj_inv :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) := by
  intro G _ _ _ _ _ _ _ _ ν _ h k hk
  have e : h * (k * h) = k := by rw [hk, mul_inv_cancel_left]
  have e2 := congrArg Measure.modularCharacterFun e
  rw [Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul] at e2
  have hk0 : (0 : ℝ) < Measure.modularCharacterFun k := Measure.modularCharacterFun_pos k
  have hh0 : (0 : ℝ) < Measure.modularCharacterFun h := Measure.modularCharacterFun_pos h
  have e3 : (Measure.modularCharacterFun h : ℝ) *
      ((Measure.modularCharacterFun k : ℝ) * Measure.modularCharacterFun h) =
      Measure.modularCharacterFun k := by exact_mod_cast e2
  have e4 : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h = 1 := by
    apply mul_left_cancel₀ hk0.ne'
    linarith
  have e5 : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  have e6 : Measure.modularCharacterFun h = 1 := by exact_mod_cast e5
  have hm : ν.map (fun g => g * h) = Measure.modularCharacterFun h • ν := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν h]
    exact Measure.isMulLeftInvariant_eq_smul _ ν
  rw [hm, e6, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem measure_univ_le_two_mul_sublevel_of_drift :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y)
      (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) →
      (∀ s y y', R y y' → R (t s y) (t s y')) →
      (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') →
        ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) →
      Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b →
      (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) →
      ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) := by
  intro Y σ _ _ _ μ R t f c b ht hR hinv hf hf0 hfR hc0 hc1 hb hdrift
  classical
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨K, hK, hK0⟩ : ∃ K : ℝ, b = K * (1 - c) ∧ 0 ≤ K :=
    ⟨b / (1 - c), by field_simp, div_nonneg hb h1c.le⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * K + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  refine ⟨M, ?_⟩
  have hN : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hA : MeasurableSet {y | f y ≤ M} := measurableSet_le hf measurable_const
  let g : ℕ → Y → ℝ := fun n =>
    Nat.rec (fun y => if f y ≤ M then 1 else 0)
      (fun _ h y => (Fintype.card σ : ℝ)⁻¹ * ∑ s, h (t s y)) n
  have g0 : ∀ y, g 0 y = if f y ≤ M then 1 else 0 := fun y => rfl
  have gs : ∀ n y, g (n + 1) y = (Fintype.card σ : ℝ)⁻¹ * ∑ s, g n (t s y) := fun n y => rfl
  clear_value g
  have gmeas : ∀ n, Measurable (g n) := by
    intro n
    induction n with
    | zero =>
      rw [show g 0 = _ from funext g0]
      exact Measurable.ite hA measurable_const measurable_const
    | succ n ih =>
      rw [show g (n + 1) = _ from funext (gs n)]
      exact measurable_const.mul (Finset.measurable_sum _ fun s _ => ih.comp (ht s))
  have gnn : ∀ n y, 0 ≤ g n y := by
    intro n
    induction n with
    | zero => intro y; rw [g0]; split_ifs <;> norm_num
    | succ n ih =>
      intro y; rw [gs]
      exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun s _ => ih _)
  have gR : ∀ n y y', R y y' → g n y = g n y' := by
    intro n
    induction n with
    | zero => intro y y' h; rw [g0, g0, hfR y y' h]
    | succ n ih =>
      intro y y' h; rw [gs, gs]
      congr 1
      exact Finset.sum_congr rfl fun s _ => ih _ _ (hR s _ _ h)
  have gint : ∀ n, ∫⁻ y, ENNReal.ofReal (g n y) ∂μ = μ {y | f y ≤ M} := by
    intro n
    induction n with
    | zero =>
      rw [← lintegral_indicator_one hA]
      refine lintegral_congr fun y => ?_
      rw [g0]
      by_cases h : f y ≤ M <;> simp [h, Set.indicator]
    | succ n ih =>
      have hm : Measurable fun y => ENNReal.ofReal (g n y) := (gmeas n).ennreal_ofReal
      have e : ∀ y, ENNReal.ofReal (g (n + 1) y) =
          (Fintype.card σ : ℝ≥0∞)⁻¹ * ∑ s, ENNReal.ofReal (g n (t s y)) := by
        intro y
        rw [gs, ENNReal.ofReal_mul (inv_nonneg.2 hN.le), ENNReal.ofReal_inv_of_pos hN,
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun s _ => gnn n _]
      simp_rw [e]
      have hN0 : (Fintype.card σ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      have hms : ∀ s, Measurable fun y => ENNReal.ofReal (g n (t s y)) :=
        fun s => hm.comp (ht s)
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun s _ => hms s),
        MeasureTheory.lintegral_finsetSum _ fun s _ => hms s]
      have : ∀ s, ∫⁻ y, ENNReal.ofReal (g n (t s y)) ∂μ = μ {y | f y ≤ M} := fun s => by
        rw [← ih]
        exact hinv (fun y => ENNReal.ofReal (g n y)) hm
          (fun y y' h => by simp only [gR n y y' h]) s
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _), one_mul]
  have glow : ∀ n y, M - (c ^ n * f y + K * (1 - c ^ n)) ≤ M * g n y := by
    intro n
    induction n with
    | zero =>
      intro y; rw [g0]
      have := hf0 y
      split_ifs with h
      · simp [this]
      · simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero]
        linarith [not_le.1 h]
    | succ n ih =>
      intro y
      have hcn : 0 ≤ c ^ n := pow_nonneg hc0 n
      have h1 : ∑ s, (M - (c ^ n * f (t s y) + K * (1 - c ^ n))) ≤ ∑ s, M * g n (t s y) :=
        Finset.sum_le_sum fun s _ => ih _
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at h1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hdrift y) hcn
      rw [gs, mul_left_comm, le_inv_mul_iff₀ hN, pow_succ]
      rw [hK] at h2
      rw [← Finset.mul_sum] at h1
      nlinarith
  have hlim : ∀ y, (2⁻¹ : ℝ≥0∞) ≤
      Filter.liminf (fun n => ENNReal.ofReal (g n y)) Filter.atTop := by
    intro y
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    have h0 : Filter.Tendsto (fun n : ℕ => c ^ n * f y) Filter.atTop (𝓝 (0 * f y)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const _
    rw [zero_mul] at h0
    filter_upwards [h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    have h1 := glow n y
    have h2 : 0 ≤ K * c ^ n := mul_nonneg hK0 (pow_nonneg hc0 n)
    have h3 : M * 2⁻¹ ≤ M * g n y := by nlinarith
    have h4 : (2⁻¹ : ℝ) ≤ g n y := le_of_mul_le_mul_left h3 hM0
    have := ENNReal.ofReal_le_ofReal h4
    rwa [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat] at this
  have hF : 2⁻¹ * μ Set.univ ≤ μ {y | f y ≤ M} := by
    rw [← lintegral_const]
    refine (lintegral_mono hlim).trans ?_
    refine (lintegral_liminf_le fun n => (gmeas n).ennreal_ofReal).trans ?_
    simp only [gint, Filter.liminf_const, le_refl]
  calc μ Set.univ = 2 * (2⁻¹ * μ Set.univ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ _ := by gcongr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSupMulRelIndexInfSame
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem relIndex_sup_mul_relIndex_inf_same {A : Type} [AddCommGroup A] (M L N : AddSubgroup A)
    (h : M ≤ L) :
    (M ⊔ N).relIndex (L ⊔ N) * (M ⊓ N).relIndex (L ⊓ N) = M.relIndex L := by
  have h1 : (M ⊔ N).relIndex (L ⊔ N) = (M ⊔ (N ⊓ L)).relIndex L := by
    have e : L ⊔ N = L ⊔ (M ⊔ N) := by
      rw [← sup_assoc, sup_eq_left.mpr h]
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (M ⊔ N) L,
      sup_inf_assoc_of_le N h]
  have h2 : (M ⊓ N).relIndex (L ⊓ N) = M.relIndex (M ⊔ (N ⊓ L)) := by
    have e : M ⊓ N = M ⊓ (L ⊓ N) := by
      rw [← inf_assoc, inf_eq_left.mpr h]
    rw [e, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_sup_left, inf_comm]
  rw [h1, h2, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le h inf_le_right)

theorem relIndex_sup_mul_relIndex_inf :
    (∀ (A : Type) [AddCommGroup A] (M₁ L₁ M₂ L₂ : AddSubgroup A), M₁ ≤ L₁ → M₂ ≤ L₂ →
      (M₁ ⊔ M₂).relIndex (L₁ ⊔ L₂) * (M₁ ⊓ M₂).relIndex (L₁ ⊓ L₂) =
        M₁.relIndex L₁ * M₂.relIndex L₂) := by
  intro A _ M₁ L₁ M₂ L₂ h₁ h₂
  have a := relIndex_sup_mul_relIndex_inf_same M₁ L₁ M₂ h₁
  have b := relIndex_sup_mul_relIndex_inf_same M₂ L₂ L₁ h₂
  rw [sup_comm M₂, sup_comm L₂, inf_comm M₂, inf_comm L₂] at b
  rw [← a, ← b,
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊔ M₂) (L₁ ⊔ M₂) (L₁ ⊔ L₂)
      (sup_le_sup_right h₁ _) (sup_le_sup_left h₂ _),
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊓ M₂) (L₁ ⊓ M₂) (L₁ ⊓ L₂)
      (inf_le_inf_right _ h₁) (inf_le_inf_left _ h₂)]
  ring

end GlobalTheory
end

