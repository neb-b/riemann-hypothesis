module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltFrob
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

namespace KAlt

def frobDelta {r : ℕ} (la : Fin r → ℕ) : ℚ :=
  ∏ a : Fin r, ∏ b : Fin r,
    if a < b then ((la a + (r - 1 - a) : ℕ) : ℚ) - ((la b + (r - 1 - b) : ℕ) : ℚ) else 1

theorem frobDim_eq {r : ℕ} (la : Fin r → ℕ) :
    frobDim la = ((∑ a, la a).factorial : ℚ) * frobDelta la /
      ∏ a : Fin r, ((la a + (r - 1 - a)).factorial : ℚ) := rfl

theorem frobDelta_add_const {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    frobDelta (fun a => s + ν a) = frobDelta ν := by
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs
  · push_cast; ring
  · rfl

theorem prod_sub_eq_prod_factorial : ∀ r : ℕ,
    (∏ a : Fin r, ∏ b : Fin r, if a < b then ((b : ℕ) : ℚ) - ((a : ℕ) : ℚ) else 1) =
      ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : (∏ b : Fin (r + 1), if (0 : Fin (r + 1)) < b
        then (((b : ℕ) : ℚ) - (((0 : Fin (r + 1)) : ℕ) : ℚ)) else 1) = (r.factorial : ℚ) := by
      rw [Fin.prod_univ_succ]
      simp only [lt_self_iff_false, ite_false, Fin.succ_pos, ite_true, one_mul, Fin.val_succ,
        Fin.val_zero, Nat.cast_zero, sub_zero]
      push_cast
      rw [Fin.prod_univ_eq_prod_range (fun i => ((i : ℚ) + 1)) r]
      exact_mod_cast Finset.prod_range_add_one_eq_factorial r
    have hs : ∀ a : Fin r, (∏ b : Fin (r + 1), if a.succ < b
        then (((b : ℕ) : ℚ) - ((a.succ : ℕ) : ℚ)) else 1) =
        ∏ b : Fin r, if a < b then (((b : ℕ) : ℚ) - ((a : ℕ) : ℚ)) else 1 := by
      intro a
      rw [Fin.prod_univ_succ]
      simp only [Fin.not_lt_zero, ite_false, one_mul, Fin.succ_lt_succ_iff, Fin.val_succ]
      refine prod_congr rfl fun b _ => ?_
      split_ifs
      · push_cast; ring
      · rfl
    have hshift (a : Fin r) : r + 1 - 1 - (a.succ : ℕ) = r - 1 - (a : ℕ) := by
      simp only [Fin.val_succ]
      omega
    conv_lhs => rw [Fin.prod_univ_succ]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [h0, hs, ih, hshift]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]

theorem frobDelta_const {r : ℕ} (s : ℕ) :
    frobDelta (fun _ : Fin r => s) = ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) := by
  rw [← prod_sub_eq_prod_factorial r]
  unfold frobDelta
  refine prod_congr rfl fun a _ => prod_congr rfl fun b _ => ?_
  split_ifs with h
  · have ha := a.isLt
    have hb := b.isLt
    have hab : (a : ℕ) < b := h
    have : ((s + (r - 1 - (a : ℕ)) : ℕ) : ℚ) + ((a : ℕ) : ℚ) =
        ((s + (r - 1 - (b : ℕ)) : ℕ) : ℚ) + ((b : ℕ) : ℚ) := by
      exact_mod_cast (show s + (r - 1 - (a : ℕ)) + a = s + (r - 1 - (b : ℕ)) + b by omega)
    linarith
  · rfl

theorem frobDelta_nonneg {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν) : 0 ≤ frobDelta ν := by
  unfold frobDelta
  refine prod_nonneg fun a _ => prod_nonneg fun b _ => ?_
  split_ifs with h
  · have h1 : ν b ≤ ν a := hν h.le
    have hab : (a : ℕ) < b := h
    have hb := b.isLt
    have h2 : ν b + (r - 1 - (b : ℕ)) ≤ ν a + (r - 1 - (a : ℕ)) := by omega
    rw [sub_nonneg]
    exact_mod_cast h2
  · exact zero_le_one

theorem factorial_mul_le (s c d : ℕ) :
    (s + c).factorial * (c + d).factorial ≤ (s + c + d).factorial * c.factorial := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show c + (d + 1) = (c + d) + 1 by ring, Nat.factorial_succ,
      show s + c + (d + 1) = (s + c + d) + 1 by ring, Nat.factorial_succ]
    calc (s + c).factorial * ((c + d + 1) * (c + d).factorial)
        = (c + d + 1) * ((s + c).factorial * (c + d).factorial) := by ring
      _ ≤ (s + c + d + 1) * ((s + c + d).factorial * c.factorial) :=
          Nat.mul_le_mul (by omega) ih
      _ = ((s + c + d + 1) * (s + c + d).factorial) * c.factorial := by ring

theorem prod_factorial_le {r : ℕ} (s : ℕ) (ν : Fin r → ℕ) :
    (∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ)) *
        ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) ≤
      (∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)) *
        ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) := by
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro a _; positivity
  · intro a _
    have := factorial_mul_le s (r - 1 - (a : ℕ)) (ν a)
    rw [show s + ν a + (r - 1 - (a : ℕ)) = s + (r - 1 - (a : ℕ)) + ν a by ring,
      show ν a + (r - 1 - (a : ℕ)) = (r - 1 - (a : ℕ)) + ν a by ring,
      mul_comm (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ)]
    exact_mod_cast this

end KAlt

theorem FrobeniusRectangleBound.intersectionNumber_baseChange : FrobeniusRectangleBound.Statement := by
  intro r s ν hν
  simp only [KAlt.frobDim_eq, KAlt.frobDelta_add_const, KAlt.frobDelta_const]
  have hsum : (∑ a : Fin r, (s + ν a)) = r * s + ∑ a, ν a := by
    rw [Finset.sum_add_distrib]; simp
  have hsum' : (∑ _a : Fin r, s) = r * s := by simp
  rw [hsum, hsum']
  set k := ∑ a, ν a with hk
  set A := ∏ a : Fin r, ((s + ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hA
  set B := ∏ a : Fin r, ((s + (r - 1 - (a : ℕ))).factorial : ℚ) with hB
  set E := ∏ a : Fin r, ((ν a + (r - 1 - (a : ℕ))).factorial : ℚ) with hE
  set F := ∏ a : Fin r, (((r - 1 - (a : ℕ)).factorial : ℕ) : ℚ) with hF
  set D := KAlt.frobDelta ν with hD
  have hA0 : 0 < A := prod_pos fun a _ => by positivity
  have hB0 : 0 < B := prod_pos fun a _ => by positivity
  have hE0 : 0 < E := prod_pos fun a _ => by positivity
  have hD0 : 0 ≤ D := KAlt.frobDelta_nonneg ν hν
  have key : B * E ≤ F * A := KAlt.prod_factorial_le s ν
  have hch : ((r * s + k).choose k : ℚ) * ((r * s).factorial : ℚ) * (k.factorial : ℚ) =
      ((r * s + k).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ r * s + k by omega)
    rw [show r * s + k - k = r * s by omega] at h
    rw [← h]; push_cast; ring
  have hrhs : ((r * s + k).choose k : ℚ) * ((r * s).factorial * F / B) * (k.factorial * D / E) =
      ((r * s + k).factorial : ℚ) * D * F / (B * E) := by
    rw [← hch]; field_simp
  rw [hrhs, div_le_div_iff₀ hA0 (mul_pos hB0 hE0)]
  calc ((r * s + k).factorial : ℚ) * D * (B * E) ≤ ((r * s + k).factorial : ℚ) * D * (F * A) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((r * s + k).factorial : ℚ) * D * F * A := by ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltPush
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Finset

noncomputable section

namespace KAlt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def permTerm (e : ι → ℕ) (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ∏ i, X (π i) ^ e i

def sgnP (π : Equiv.Perm ι) : MvPolynomial ι ℚ := ((Equiv.Perm.sign π : ℤ) : MvPolynomial ι ℚ)

theorem alternant_eq_sum (e : ι → ℕ) : alternant e = ∑ π, sgnP π * permTerm e π := by
  simp [alternant, Matrix.det_apply', permTerm, sgnP]

theorem antisym_eq_sum (H : MvPolynomial ι ℚ) : antisym H = ∑ w, sgnP w * rename w H := by
  unfold antisym
  refine sum_congr rfl fun w _ => ?_
  rw [Algebra.smul_def, map_intCast]
  rfl

omit [DecidableEq ι] in
theorem rename_permTerm (e : ι → ℕ) (w π : Equiv.Perm ι) :
    rename w (permTerm e π) = permTerm e (w * π) := by
  simp [permTerm, map_prod, rename_X, Equiv.Perm.mul_apply]

theorem permSign_mul₂ (a b : Equiv.Perm ι) : sgnP (a * b) = sgnP a * sgnP b := by
  simp [sgnP, Equiv.Perm.sign_mul]

theorem permSign_inv₂ (a : Equiv.Perm ι) : sgnP a⁻¹ = sgnP a := by
  simp [sgnP, Equiv.Perm.sign_inv]

theorem permSign_mul_self₂ (a : Equiv.Perm ι) : sgnP a * sgnP a = 1 := by
  unfold sgnP
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem antisym_permTerm (e : ι → ℕ) (π : Equiv.Perm ι) :
    antisym (permTerm e π) = sgnP π * alternant e := by
  rw [antisym_eq_sum, alternant_eq_sum, mul_sum]
  simp_rw [rename_permTerm]
  refine (Equiv.sum_comp (Equiv.mulRight π⁻¹) _).symm.trans ?_
  refine sum_congr rfl fun u _ => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right, permSign_mul₂, permSign_inv₂]
  ring

theorem antisym_sum {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι ℚ) :
    antisym (∑ x ∈ s, f x) = ∑ x ∈ s, antisym (f x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [antisym, map_sum, smul_sum]
  rw [sum_comm]

theorem antisym_sign_mul (a : Equiv.Perm ι) (p : MvPolynomial ι ℚ) :
    antisym (sgnP a * p) = sgnP a * antisym p := by
  simp only [antisym_eq_sum, map_mul, sgnP, map_intCast, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  ring

variable {r s : ℕ}

theorem rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β) =
      ∑ σ : Equiv.Perm (Fin r), ∑ τ : Equiv.Perm (Fin s),
        sgnP (Equiv.Perm.sumCongr σ τ) * permTerm (Sum.elim α β) (Equiv.Perm.sumCongr σ τ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [alternant_eq_sum, alternant_eq_sum, map_sum, map_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  simp only [sgnP, permTerm, map_mul, map_intCast, map_prod, map_pow, rename_X,
    Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul, Fintype.prod_sum_type,
    Equiv.Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr]
  ring

theorem antisym_rename_mul_rename (α : Fin r → ℕ) (β : Fin s → ℕ) :
    antisym (rename (Sum.inl : Fin r → Fin r ⊕ Fin s) (alternant α) *
        rename (Sum.inr : Fin s → Fin r ⊕ Fin s) (alternant β)) =
      ((r.factorial : ℚ) * s.factorial) • alternant (Sum.elim α β) := by
  rw [rename_mul_rename, antisym_sum]
  simp_rw [antisym_sum, antisym_sign_mul, antisym_permTerm, ← mul_assoc, permSign_mul_self₂, one_mul]
  simp only [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

end KAlt

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.AltRow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace KAlt

end KAlt

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory

noncomputable section

namespace ChartMongeAmpereAffineInvariance

variable {D : ℕ}

def sesq (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (u v : Fin D → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4

theorem cxHessian_eq_sesq (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    cxHessian f z i j = sesq (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl

section Sesq

variable (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)

theorem sesq_add_left (u u' v : Fin D → ℂ) : sesq H (u + u') v = sesq H u v + sesq H u' v := by
  simp only [sesq, smul_add, map_add (f := _), _root_.add_apply]
  push_cast
  ring

theorem sesq_add_right (u v v' : Fin D → ℂ) : sesq H u (v + v') = sesq H u v + sesq H u v' := by
  simp only [sesq, smul_add, map_add (f := _)]
  push_cast
  ring

theorem sesq_real_smul_left (r : ℝ) (u v : Fin D → ℂ) : sesq H (r • u) v = r * sesq H u v := by
  simp only [sesq, smul_comm Complex.I r u, map_smul, _root_.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem sesq_real_smul_right (r : ℝ) (u v : Fin D → ℂ) : sesq H u (r • v) = r * sesq H u v := by
  simp only [sesq, smul_comm Complex.I r v, map_smul, smul_eq_mul]
  push_cast
  ring

theorem sesq_I_left (u v : Fin D → ℂ) : sesq H (Complex.I • u) v = Complex.I * sesq H u v := by
  have h : Complex.I • Complex.I • u = -u := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sesq, h, map_neg, _root_.neg_apply]
  push_cast
  linear_combination (-(H u (Complex.I • v) : ℂ) + (H (Complex.I • u) v : ℂ)) / 4 * Complex.I_sq

theorem sesq_I_right (u v : Fin D → ℂ) : sesq H u (Complex.I • v) = -Complex.I * sesq H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [sesq, h, map_neg]
  push_cast
  linear_combination ((H u (Complex.I • v) : ℂ) - (H (Complex.I • u) v : ℂ)) / 4 * Complex.I_sq

theorem smul_eq_re_add_im (a : ℂ) (u : Fin D → ℂ) : a • u = a.re • u + a.im • (Complex.I • u) := by
  funext p
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im a]
  ring

theorem sesq_smul_left (a : ℂ) (u v : Fin D → ℂ) : sesq H (a • u) v = a * sesq H u v := by
  rw [smul_eq_re_add_im, sesq_add_left, sesq_real_smul_left, sesq_real_smul_left, sesq_I_left]
  conv_rhs => rw [← Complex.re_add_im a]
  ring

theorem sesq_smul_right (a : ℂ) (u v : Fin D → ℂ) : sesq H u (a • v) = star a * sesq H u v := by
  rw [smul_eq_re_add_im, sesq_add_right, sesq_real_smul_right, sesq_real_smul_right, sesq_I_right]
  have hs : star a = (a.re : ℂ) - a.im * Complex.I := by apply Complex.ext <;> simp
  rw [hs]
  ring

theorem sesq_sum_left (u : Fin D → Fin D → ℂ) (v : Fin D → ℂ) :
    sesq H (∑ k, u k) v = ∑ k, sesq H (u k) v :=
  map_sum (AddMonoidHom.mk' (fun a => sesq H a v) fun a b => sesq_add_left H a b v) u Finset.univ

theorem sesq_sum_right (u : Fin D → ℂ) (v : Fin D → Fin D → ℂ) :
    sesq H u (∑ l, v l) = ∑ l, sesq H u (v l) :=
  map_sum (AddMonoidHom.mk' (fun b => sesq H u b) fun a b => sesq_add_right H u a b) v Finset.univ

theorem eq_sum_smul_single (a : Fin D → ℂ) : a = ∑ k, a k • (Pi.single k 1 : Fin D → ℂ) := by
  funext p
  simp [Finset.sum_apply, Pi.single_apply]

theorem sesq_expand (a b : Fin D → ℂ) :
    sesq H a b = ∑ k, ∑ l, a k * star (b l) * sesq H (Pi.single k 1) (Pi.single l 1) := by
  conv_lhs => rw [eq_sum_smul_single a, eq_sum_smul_single b]
  rw [sesq_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sesq_sum_right]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sesq_smul_left, sesq_smul_right]
  ring

end Sesq

def realCLE (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ) :=
  letI := P.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hP)
  ((P.toLinearEquiv' this).restrictScalars ℝ).toContinuousLinearEquiv

theorem realCLE_apply (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (y : Fin D → ℂ) :
    realCLE P hP y = P *ᵥ y := rfl

theorem fderiv_fderiv_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (L : (Fin D → ℂ) ≃L[ℝ] (Fin D → ℂ))
    (κ : ℝ) (z u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y => φ (c + L y) + κ) z u v = fderiv ℝ (fderiv ℝ φ) (c + L z) (L u) (L v) := by
  have h1 : (fderiv ℝ fun y => φ (c + L y) + κ) =
      fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) := by
    funext y
    rw [fderiv_add_const]
    have : (fun y => φ (c + L y)) = (fun w => φ (c + w)) ∘ L := rfl
    rw [this, L.comp_right_fderiv, fderiv_comp_add_left]
  have h2 : (fun y => (fderiv ℝ φ (c + L y)).comp (L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ))) =
      (L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) ∘ ((fun w => fderiv ℝ φ (c + w)) ∘ L) := by
    funext y
    ext w
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  rw [h1, h2, ContinuousLinearEquiv.comp_fderiv, L.comp_right_fderiv, fderiv_comp_add_left]
  simp [ContinuousLinearEquiv.arrowCongr_apply]

theorem cxHessian_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    cxHessian (fun y => φ (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian φ (c + P *ᵥ z) * P.map (starRingEnd ℂ) := by
  ext i j
  set L := realCLE P hP
  set H := fderiv ℝ (fderiv ℝ φ) (c + P *ᵥ z)
  have hI : ∀ w, L (Complex.I • w) = Complex.I • L w := fun w => by
    simp only [L, realCLE_apply, Matrix.mulVec_smul]
  have hent : cxHessian (fun y => φ (c + P *ᵥ y) + κ) z i j = sesq H (L (Pi.single i 1)) (L (Pi.single j 1)) := by
    have hg : (fun y => φ (c + P *ᵥ y) + κ) = fun y => φ (c + L y) + κ := rfl
    rw [cxHessian_eq_sesq, hg]
    simp only [sesq, fderiv_fderiv_comp_affine, hI]
    rfl
  rw [hent, sesq_expand]
  simp only [L, realCLE_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    mulVec_single_one]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian φ (c + P *ᵥ z) l k = sesq H (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [Matrix.col_apply, starRingEnd_apply, hc]
  ring

theorem mixedDisc_mul_mul (P Q : Matrix (Fin D) (Fin D) ℂ) (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => P * A k * Q) = P.det * Q.det * mixedDisc A := by
  have hS : ∀ S : Finset (Fin D), (∑ k ∈ S, P * A k * Q) = P * (∑ k ∈ S, A k) * Q := fun S => by
    rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mixedDisc, hS, det_mul]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

theorem maDensity_comp_affine (φ : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun _ : Fin D => fun y => φ (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity (fun _ : Fin D => φ) (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  simp only [maDensity, cxHessian_comp_affine φ c P hP κ z]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun _ => cxHessian φ (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem det_realCLE (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) :
    LinearMap.det ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      Complex.normSq P.det := by
  have h : ((realCLE P hP : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      (Matrix.toLin' P).restrictScalars ℝ := by
    ext y
    simp [realCLE_apply]
  rw [h, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem integral_comp_affine (f : (Fin D → ℂ) → ℝ) (c : Fin D → ℂ) (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.det ≠ 0) :
    ∫ y, f (c + P *ᵥ y) = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
  set L := realCLE P hP
  have hpos : 0 < Complex.normSq P.det := Complex.normSq_pos.mpr hP
  have hdet := det_realCLE P hP
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin D → ℂ))
    (f := ((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ))) (by rw [hdet]; exact hpos.ne')
  have hcoe : ⇑((L : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) = ⇑L := rfl
  rw [hcoe, hdet] at hmap
  calc ∫ y, f (c + P *ᵥ y) = ∫ y, (fun w => f (c + w)) (L y) := rfl
    _ = ∫ w, f (c + w) ∂(Measure.map L volume) :=
        (L.toHomeomorph.measurableEmbedding.integral_map (fun w => f (c + w))).symm
    _ = (Complex.normSq P.det)⁻¹ * ∫ y, f y := by
        rw [hmap, integral_smul_measure, integral_add_left_eq_self, ENNReal.toReal_ofReal (abs_nonneg _),
          abs_inv, abs_of_pos hpos, smul_eq_mul]

end ChartMongeAmpereAffineInvariance

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerKernel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem PlueckerKernel.proof (h₁ : PlueckerNormSq.Statement) (h₂ : PlueckerUnitBound.Statement) :
    PlueckerKernel.Statement := by
  intro j m Z hZ
  set S : ℝ := ∑ I : {I : Finset (Fin (j + m)) // I.card = j}, ‖(colsOf (onePipe Z) I).det‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun I _ => by positivity
  have hnorm : ‖((S : ℝ) : ℂ)‖ = S := Complex.norm_of_nonneg hS0
  have heq : ((S : ℝ) : ℂ) = (1 + Z * Zᴴ).det := h₁ j m Z
  calc S = ‖((S : ℝ) : ℂ)‖ := hnorm.symm
    _ = ‖(1 + Z * Zᴴ).det‖ := by rw [heq]
    _ ≤ (1 + m : ℝ) ^ j := h₂ j m Z hZ

end GroundTheory.Heights₂.Heights
end

