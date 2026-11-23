module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma gram_eq_lemma (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma gram_mul_lemma_2 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq_lemma, gram_eq_lemma, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem dom_rmul {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) : rmul x b ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  have hN := FrameDegreeData.upper_of_bor (X := X) hb τ
  have hbd := (hb τ).1
  refine ⟨?_, fun i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 hbd
  · have hd := (hx τ).2 i
    have hdiag : ∀ j, mat b τ j j ≠ 0 := by
      intro j
      rw [Matrix.det_of_upperTriangular hN] at hbd
      exact Finset.prod_ne_zero_iff.1 hbd j (Finset.mem_univ j)
    have hP0 : (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
        (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => hdiag _
    have heq : dmin X.Gm (rmul x b) τ i = dmin X.Gm x τ i *
        (Complex.normSq (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
          (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) : ℂ) := by
      show lminor (gram τ.1 X.Gm (mat x τ * mat b τ)) i = _
      rw [gram_mul_lemma_2, FrameDegreeData.lminor_conj hN,
        show ∀ z w : ℂ, z * w * conj z = w * (z * conj z) from fun z w => by ring, Complex.mul_conj]
      rfl
    rw [heq, Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos hd (Complex.normSq_pos.2 hP0)

theorem stab_mat {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc = X.Gm := by
  have hst := (X.Γ_stab γ hγ).1
  ext i j
  have h := hst (Pi.single i 1) (Pi.single j 1)
  have hR : herm X.Gm (Pi.single i (1 : E)) (Pi.single j 1) = X.Gm i j := by
    simp [herm, Pi.single_apply, cc, apply_ite]
  have hL : herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single i 1)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single j 1) =
      ((γ : Matrix (Fin r) (Fin r) E)ᵀ * X.Gm * (γ : Matrix (Fin r) (Fin r) E).map cc) i j := by
    simp only [herm, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [← hL, h, hR]

theorem gram_gam {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (τ : X.Ψ) :
    gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1) = X.Gm.map τ.1 := by
  have h := stab_mat X hγ
  rw [gram_eq_lemma]
  conv_rhs => rw [← h]
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, emb_cc]

theorem gram_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
  show gram τ.1 X.Gm ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) = _
  rw [gram_mul_lemma_2, gram_gam X hγ τ, gram_eq_lemma]

theorem dom_lact {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  rw [X.mem_dom_iff] at hx ⊢
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
    rw [Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have h1 : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]
      rfl
    rw [h1]
    exact (map_ne_zero τ.1).2 (Matrix.isUnits_det_units γ).ne_zero
  · have := (hx τ).2 i
    simpa only [dmin, gram_lact X hγ x τ] using this

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfA
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

open Topology Filter
open ReciprocityTheory.L2DbarEstimates

variable {n : ℕ}

theorem grad_le_of_minorant (rh Ψ : V n → ℝ) (v0 : V n) (C : ℝ) (hC : 0 < C)
    (hΨ0 : 0 < Ψ v0) (hrh : ContDiffAt ℝ 2 rh v0) (hΨ : ContDiffAt ℝ 2 Ψ v0) (ξ : Fin n → ℂ)
    (hL : (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re ≤ 0)
    (hle : ∀ᶠ v in 𝓝 v0, -C * Real.log (Ψ v) ≤ rh v) (heq : rh v0 = -C * Real.log (Ψ v0)) :
    Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) ≤
      C * (leviV n (fun y => (rh y : ℂ)) v0 ξ).re := by
  set k : ℝ → ℝ := fun t => -C * Real.log t with hkdef
  set ψ : V n → ℝ := fun y => k (Ψ y) with hψdef
  have hk : ContDiffAt ℝ 2 k (Ψ v0) := contDiffAt_const.mul (Real.contDiffAt_log.2 hΨ0.ne')
  have hψ : ContDiffAt ℝ 2 ψ v0 := hk.comp v0 hΨ
  have hrd : DifferentiableAt ℝ rh v0 := hrh.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ v0 := hψ.differentiableAt (by simp)
  have hΨd : DifferentiableAt ℝ Ψ v0 := hΨ.differentiableAt (by simp)
  have hkd : DifferentiableAt ℝ k (Ψ v0) := hk.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => rh y - ψ y) v0 := by
    filter_upwards [hle] with v hv
    simp only [hψdef, hkdef]
    linarith
  have hfd : fderiv ℝ rh v0 = fderiv ℝ ψ v0 := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (rh y : ℂ)) v0 = wd n j (fun y => (ψ y : ℂ)) v0 := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hdk : deriv k = fun t => -C * t⁻¹ := by
    funext t
    simp only [hkdef]
    rw [deriv_const_mul_field', Real.deriv_log']
  have hddk : deriv (deriv k) = fun t => C * (t ^ 2)⁻¹ := by
    rw [hdk]
    funext t
    rw [deriv_const_mul_field']
    show -C * deriv (fun x : ℝ => x⁻¹) t = _
    rw [deriv_inv]
    ring
  have hwdψ : ∀ j, wd n j (fun y => (ψ y : ℂ)) v0 =
      (((-C * (Ψ v0)⁻¹ : ℝ)) : ℂ) * wd n j (fun y => (Ψ y : ℂ)) v0 := by
    intro j
    rw [show (fun y => (ψ y : ℂ)) = fun y => (k (Ψ y) : ℂ) from rfl, wd_ofReal_comp hkd hΨd, hdk]
  have hchain := leviChain n k Ψ v0 ξ hΨ hk
  rw [hddk, hdk] at hchain

  have hmax : IsLocalMax (fun y => ψ y + (-1) * rh y) v0 := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * rh y) v0 := hψ.add (contDiffAt_const.mul hrh)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hrh) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hrh ξ] at h2
  have hψL : leviV n (fun y => (ψ y : ℂ)) v0 ξ = leviV n (fun y => (k (Ψ y) : ℂ)) v0 ξ := rfl
  rw [hψL, hchain] at h2
  set N := Complex.normSq (∑ j, wd n j (fun y => (Ψ y : ℂ)) v0 * ξ j) with hN
  set LΨ := (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re
  set Lr := (leviV n (fun y => (rh y : ℂ)) v0 ξ).re
  have h3 : (-C * (Ψ v0)⁻¹) * LΨ + C * ((Ψ v0) ^ 2)⁻¹ * N ≤ Lr := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Complex.neg_re, Complex.one_re, neg_mul, one_mul] at h2
    linarith
  have hlhs : Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) =
      (C * (Ψ v0)⁻¹) ^ 2 * N := by
    simp only [hwd, hwdψ, mul_assoc, ← Finset.mul_sum, Complex.normSq_mul, Complex.normSq_ofReal, hN]
    ring
  rw [hlhs]
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hi : 0 < (Ψ v0)⁻¹ := inv_pos.2 hΨ0
  have h4 : 0 ≤ (-C * (Ψ v0)⁻¹) * LΨ := by
    have : -C * (Ψ v0)⁻¹ ≤ 0 := by nlinarith
    nlinarith
  have h5 : (C * (Ψ v0)⁻¹) ^ 2 * N = C * (C * ((Ψ v0) ^ 2)⁻¹ * N) := by
    ring
  rw [h5]
  exact mul_le_mul_of_nonneg_left (by linarith) hC.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgB

open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA

open scoped MatrixOrder in
theorem exists_factor {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ} (hM : M.PosSemidef) :
    ∃ y : Matrix (Fin m) (Fin m) ℂ, M = yᴴ * y := by
  obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  exact ⟨y, hy⟩

theorem amgm_psd {m : ℕ} (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosSemidef) :
    P.det.re ^ ((m : ℝ)⁻¹) ≤ P.trace.re / m := by
  have hH := hP.1
  have hd : P.det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  have ht : P.trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp [← Complex.ofReal_sum]
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.eigenvalues_nonneg i
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin m))
    (fun _ => (m : ℝ)⁻¹) (fun i => hH.eigenvalues i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp) (fun i _ => hnn i)
  rw [hd, ht, ← Real.finsetProd_rpow _ _ (fun i _ => hnn i)]
  calc ∏ i, hH.eigenvalues i ^ ((m : ℝ)⁻¹) ≤ ∑ i, (m : ℝ)⁻¹ * hH.eigenvalues i := h
    _ = (∑ i, hH.eigenvalues i) / m := by rw [← Finset.mul_sum]; field_simp

theorem amgm {m : ℕ} (hm : 0 < m) {A A0 : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef)
    (hA0 : A0.PosDef) :
    A.det.re ^ ((m : ℝ)⁻¹) ≤ A0.det.re ^ ((m : ℝ)⁻¹) * ((A * A0⁻¹).trace.re / m) := by
  have hM : (A0⁻¹).PosDef := hA0.inv
  obtain ⟨y, hy⟩ := exists_factor hM.posSemidef
  have hP : (y * A * yᴴ).PosSemidef := hA.posSemidef.mul_mul_conjTranspose_same y
  have htr : (y * A * yᴴ).trace = (A * A0⁻¹).trace := by
    rw [hy, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  obtain ⟨ha, hai⟩ := det_re_pos_im hA
  obtain ⟨hb, hbi⟩ := det_re_pos_im hA0
  have hdet : (y * A * yᴴ).det.re = A.det.re * (A0.det.re)⁻¹ := by
    have e1 : (y * A * yᴴ).det = A.det * (A0⁻¹).det := by
      rw [hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]; ring
    rw [e1, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', det_eq_ofReal hA, det_eq_ofReal hA0]
    simp only [Complex.ofReal_re]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := amgm_psd hm hP
  rw [hdet, htr, Real.mul_rpow ha.le (inv_nonneg.2 hb.le), Real.inv_rpow hb.le] at h
  have hc : 0 < A0.det.re ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hb _
  calc A.det.re ^ ((m : ℝ)⁻¹) = A0.det.re ^ ((m : ℝ)⁻¹) *
        (A.det.re ^ ((m : ℝ)⁻¹) * (A0.det.re ^ ((m : ℝ)⁻¹))⁻¹) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le

end ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
end

