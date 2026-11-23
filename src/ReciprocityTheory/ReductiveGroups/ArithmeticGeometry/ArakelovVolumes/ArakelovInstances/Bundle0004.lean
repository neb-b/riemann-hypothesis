module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.KappaStatementHolds
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_lower (w : V (nd X)) (τ : X.Ψ) : (mat (nmat X w) τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := hij
  simp [mat, nmat, hij'.ne, not_lt.mpr hij'.le]

theorem ninv_lower (w : V (nd X)) (τ : X.Ψ) (x y : Fin r) (hxy : x < y) :
    Ring.inverse (mat (nmat X w) τ) x y = 0 := by
  have : Invertible (mat (nmat X w) τ) := (isUnit_nmat X τ w).invertible
  have h := Matrix.blockTriangular_inv_of_blockTriangular (nmat_lower X w τ)
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact h hxy

theorem ninv_diag (w : V (nd X)) (τ : X.Ψ) (a : Fin r) : Ring.inverse (mat (nmat X w) τ) a a = 1 := by
  have hu : IsUnit (mat (nmat X w) τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_nmat X τ w)

  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · rw [← Matrix.nonsing_inv_eq_ringInverse]
    simpa [mat, nmat] using h1
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h0 : (mat (nmat X w) τ)⁻¹ k a = 0 := by
        rw [Matrix.nonsing_inv_eq_ringInverse]
        exact ninv_lower X w τ k a hlt
      rw [h0, mul_zero]
    · rw [nmat_lower X w τ hgt, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c

theorem det_lmulL_ninv (w : V (nd X)) : LinearMap.det (lmulL X (ninvF X w)) = 1 :=
  det_lmulL_unit X (ninvF X w) (fun τ a x h => ninv_lower X w τ a x h) (fun τ a => ninv_diag X w τ a)

theorem embF_lmulL (w : V (nd X)) (τ : X.Ψ) (v : V (nd X)) (x c : Fin r) :
    embF X (lmulL X (ninvF X w) (vecOf X v)) τ x c =
      (Ring.inverse (mat (nmat X w) τ) * Lin X τ v) x c := by
  have hl : ∀ (N : Frame X.Ψ r) (u : Ent X → ℂ) (e : Ent X),
      lmulL X N u e = ∑ k, N e.1 e.2.1.1 k * embF X u e.1 k e.2.1.2 := fun _ _ _ => rfl
  have hL : ∀ k c' : Fin r, Lin X τ v k c' = embF X (vecOf X v) τ k c' := fun _ _ => rfl
  rw [Matrix.mul_apply]
  by_cases h : c < x
  · rw [embF, dite_eq_left h, hl]
    rfl
  ·
    rw [embF, dite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : c < k
    · rw [ninv_lower X w τ x k (lt_of_le_of_lt (not_lt.mp h) hk), zero_mul]
    · rw [hL, embF, dite_eq_right hk, mul_zero]

def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))

theorem vecL_apply (v : V (nd X)) : vecL X v = vecOf X v := rfl

theorem kappa_statement_holds : KapGGStatement (E := E) := by
  intro r X x0 x1 γ U Φ bf hU hdiff hrel z hz
  obtain ⟨hdom, hbor, -⟩ := hrel z hz
  set Φ' := fderiv ℂ Φ z with hΦ'
  have hΦ : HasFDerivAt Φ Φ' z := ((hdiff z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt

  have hmat : ∀ z' ∈ U, ∀ τ : X.Ψ, mat x0 τ * mat (nmat X z') τ =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ) *
        (mat (nmat X (Φ z')) τ * mat (bf z') τ) := by
    intro z' hz' τ
    have h := congrFun (hrel z' hz').2.2 τ
    change mat x0 τ * mat (nmat X z') τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((mat x1 τ * mat (nmat X (Φ z')) τ) * mat (bf z') τ) at h
    rw [h]
    simp only [Matrix.mul_assoc]

  have hG : ∀ τ : X.Ψ, IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ).det := by
    intro τ
    have h0 : (mat x0 τ * mat (nmat X z) τ).det ≠ 0 := (hdom τ).1
    rw [hmat z hz τ, Matrix.det_mul] at h0
    exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul h0)
  have hrel' : ∀ τ : X.Ψ, ∀ z' ∈ U, mat (nmat X (Φ z')) τ * mat (bf z') τ =
      (((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x1 τ)⁻¹ * mat x0 τ) * mat (nmat X z') τ := by
    intro τ z' hz'
    rw [Matrix.mul_assoc, hmat z' hz' τ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hG τ),
      Matrix.one_mul]
  have hup : ∀ τ : X.Ψ, ∀ z' ∈ U, ∀ a c : Fin r, c < a → mat (bf z') τ a c = 0 :=
    fun τ z' hz' a c h => ((hrel z' hz').2.1 τ).2 a c h
  set b := bf z with hb

  have key : (rmulL X b) ∘ₗ (lmulL X (ninvF X (Φ z))) ∘ₗ
      ((vecL X : V (nd X) →ₗ[ℂ] (Ent X → ℂ)) ∘ₗ (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
        ((vecL X).symm : (Ent X → ℂ) →ₗ[ℂ] V (nd X))) =
      (lmulL X b) ∘ₗ (lmulL X (ninvF X z)) := by
    refine LinearMap.ext fun u => funext fun e => ?_
    obtain ⟨h, rfl⟩ : ∃ h, vecL X h = u := ⟨(vecL X).symm u, (vecL X).apply_symm_apply u⟩
    rcases e with ⟨τ, ⟨⟨a, c⟩, hca⟩⟩
    have hld := lower_deriv X τ _ U hU Φ (fun z' => mat (bf z') τ) (hrel' τ) (hup τ) z hz Φ' hΦ h a c hca
    rw [Matrix.sub_apply, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply] at hld
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      ContinuousLinearMap.coe_coe]
    simp only [vecL_apply]
    show ∑ y, embF X (lmulL X (ninvF X (Φ z)) (vecOf X (Φ' h))) τ a y * b τ y c =
      ∑ x, b τ a x * embF X (lmulL X (ninvF X z) (vecOf X h)) τ x c
    simp only [embF_lmulL]
    exact hld.symm
  have hdet := congrArg LinearMap.det key
  simp only [LinearMap.det_comp, LinearMap.det_conj, det_lmulL_ninv, one_mul] at hdet
  have hupb : ∀ τ a x, x < a → b τ a x = 0 := fun τ a x h => (hbor τ).2 a x h
  rw [det_lmulL_upper X b hupb, det_rmulL_upper X b hupb] at hdet

  have hd : ∀ τ a, b τ a a ≠ 0 := by
    intro τ a
    have h0 := (hbor τ).1
    rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun i j h => (hbor τ).2 i j h)] at h0
    exact Finset.prod_ne_zero_iff.mp h0 a (Finset.mem_univ a)
  have hcol : ∏ e : Ent X, b e.1 e.2.1.2 e.2.1.2 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ => hd _ _
  rw [bchar_kap X b hd]
  show LinearMap.det (Φ' : V (nd X) →ₗ[ℂ] V (nd X)) = _
  exact eq_div_of_mul_eq hcol (by rw [mul_comm, hdet, mul_one])

end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LogpdAnalytic
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P Filter Topology

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

theorem fn_zero_ne (hD : ∀ k, D k ≠ 0) : fn hm D Y 0 ≠ 0 := by
  unfold fn
  simp only [Pi.zero_apply]
  have h : Gnz hm D Y 0 = Matrix.diagonal fun a : Fin m => ((D (Fin.castLE hm a) : ℝ) : ℂ) := by
    simp only [Gnz, Gz, zero_smul, sub_zero, add_zero, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
    first
    | exact Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)
    | simp [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hm)]
    | (ext i j
       simp [Matrix.diagonal_apply, (Fin.castLE_injective hm).eq_iff])
  rw [h, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_ne_zero_iff.2 fun a _ => hD _

theorem levi_logfn (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fn hm D Y v|) 0 (fun _ => 1) =
      levi (fn hm D Y) 0 (fun _ => 1) / fn hm D Y 0 := by
  have hc : ContDiffAt ℝ 2 (fn hm D Y) 0 := (contDiff_fn hm D Y).contDiffAt
  have h0 := fn_zero_ne hm D Y hD
  have h := leviHalfLogAbs (ι := Fin 1) (fn hm D Y) 0 hc h0 (fderiv_fn_zero hm D Y) (fun _ => 1)
  have hL : ContDiffAt ℝ 2 (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) 0 := by
    have e : (fun x => (1 / 2 : ℝ) * Real.log |fn hm D Y x|) = fun x => (1 / 2 : ℝ) * Real.log (fn hm D Y x) := by
      funext x; rw [Real.log_abs]
    rw [e]
    exact contDiffAt_const.mul (hc.log h0)
  have e : (fun v => Real.log |fn hm D Y v|) =
      fun v => (1 / 2 * Real.log |fn hm D Y v|) + 1 * (1 / 2 * Real.log |fn hm D Y v|) := by
    funext v; ring
  rw [e, levi_add_smul 1 hL hL, h]
  field_simp
  ring

theorem Gz_herm (ζ : ℂ) : (Gz hm D Y ζ)ᴴ = Gz hm D Y ζ := by
  have hD : (Matrix.diagonal fun k => (D k : ℂ))ᴴ = Matrix.diagonal fun k => (D k : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext k
    simp
  first
  | simp only [Gz, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
  | (unfold Gz
     rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
       Matrix.conjTranspose_conjTranspose]
     erw [hD]
     simp only [Matrix.mul_assoc])

theorem fn_eq (v : Fin 1 → ℂ) : fn hm D Y v = ‖pd hm Y v‖ ^ 2 * fY hm D Y v := by
  have key : ∀ (p G : ℂ), (star p * (G * p)).re = ‖p‖ ^ 2 * G.re := by
    intro p G
    have h1 : star p * (G * p) = ((Complex.normSq p : ℝ) : ℂ) * G := by
      rw [Complex.star_def, ← Complex.mul_conj]
      ring
    rw [h1, Complex.re_ofReal_mul]
    first
    | rw [Complex.normSq_eq_norm_sq]
    | rw [← Complex.sq_norm]
    | simp [Complex.normSq_eq_norm_sq]
  simp only [fn, fY, Gnz, pd, Matrix.det_mul, Matrix.det_conjTranspose]
  exact key _ _

theorem pd_eval (v : Fin 1 → ℂ) : pd hm Y v = (lin (-(Ym hm Y))).det.eval (v 0) := by
  unfold pd lin
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, sub_eq_add_neg] <;> ring
  · simp [Matrix.one_apply, h, sub_eq_add_neg] <;> ring

theorem pd_analytic : AnalyticAt ℂ (pd hm Y) 0 := by
  have e : pd hm Y = (fun z => (lin (-(Ym hm Y))).det.eval z) ∘ (fun v : Fin 1 → ℂ => v 0) :=
    funext fun v => pd_eval hm Y v
  rw [e]
  exact ((lin (-(Ym hm Y))).det.differentiable.analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt _)

theorem pd_zero : pd hm Y 0 = 1 := by
  simp [pd]

theorem logpd_analytic : AnalyticAt ℂ (fun v => 2 * Complex.log (pd hm Y v)) 0 := by
  have h0 : pd hm Y 0 ∈ Complex.slitPlane := by
    rw [pd_zero]
    exact Complex.one_mem_slitPlane
  exact analyticAt_const.mul ((pd_analytic hm Y).clog h0)

theorem logpd_eq (v : Fin 1 → ℂ) : Real.log (‖pd hm Y v‖ ^ 2) = (2 * Complex.log (pd hm Y v)).re := by
  have h : (2 * Complex.log (pd hm Y v)).re = 2 * (Complex.log (pd hm Y v)).re := by
    simp [Complex.mul_re]
  rw [h, Complex.log_re, Real.log_pow]
  push_cast
  ring

theorem levi_logpd (w : Fin 1 → ℂ) : levi (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 w = 0 := by
  have e : (fun v => Real.log (‖pd hm Y v‖ ^ 2)) = fun v => (2 * Complex.log (pd hm Y v)).re :=
    funext fun v => logpd_eq hm Y v
  rw [e]
  exact levi_re_analytic (logpd_analytic hm Y) w

theorem core_levi (hD : ∀ k, D k ≠ 0) :
    levi (fun v => Real.log |fY hm D Y v|) 0 (fun _ => 1) =
      ∑ a : Fin m, (D (Fin.castLE hm a))⁻¹ * Sa hm D Y a := by
  have hP : (∏ a : Fin m, D (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hD _
  have hfY0 : fY hm D Y 0 ≠ 0 := by rw [fY_zero]; exact hP
  have h0 := fn_zero_ne hm D Y hD
  have hcont : ContinuousAt (fY hm D Y) 0 := (contDiff_fY hm D Y).continuous.continuousAt
  have hpdc : ContinuousAt (pd hm Y) 0 := (pd_analytic hm Y).continuousAt
  have hev : (fun v => Real.log |fY hm D Y v|) =ᶠ[𝓝 0]
      fun v => Real.log |fn hm D Y v| + (-1) * Real.log (‖pd hm Y v‖ ^ 2) := by
    filter_upwards [hcont.eventually_ne hfY0, hpdc.eventually_ne (by rw [pd_zero]; exact one_ne_zero)]
      with v h1 h2
    have hp : ‖pd hm Y v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 h2)
    rw [Real.log_abs, Real.log_abs, fn_eq, Real.log_mul hp h1]
    ring
  have hL1 : ContDiffAt ℝ 2 (fun v => Real.log |fn hm D Y v|) 0 := by
    have e : (fun v => Real.log |fn hm D Y v|) = fun v => Real.log (fn hm D Y v) := by
      funext v; rw [Real.log_abs]
    rw [e]
    exact (contDiff_fn hm D Y).contDiffAt.log h0
  have hL2 : ContDiffAt ℝ 2 (fun v => Real.log (‖pd hm Y v‖ ^ 2)) 0 := by
    rw [funext (logpd_eq hm Y)]
    exact Complex.reCLM.contDiff.contDiffAt.comp _
      ((logpd_analytic hm Y).contDiffAt.restrict_scalars ℝ)
  rw [levi_congr hev, levi_add_smul (-1) hL1 hL2, levi_logpd, levi_logfn hm D Y hD, levi_fn hm D Y hD,
    fn_zero, mul_zero, add_zero, mul_div_cancel_left₀ _ hP]

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

