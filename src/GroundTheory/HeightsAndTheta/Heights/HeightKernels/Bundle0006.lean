module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartHessHolo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix Filter Topology

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {D : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
  [IsScalarTower ℝ ℂ E']

theorem eventually_fderiv_I_smul {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y) :
    ∀ᶠ y' in 𝓝 y, ∀ v, fderiv ℝ F y' (Complex.I • v) = Complex.I • fderiv ℝ F y' v := by
  filter_upwards [hF.eventually (by simp)] with y' hy' v
  rw [(hy'.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
  simp

theorem fderiv_fderiv_I_right {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y u (Complex.I • v) = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  have hR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y' => fderiv ℝ F y' (Complex.I • v))
      ((fderiv ℝ (fderiv ℝ F) y).flip (Complex.I • v)) y := by
    simpa using hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • v) y)
  have h2 : HasFDerivAt (fun y' => Complex.I • fderiv ℝ F y' v)
      (Complex.I • (fderiv ℝ (fderiv ℝ F) y).flip v) y := by
    have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).const_smul Complex.I
    simpa [Pi.smul_def] using this
  have h3 := h2.congr_of_eventuallyEq ((eventually_fderiv_I_smul hF).mono fun y' hy' => hy' v)
  have := congrArg (fun L => L u) (h1.unique h3)
  simpa using this


omit [NormedSpace ℂ E'] [IsScalarTower ℝ ℂ E'] in
theorem fderiv_fderiv_symm {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) : fderiv ℝ (fderiv ℝ F) y u v = fderiv ℝ (fderiv ℝ F) y v u :=
  hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) u v

theorem fderiv_fderiv_I_left {F : (Fin D → ℂ) → E'} {y : Fin D → ℂ} (hF : ContDiffAt ℂ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ F) y (Complex.I • u) v = Complex.I • fderiv ℝ (fderiv ℝ F) y u v := by
  rw [fderiv_fderiv_symm (hF.restrict_scalars ℝ), fderiv_fderiv_I_right hF,
    fderiv_fderiv_symm (hF.restrict_scalars ℝ)]

theorem fderiv_fderiv_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : G → ℝ}
    {F : (Fin D → ℂ) → G} {y : Fin D → ℂ} (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℝ 2 F y)
    (u v : Fin D → ℂ) :
    fderiv ℝ (fderiv ℝ fun y' => g (F y')) y u v =
      fderiv ℝ (fderiv ℝ g) (F y) (fderiv ℝ F y u) (fderiv ℝ F y v) +
        fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) := by
  have hgev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ g (F y') :=
    hF.continuousAt.tendsto.eventually
      ((hg.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num))
  have hFev : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℝ F y' :=
    (hF.eventually (by simp)).mono fun _ h => h.differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y' => g (F y')) =ᶠ[𝓝 y]
      fun y' => (fderiv ℝ g (F y')).comp (fderiv ℝ F y') := by
    filter_upwards [hgev, hFev] with y' h1 h2
    exact fderiv_comp y' h1 h2
  have hgd : DifferentiableAt ℝ (fderiv ℝ g) (F y) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y' => fderiv ℝ g (F y'))
      ((fderiv ℝ (fderiv ℝ g) (F y)).comp (fderiv ℝ F y)) y :=
    hgd.hasFDerivAt.comp y (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hall := (hc.clm_comp hFd.hasFDerivAt).congr_of_eventuallyEq heq
  rw [hall.fderiv]
  simp [add_comm]

theorem fderiv_fderiv_add {f₁ f₂ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h₁ : ContDiffAt ℝ 2 f₁ y)
    (h₂ : ContDiffAt ℝ 2 f₂ y) :
    fderiv ℝ (fderiv ℝ fun y' => f₁ y' + f₂ y') y = fderiv ℝ (fderiv ℝ f₁) y + fderiv ℝ (fderiv ℝ f₂) y := by
  have heq : fderiv ℝ (fun y' => f₁ y' + f₂ y') =ᶠ[𝓝 y] fun y' => fderiv ℝ f₁ y' + fderiv ℝ f₂ y' := by
    filter_upwards [h₁.eventually (by simp), h₂.eventually (by simp)] with y' a b
    exact fderiv_add (a.differentiableAt (by norm_num)) (b.differentiableAt (by norm_num))
  have hd₁ : DifferentiableAt ℝ (fderiv ℝ f₁) y :=
    (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ : DifferentiableAt ℝ (fderiv ℝ f₂) y :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hd₁.hasFDerivAt.add hd₂.hasFDerivAt).congr_of_eventuallyEq heq).fderiv

theorem sesq_eq_of_form (H H₀ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, H u v = H₀ (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) (a b : Fin D → ℂ) :
    sesq H a b = sesq H₀ (L a) (L b) := by
  simp only [sesq, hH, map_smul]
  rw [hR₁, hR₂]
  push_cast
  ring

theorem cxHessian_of_form (f g : (Fin D → ℂ) → ℝ) (y w : Fin D → ℂ) (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ))
    (R : (Fin D → ℂ) → (Fin D → ℂ) → ℝ)
    (hH : ∀ u v, fderiv ℝ (fderiv ℝ f) y u v = fderiv ℝ (fderiv ℝ g) w (L u) (L v) + R u v)
    (hR₁ : ∀ u v, R (Complex.I • u) (Complex.I • v) = -R u v)
    (hR₂ : ∀ u v, R u (Complex.I • v) = R (Complex.I • u) v) :
    cxHessian f y = (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ * cxHessian g w *
      (LinearMap.toMatrix' (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map (starRingEnd ℂ) := by
  ext i j
  rw [cxHessian_eq_sesq, sesq_eq_of_form _ _ L R hH hR₁ hR₂, sesq_expand]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hc : cxHessian g w l k = sesq (fderiv ℝ (fderiv ℝ g) w) (Pi.single l 1) (Pi.single k 1) := rfl
  simp only [hc, starRingEnd_apply]
  ring

theorem cxHessian_comp_holo (f g : (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ)) (h : (Fin D → ℂ) → ℂ)
    (y : Fin D → ℂ) (hg : ContDiffAt ℝ 2 g (F y)) (hF : ContDiffAt ℂ 2 F y) (hh : ContDiffAt ℂ 2 h y)
    (hf : f =ᶠ[𝓝 y] fun y' => g (F y') + (h y').re) :
    cxHessian f y = (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))ᵀ *
      cxHessian g (F y) * (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).map
        (starRingEnd ℂ) := by
  have hFR : ContDiffAt ℝ 2 F y := hF.restrict_scalars ℝ
  have hhR : ContDiffAt ℝ 2 h y := hh.restrict_scalars ℝ
  have hHess : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ fun y' => g (F y') + (h y').re) y := by
    have : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun y' => g (F y') + (h y').re) :=
      hf.eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq
    exact this.fderiv_eq
  have hre2 : ContDiffAt ℝ 2 (fun y' => (h y').re) y := Complex.reCLM.contDiff.contDiffAt.comp y hhR
  have hsum := fderiv_fderiv_add (f₁ := fun y' => g (F y')) (f₂ := fun y' => (h y').re) (hg.comp y hFR) hre2
  have hre : ∀ u v, fderiv ℝ (fderiv ℝ fun y' => (h y').re) y u v =
      Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v) := by
    intro u v
    have := fderiv_fderiv_comp (g := ⇑Complex.reCLM) (F := h) Complex.reCLM.contDiff.contDiffAt hhR u v
    have h0 : fderiv ℝ (fderiv ℝ (⇑Complex.reCLM)) (h y) = 0 := by
      have : fderiv ℝ (⇑Complex.reCLM) = fun _ => Complex.reCLM := funext fun _ => Complex.reCLM.fderiv
      rw [this]
      exact fderiv_const_apply _
    rw [h0, Complex.reCLM.fderiv] at this
    simpa using this
  have hLF : ∀ u, fderiv ℝ F y u = fderiv ℂ F y u := fun u => by
    rw [(hF.differentiableAt (by norm_num)).fderiv_restrictScalars ℝ]
    rfl
  refine cxHessian_of_form f g y (F y) (fderiv ℂ F y)
    (fun u v => fderiv ℝ g (F y) (fderiv ℝ (fderiv ℝ F) y u v) + Complex.reCLM (fderiv ℝ (fderiv ℝ h) y u v))
    ?_ ?_ ?_
  · intro u v
    rw [hHess, hsum, _root_.add_apply, _root_.add_apply, fderiv_fderiv_comp hg hFR,
      hre, hLF, hLF]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
    ring
  · intro u v
    simp only [fderiv_fderiv_I_left hF, fderiv_fderiv_I_right hF, fderiv_fderiv_I_left hh,
      fderiv_fderiv_I_right hh]

theorem maDensity_comp_holo (Φ' Φ : Fin D → (Fin D → ℂ) → ℝ) (F : (Fin D → ℂ) → (Fin D → ℂ))
    (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ) (hΦ : ∀ j, ContDiffAt ℝ 2 (Φ j) (F y)) (hF : ContDiffAt ℂ 2 F y)
    (hh : ContDiffAt ℂ 2 h y) (hΦ' : ∀ j, Φ' j =ᶠ[𝓝 y] fun y' => Φ j (F y') + (h y').re) :
    maDensity Φ' y = Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det *
      maDensity Φ (F y) := by
  set J := LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) with hJ
  have hQ : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := (RingHom.map_det (starRingEnd ℂ) J).symm
  have hH : ∀ j, cxHessian (Φ' j) y = Jᵀ * cxHessian (Φ j) (F y) * J.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_holo (Φ' j) (Φ j) F h y (hΦ j) hF hh (hΦ' j)
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Jᵀ) (J.map (starRingEnd ℂ)) (fun j => cxHessian (Φ j) (F y)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

theorem det_fderiv_real {F : (Fin D → ℂ) → (Fin D → ℂ)} {y : Fin D → ℂ} (hF : DifferentiableAt ℂ F y) :
    (fderiv ℝ F y).det =
      Complex.normSq (LinearMap.toMatrix' (fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).det := by
  rw [hF.fderiv_restrictScalars ℝ, LinearMap.det_toMatrix']
  have : ((ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F y) : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ)) :
      (Fin D → ℂ) →ₗ[ℝ] (Fin D → ℂ)) =
      ((fderiv ℂ F y : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))).restrictScalars ℝ := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

end ChartEnergySwapHessian

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartMassInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartMongeAmpereAffineInvariance

variable {e : ℕ}

theorem mulVec_cons_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (y : Fin e → ℂ) :
    T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) =
      Fin.cons (T 0 0) ((fun i => T i.succ 0) + (T.submatrix Fin.succ Fin.succ) *ᵥ y) := by
  funext p
  refine Fin.cases ?_ (fun i => ?_) p
  · simp [mulVec, dotProduct, Fin.sum_univ_succ, hT]
  · simp [mulVec, dotProduct, Fin.sum_univ_succ]

theorem det_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0) :
    T.det = T 0 0 * (T.submatrix Fin.succ Fin.succ).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [hT, Fin.succAbove_zero]

theorem hermChartPot_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (ht : T 0 0 ≠ 0) (y : Fin e → ℂ) :
    hermChartPot (Tᴴ * M * T) y =
      hermChartPot M ((T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) +
        Real.log ‖T 0 0‖ := by
  set w : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) + ((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y with hw
  set u : Fin (e + 1) → ℂ := Fin.cons 1 w with hu
  have hTv : T *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ) = T 0 0 • u := by
    rw [mulVec_cons_of_row_zero T hT]
    funext p
    refine Fin.cases ?_ (fun i => ?_) p
    · simp [u]
    · have hm : (((T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ) *ᵥ y) i =
          (T 0 0)⁻¹ * ((T.submatrix Fin.succ Fin.succ) *ᵥ y) i := by
        simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      simp only [u, w, Fin.cons_succ, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hm]
      field_simp
  have hq : star (Fin.cons 1 y : Fin (e + 1) → ℂ) ⬝ᵥ ((Tᴴ * M * T) *ᵥ (Fin.cons 1 y : Fin (e + 1) → ℂ)) =
      (Complex.normSq (T 0 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (T 0 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr ht) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem chartMass_conj (M T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef)
    (hT : ∀ j : Fin e, T 0 j.succ = 0) (hdet : T.det ≠ 0) :
    chartMass (Tᴴ * M * T) = chartMass M := by
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set C := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hCdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hC' : C.det ≠ 0 := by
    rw [hCdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfun : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + C *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  unfold chartMass
  rw [hfun]
  simp_rw [maDensity_comp_affine (hermChartPot M) c C hC']
  rw [integral_const_mul, integral_comp_affine (maDensity fun _ => hermChartPot M) c C hC', ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hC').ne', one_mul]

end ChartMongeAmpereAffineInvariance


open ChartMongeAmpereAffineInvariance in
theorem ChartMassInvariant.proof : ChartMassInvariant.Statement := by
  intro e M hM
  let S : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := M
  have hS : S.PosDef := hM
  let P₀ : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := LDL.lowerInv hS
  let P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := P₀
  have hPdet : P.det ≠ 0 := (isUnit_det_of_invertible P₀).ne_zero
  set T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Pᴴ with hTdef
  have hT : ∀ j : Fin e, T 0 j.succ = 0 := fun j => by
    have h := LDL.isLowerTriangular_lowerInv hS (i := OrderDual.toDual j.succ) (j := OrderDual.toDual 0)
      (OrderDual.toDual_lt_toDual.mpr (Fin.succ_pos j))
    rw [hTdef, conjTranspose_apply, show P j.succ 0 = 0 from h, star_zero]
  have hTdet : T.det ≠ 0 := by
    rw [hTdef, det_conjTranspose]
    exact star_ne_zero.mpr hPdet
  let d₀ : (Fin (e + 1))ᵒᵈ → ℂ := LDL.diagEntries hS
  set d : Fin (e + 1) → ℂ := d₀ with hddef
  have hD : Tᴴ * M * T = diagonal d := by
    rw [hTdef, conjTranspose_conjTranspose]
    exact (LDL.diag_eq_lowerInv_conj hS).symm
  have hDpos : (diagonal d).PosDef := by
    rw [← hD]
    exact hM.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hTdet)))
  have hdpos : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  set T' : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := diagonal fun i => ((Real.sqrt (d i).re)⁻¹ : ℝ) with hT'def
  have hT' : ∀ j : Fin e, T' 0 j.succ = 0 := fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm
  have hT'det : T'.det ≠ 0 := by
    rw [hT'def, det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (Complex.pos_iff.mp (hdpos i)).1).ne')
  have h1 : T'ᴴ * diagonal d * T' = 1 := by
    rw [hT'def, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    obtain ⟨hr, him⟩ := Complex.pos_iff.mp (hdpos i)
    set r := (d i).re with hrdef
    have hdi : d i = (r : ℂ) := Complex.ext (by simp [hrdef]) (by simp [← him])
    have key : (Real.sqrt r)⁻¹ * r * (Real.sqrt r)⁻¹ = 1 := by
      have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
      rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne']
    rw [hdi, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast key
  calc chartMass M = chartMass (Tᴴ * M * T) := (chartMass_conj M T hM hT hTdet).symm
    _ = chartMass (diagonal d) := by rw [hD]
    _ = chartMass (T'ᴴ * diagonal d * T') := (chartMass_conj _ T' hDpos hT' hT'det).symm
    _ = chartMass 1 := by rw [h1]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real

noncomputable section

namespace PGaussConstant

theorem rhs_eq (n : ℕ) :
    (72 * Real.exp 4 * (n : ℝ)) ^ ((n : ℝ) / 2) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
  have hx : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : 0 ≤ 6 * √2 * Real.exp 2 * √(n : ℝ) := by positivity
  have hsq : 72 * Real.exp 4 * (n : ℝ) = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2 := by
    have h4 : Real.exp 2 ^ 2 = Real.exp 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ 2
        = 36 * (√2) ^ 2 * (Real.exp 2) ^ 2 * (√(n : ℝ)) ^ 2 := by ring
    rw [this, Real.sq_sqrt (by norm_num), Real.sq_sqrt hx, h4]
    ring
  rw [hsq, ← Real.rpow_natCast (6 * √2 * Real.exp 2 * √(n : ℝ)) 2, ← Real.rpow_mul ha,
    ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

theorem exp_part (n : ℕ) (hn : 1 ≤ n) :
    2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))) ≤ 2 ^ n * Real.exp 2 ^ n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hs : √(n : ℝ) ≤ n := by
    have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hpi : (n : ℝ) / (2 * π) ≤ n := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have he : Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)) ≤ Real.exp 2 ^ n := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul h2 he (by positivity) (by positivity)

end PGaussConstant


open PGaussConstant in
theorem GaussConstant.proof : GaussConstant.Statement := by
  intro n hn
  rw [PGaussConstant.rhs_eq, gaussShellConst]
  have key := PGaussConstant.exp_part n hn
  have hc : 0 ≤ √2 ^ n * 3 ^ n * √(n : ℝ) ^ n := by positivity
  calc √2 ^ n * (2 * (3 ^ n * √(n : ℝ) ^ n * Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π))))
      = (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) *
          (2 * (Real.exp √(n : ℝ) * Real.exp ((n : ℝ) / (2 * π)))) := by ring
    _ ≤ (√2 ^ n * 3 ^ n * √(n : ℝ) ^ n) * (2 ^ n * Real.exp 2 ^ n) :=
        mul_le_mul_of_nonneg_left key hc
    _ = (6 * √2 * Real.exp 2 * √(n : ℝ)) ^ n := by
        rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp only [mul_pow]; ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDetFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PGaussDetFactor

lemma rpow_neg_half_sq {d : ℝ} (hd : 0 < d) : (d ^ (-(1 / 2 : ℝ))) ^ 2 = d⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
  norm_num
  exact Real.rpow_neg_one d

end PGaussDetFactor


open PGaussDetFactor in
theorem GaussDetFactor.proof : GaussDetFactor.Statement := by
  intro g Y B hY hBY
  have hd : 0 < Y.det := hY.det_pos
  have hsq : B.det ^ 2 = (1 / 2 : ℝ) ^ g * Y.det := by
    have := congrArg Matrix.det hBY
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at this
    rw [sq]; exact this
  have hB0 : 0 < |B.det| := by
    have : B.det ^ 2 ≠ 0 := by rw [hsq]; positivity
    exact abs_pos.mpr (fun h => this (by rw [h]; ring))
  have hL : 0 ≤ |B.det|⁻¹ := (inv_pos.mpr hB0).le
  have hR : 0 ≤ √2 ^ g * Y.det ^ (-(1 / 2 : ℝ)) := by positivity
  refine (pow_left_inj₀ hL hR (two_ne_zero)).mp ?_
  rw [inv_pow, sq_abs, hsq, mul_pow, rpow_neg_half_sq hd, ← pow_mul, mul_comm g 2, pow_mul,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [mul_inv, one_div, inv_pow, inv_inv]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussFourierSelf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Real MeasureTheory
open scoped FourierTransform

namespace PGaussFourierSelf

lemma ofReal_gauss {V : Type*} [NormedAddCommGroup V] (x : V) :
    ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ) = Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end PGaussFourierSelf

theorem GaussFourierSelf.proof : GaussFourierSelf.Statement := by
  intro g w
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hfun : (fun x : EuclideanSpace ℝ (Fin g) => ((Real.exp (-π * ‖x‖ ^ 2) : ℝ) : ℂ)) =
      fun x => Complex.exp (-(π : ℂ) * (‖x‖ : ℂ) ^ 2) := by
    funext x
    exact PGaussFourierSelf.ofReal_gauss x
  rw [hfun, fourier_gaussian_innerProductSpace hb w, PGaussFourierSelf.ofReal_gauss w]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_self hpi, Complex.one_cpow, one_mul]
  congr 1
  field_simp

end GroundTheory.Heights₂.Heights
end

