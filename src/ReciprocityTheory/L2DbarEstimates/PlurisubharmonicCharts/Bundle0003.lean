module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0062

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourBasic
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem fourBasic_cube_vol (f : ℕ) :
    volume (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)) = 1 := by
  rw [MeasureTheory.volume_pi_pi]; simp [Real.volume_Ioc]

theorem fourBasic_norm_exp {f : ℕ} (ν : Fin f → ℤ) (x b : Fin f → ℝ) :
    ‖Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))‖ =
      Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
  have hsplit : (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) + ((∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have harg : -2 * Real.pi * Complex.I *
        (∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)) =
      ((2 * Real.pi * ∑ k, (ν k : ℝ) * b k : ℝ) : ℂ) +
        ((-2 * Real.pi * ∑ k, (ν k : ℝ) * x k : ℝ) : ℂ) * Complex.I := by
    rw [hsplit]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * ∑ k, (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq
  rw [harg, Complex.norm_exp]
  congr 1
  simp

theorem four_bound (f : ℕ) : FOURBoundStatement f := by
  intro h b ν C hC
  have hint_r : ‖fourCoeff h b ν‖ ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) := by
    unfold fourCoeff
    have : IsFiniteMeasure
        (volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1))) :=
      ⟨by rw [Measure.restrict_apply_univ, fourBasic_cube_vol]; exact ENNReal.one_lt_top⟩
    have hle := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1)))
      (f := fun x : Fin f → ℝ => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
        Complex.exp (-2 * Real.pi * Complex.I *
          ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I)))
      (C := C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k))
      (ae_of_all _ fun x => by
        rw [norm_mul, fourBasic_norm_exp]
        exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le)
    simpa [Measure.real, Measure.restrict_apply_univ, fourBasic_cube_vol] using hle
  have h1 : Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
      Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) = 1 := by
    rw [← Real.exp_add]
    rw [show 2 * Real.pi * ∑ k, (ν k : ℝ) * b k + -2 * Real.pi * ∑ k, (ν k : ℝ) * b k = 0 by ring]
    exact Real.exp_zero
  calc ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k)
      ≤ C * Real.exp (2 * Real.pi * ∑ k, (ν k : ℝ) * b k) *
          Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) :=
        mul_le_mul_of_nonneg_right hint_r (Real.exp_pos _).le
    _ = C := by rw [mul_assoc, h1, mul_one]

theorem four_sign (f : ℕ) (hI : FOURIndepStatement f) (hB : FOURBoundStatement f) :
    FOURSignStatement f := by
  intro Ω h b0 κ C E hΩ hpre hd hper hray hgrowth ν hne
  by_contra hneg0
  have hneg := not_le.mp hneg0
  obtain ⟨S0, hS0⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * b0 k := ⟨_, rfl⟩
  obtain ⟨Sκ, hSκ⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * κ k := ⟨_, rfl⟩
  rw [← hSκ] at hneg
  have hb0 : b0 ∈ Ω := by simpa using hray 0 le_rfl
  have hsum : ∀ t : ℝ, ∑ k, (ν k : ℝ) * (b0 + t • κ) k = S0 + t * Sκ := by
    intro t
    rw [hS0, hSκ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -2 * Real.pi * Sκ := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβ]; nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hneg)]
  have hK : 0 < ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) :=
    mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)
  have hle : ∀ t : ℝ, 0 ≤ t → ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) ≤
      C * ((1 + t) ^ E * Real.exp (-β * t)) := by
    intro t ht
    have hcoef := hI Ω h hΩ hpre hd hper b0 hb0 (b0 + t • κ) (hray t ht) ν
    have hbd := hB h (b0 + t • κ) ν (C * (1 + t) ^ E) (hgrowth t ht)
    rw [← hcoef, hsum t] at hbd
    have hexp : Real.exp (-2 * Real.pi * (S0 + t * Sκ)) =
        Real.exp (-2 * Real.pi * S0) * Real.exp (β * t) := by
      rw [← Real.exp_add, hβ]; congr 1; ring
    rw [hexp] at hbd
    have h1 : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
      rw [← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]
    calc ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0)
        = ‖fourCoeff h b0 ν‖ * (Real.exp (-2 * Real.pi * S0) * Real.exp (β * t)) *
            Real.exp (-β * t) := by
          linear_combination (-(‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0))) * h1
      _ ≤ C * (1 + t) ^ E * Real.exp (-β * t) :=
          mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
      _ = C * ((1 + t) ^ E * Real.exp (-β * t)) := by ring
  have hlim : Tendsto (fun t : ℝ => C * ((1 + t) ^ E * Real.exp (-β * t))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero E β hβpos
    have h2 : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_of_nonneg_left zero_le_one) tendsto_id
    have h3 := (h1.comp h2).const_mul (Real.exp β)
    rw [mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => (1 + t) ^ E * Real.exp (-β * t)) atTop (𝓝 0) := by
      refine h3.congr fun t => ?_
      have he : Real.exp β * Real.exp (-β * (1 + t)) = Real.exp (-β * t) := by
        rw [← Real.exp_add]; congr 1; ring
      show Real.exp β * ((1 + t) ^ E * Real.exp (-β * (1 + t))) = _
      rw [← he]; ring
    have h5 := h4.const_mul C
    rwa [mul_zero] at h5
  have hfin := ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hle t ht)
  linarith

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSum
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

def fsProj (f : ℕ) : (Fin f → ℝ) → UnitAddTorus (Fin f) := fun t i => (t i : UnitAddCircle)

theorem fsProj_isOpenQuotientMap (f : ℕ) : IsOpenQuotientMap (fsProj f) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

theorem fsProj_eq {f : ℕ} (s t : Fin f → ℝ) (h : fsProj f s = fsProj f t) :
    ∃ n : Fin f → ℤ, t = s + fun i => (n i : ℝ) := by
  have hi : ∀ i, ∃ k : ℤ, t i = s i + k := by
    intro i
    have h1 : ((s i : ℝ) : UnitAddCircle) = (t i : UnitAddCircle) := congrFun h i
    have h2 : (((t i - s i : ℝ)) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, h1, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h2
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hk
    linarith
  choose n hn using hi
  exact ⟨n, funext fun i => by simp [hn i]⟩

def fsFun {f : ℕ} (g : (Fin f → ℝ) → ℂ) : UnitAddTorus (Fin f) → ℂ :=
  fun θ => g (Function.surjInv (fsProj_isOpenQuotientMap f).surjective θ)

theorem fsFun_proj {f : ℕ} (g : (Fin f → ℝ) → ℂ)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) (t : Fin f → ℝ) :
    fsFun g (fsProj f t) = g t := by
  unfold fsFun
  set s := Function.surjInv (fsProj_isOpenQuotientMap f).surjective (fsProj f t)
  have hs : fsProj f s = fsProj f t := Function.surjInv_eq _ _
  obtain ⟨n, hn⟩ := fsProj_eq s t hs
  rw [hn, hper]

theorem fsFun_continuous {f : ℕ} (g : (Fin f → ℝ) → ℂ) (hg : Continuous g)
    (hper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x) :
    Continuous (fsFun g) := by
  rw [(fsProj_isOpenQuotientMap f).isQuotientMap.continuous_iff]
  have : fsFun g ∘ fsProj f = g := funext fun t => fsFun_proj g hper t
  rw [this]; exact hg

theorem fs_mFourier_proj {f : ℕ} (m : Fin f → ℤ) (t : Fin f → ℝ) :
    UnitAddTorus.mFourier m (fsProj f t) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (m k : ℂ) * (t k : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fsProj, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem four_sum (f : ℕ) : FOURSumStatement f := by
  intro Ω h hΩ hh hper h0 hsum x
  set g : (Fin f → ℝ) → ℂ := fun x => h (fun k => (x k : ℂ)) with hgdef
  have hreal : ∀ y : Fin f → ℝ, (fun k => ((y k : ℝ) : ℂ)) ∈ tube f Ω := by
    intro y
    show (fun k => ((y k : ℝ) : ℂ).im) ∈ Ω
    have e : (fun k => (((y k : ℝ) : ℂ)).im) = 0 := by funext k; simp
    rw [e]; exact h0
  have hg : Continuous g := by
    have hc : Continuous (fun y : Fin f → ℝ => (fun k => ((y k : ℝ) : ℂ))) := by fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
    exact ((hh _ (hreal y)).differentiableAt (hopen.mem_nhds (hreal y))).continuousAt.comp
      hc.continuousAt
  have hgper : ∀ x (n : Fin f → ℤ), g (x + fun i => (n i : ℝ)) = g x := by
    intro y n
    have := hper _ (hreal y) n
    simp only [hgdef]
    convert this using 2
    funext k
    simp only [Pi.add_apply, Complex.ofReal_add, Complex.ofReal_intCast]
  let F : C(UnitAddTorus (Fin f), ℂ) := ⟨fsFun g, fsFun_continuous g hg hgper⟩
  have hcoef : ∀ ν, UnitAddTorus.mFourierCoeff F ν = fourCoeff h 0 ν := by
    intro ν
    rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
    have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
        : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp
    rw [hset]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
    have h2 : F (fsProj f t) = g t := fsFun_proj g hgper t
    beta_reduce
    rw [h1, h2, smul_eq_mul, fs_mFourier_proj]
    simp only [hgdef, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, Pi.neg_apply, Int.cast_neg]
    rw [mul_comm]
    congr 2
    simp [Finset.sum_neg_distrib]
  have hs : Summable (UnitAddTorus.mFourierCoeff F) := by
    refine Summable.of_norm ?_
    simpa [hcoef] using hsum
  have := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (fsProj f x)
  simp only [hcoef, smul_eq_mul, fs_mFourier_proj] at this
  rw [show F (fsProj f x) = g x from fsFun_proj g hgper x] at this
  exact this

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.RegMaxA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

variable {n : ℕ}

lemma rm_wdb_ofReal_eventually (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (k : Fin n) :
    wdb n k (fun x => (F x : ℂ)) =ᶠ[𝓝 y] fun x =>
      (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
        Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2 := by
  filter_upwards [hF.eventually (by simp)] with x hx
  have hd : HasFDerivAt (fun x => (F x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ F x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hx.differentiableAt (by norm_num)).hasFDerivAt
  unfold wdb
  rw [hd.fderiv]
  simp

lemma rm_hasFDerivAt_fderiv_apply_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y)
    (w : V n) :
    HasFDerivAt (fun x => ((fderiv ℝ F x w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ F) y).flip w)) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) y := hF.fderiv_right (by norm_num)
  have h2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) y) y :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  have h3 : HasFDerivAt (fun x => fderiv ℝ F x w) ((fderiv ℝ (fderiv ℝ F) y).flip w) y := by
    have := h2.clm_apply (hasFDerivAt_const w y)
    rw [ContinuousLinearMap.comp_zero, zero_add] at this
    exact this
  exact Complex.ofRealCLM.hasFDerivAt.comp y h3

lemma rm_wd_wdb_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (j k : Fin n) :
    wd n j (wdb n k (fun x => (F x : ℂ))) y =
      (((fderiv ℝ (fderiv ℝ F) y (bas n j) (bas n k) : ℝ) : ℂ)
        + Complex.I * ((fderiv ℝ (fderiv ℝ F) y (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
        - Complex.I * ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (bas n k) : ℝ) : ℂ)
        + ((fderiv ℝ (fderiv ℝ F) y (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)) / 4 := by
  have hS := (rm_hasFDerivAt_fderiv_apply_ofReal F y hF (bas n k)).add
    ((rm_hasFDerivAt_fderiv_apply_ofReal F y hF (Complex.I • bas n k)).const_mul Complex.I)
  have hG := HasFDerivAt.const_mul (𝔸 := ℂ) hS ((2 : ℂ)⁻¹)
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (rm_wdb_ofReal_eventually F y hF k)
  have hfun : (fun x => (((fderiv ℝ F x (bas n k) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ F x (Complex.I • bas n k) : ℝ) : ℂ)) / 2) =
      fun x => (2 : ℂ)⁻¹ * (((fun x => ((fderiv ℝ F x (bas n k) : ℝ) : ℂ)) +
        fun y => Complex.I * ((fderiv ℝ F y (Complex.I • bas n k) : ℝ) : ℂ)) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold wd
  rw [hfd, hfun, hG.fderiv]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

def rmVec (ξ : Fin n → ℂ) : V n := ∑ j, ξ j • bas n j

lemma rm_cplx_smul_eq (z : ℂ) (x : V n) : z • x = z.re • x + z.im • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

lemma rm_bil_expand (B : V n →L[ℝ] V n →L[ℝ] ℝ) (z w : ℂ) (a b : V n) :
    B (z • a) (w • b) = z.re * w.re * B a b + z.re * w.im * B a (Complex.I • b)
      + z.im * w.re * B (Complex.I • a) b + z.im * w.im * B (Complex.I • a) (Complex.I • b) := by
  rw [rm_cplx_smul_eq z a, rm_cplx_smul_eq w b]
  simp only [map_add (f := _), map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma rm_bil_sum (B : V n →L[ℝ] V n →L[ℝ] ℝ) (c : Fin n → ℂ) :
    B (∑ j, c j • bas n j) (∑ k, c k • bas n k) = ∑ j, ∑ k, B (c j • bas n j) (c k • bas n k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_comm

lemma rm_I_smul_vec (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]

theorem rm_levi_re_ofReal (F : V n → ℝ) (y : V n) (hF : ContDiffAt ℝ 2 F y) (ξ : Fin n → ℂ) :
    4 * (leviV n (fun x => (F x : ℂ)) y ξ).re =
      fderiv ℝ (fderiv ℝ F) y (rmVec ξ) (rmVec ξ) +
        fderiv ℝ (fderiv ℝ F) y (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec]
  unfold rmVec
  rw [rm_bil_sum, rm_bil_sum, ← Finset.sum_add_distrib]
  unfold leviV
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_wd_wdb_ofReal F y hF j k, rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (ξ j) (ξ k),
    rm_bil_expand (fderiv ℝ (fderiv ℝ F) y) (Complex.I * ξ j) (Complex.I * ξ k)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section Newton

open Polynomial

private theorem trace_pow_eq_zero_of_le_dim {K : Type*} [Field K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    ∀ k, 1 ≤ k → (N ^ k).trace = 0 := by
  first | exact UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim .. | (apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> assumption) | (apply @UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim <;> first | assumption | infer_instance)

private theorem trace_aeval_X_mul {K : Type*} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) (p : K[X]) :
    (aeval N (X * p)).trace = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add (f := _), Matrix.trace_add, hp, hq, add_zero]
  | monomial n a =>
    rw [show (X * monomial n a : K[X]) = monomial (n + 1) a by
      rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]; ring]
    rw [aeval_monomial, ← Algebra.smul_def, Matrix.trace_smul, h, smul_zero]

private theorem isNilpotent_of_trace_pow_succ {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (h : ∀ k : ℕ, (N ^ (k + 1)).trace = 0) : IsNilpotent N := by
  classical
  have hint : IsIntegral K N := Algebra.IsIntegral.isIntegral N
  have hμ : minpoly K N ≠ 0 := minpoly.ne_zero hint
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K N) hμ 0
  set m := (minpoly K N).rootMultiplicity 0
  simp only [map_zero, sub_zero] at hq hnd
  have hcop : IsCoprime (X ^ (m + 1)) q :=
    ((Polynomial.irreducible_X).coprime_iff_not_dvd.mpr hnd).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hXq : aeval N (X ^ (m + 1) * q) = 0 := by
    rw [show (X ^ (m + 1) * q : K[X]) = X * minpoly K N by rw [hq]; ring, map_mul,
      minpoly.aeval, mul_zero]
  have h1 : aeval N (u * X ^ (m + 1)) + aeval N (v * q) = 1 := by
    rw [← map_add (f := _), huv, map_one]
  have hprod : aeval N (u * X ^ (m + 1)) * aeval N (v * q) = 0 := by
    rw [← map_mul, show (u * X ^ (m + 1) * (v * q) : K[X]) = u * v * (X ^ (m + 1) * q) by ring,
      map_mul, hXq, mul_zero]
  set e := aeval N (u * X ^ (m + 1)) with he_def
  have he : IsIdempotentElem e := by
    have : aeval N (v * q) = 1 - e := by rw [← h1]; abel
    rw [this, mul_sub, mul_one, sub_eq_zero] at hprod
    exact hprod.symm
  have hτ : e.trace = 0 := by
    rw [he_def, show (u * X ^ (m + 1) : K[X]) = X * (u * X ^ m) by ring]
    exact trace_aeval_X_mul N h _
  have hle : IsIdempotentElem (Matrix.toLin' e) := by
    have h3 := Matrix.toLin'_mul e e
    rw [he.eq] at h3
    exact h3.symm
  have hl0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hle (by rw [Matrix.trace_toLin'_eq, hτ])
  have he0 : e = 0 := Matrix.toLin'.map_eq_zero_iff.mp hl0
  have hvq : aeval N (v * q) = 1 := by rw [← h1, he0, zero_add]
  refine ⟨m + 1, ?_⟩
  calc N ^ (m + 1) = N ^ (m + 1) * aeval N (v * q) := by rw [hvq, mul_one]
    _ = aeval N (v * (X ^ (m + 1) * q)) := by
        rw [show (v * (X ^ (m + 1) * q) : K[X]) = X ^ (m + 1) * (v * q) by ring,
          map_mul (aeval N) (X ^ (m + 1)), map_pow, aeval_X]
    _ = 0 := by rw [map_mul, hXq, mul_zero]

end Newton

theorem isNilpotent_of_trace_pow {K : Type*} [Field K] [CharZero K] (r : ℕ)
    (N : Matrix (Fin r) (Fin r) K) (h : ∀ k, 1 ≤ k → k ≤ r → (N ^ k).trace = 0) :
    IsNilpotent N :=
  isNilpotent_of_trace_pow_succ N fun k => trace_pow_eq_zero_of_le_dim r N h (k + 1) (by omega)

end

end ReciprocityTheory.L2DbarEstimates.Y
end

