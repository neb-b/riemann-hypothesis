module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal ComplexConjugate

noncomputable section

def dbv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ + I * D (I • ζ)) / 2

def dv {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) : ℂ := (D ζ - I * D (I • ζ)) / 2

theorem clm_smul_decomp {n : ℕ} (D : V n →L[ℝ] ℂ) (c : ℂ) (e : V n) :
    D (c • e) = c.re * D e + c.im * D (I • e) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add (f := _), D.map_smul, D.map_smul,
    Complex.real_smul, Complex.real_smul]

theorem vec_expand {n : ℕ} (w : V n) : w = ∑ j, w j • bas n j := by
  have h := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr w
  conv_lhs => rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  rfl

private theorem clm_apply_eq_sum_re_im_basis {n : ℕ} (D : V n →L[ℝ] ℂ) (ζ : V n) :
    D ζ = ∑ k, ((ζ k).re * D (bas n k) + (ζ k).im * D (I • bas n k)) := by
  conv_lhs => rw [vec_expand ζ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => clm_smul_decomp D (ζ k) (bas n k)

theorem sum_wdb_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wdb n k g y * conj (ζ k) = dbv (fderiv ℝ g y) ζ := by
  unfold dbv
  rw [clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wdb, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  apply Complex.ext <;> simp <;> ring

theorem sum_wd_eq {n : ℕ} (g : V n → ℂ) (y : V n) (ζ : V n) :
    ∑ k, wd n k g y * ζ k = dv (fderiv ℝ g y) ζ := by
  unfold dv
  rw [clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) ζ, clm_apply_eq_sum_re_im_basis (fderiv ℝ g y) (I • ζ), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [wd, PiLp.smul_apply, smul_eq_mul, Complex.I_mul_re, Complex.I_mul_im]
  apply Complex.ext <;> simp <;> ring

theorem leviV_eq_dv {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (ξ : Fin n → ℂ) :
    leviV n g y ξ =
      dv (fderiv ℝ (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) y) (WithLp.toLp 2 ξ) := by
  have hF : DifferentiableAt ℝ (fderiv ℝ g) y :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd : ∀ k, DifferentiableAt ℝ (wdb n k g) y := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ g v (I • bas n k)) y :=
      hF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ g v (bas n k) + I * fderiv ℝ g v (I • bas n k)) y :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hsum : (fun v => dbv (fderiv ℝ g v) (WithLp.toLp 2 ξ)) =
      fun v => ∑ k, wdb n k g v * conj (ξ k) := by
    funext v
    rw [← sum_wdb_eq]
  have hD : HasFDerivAt (fun v => ∑ k, wdb n k g v * conj (ξ k))
      (∑ k, conj (ξ k) • fderiv ℝ (wdb n k g) y) y :=
    HasFDerivAt.fun_sum fun k _ => (hd k).hasFDerivAt.mul_const (conj (ξ k))
  rw [hsum, ← sum_wd_eq]
  unfold leviV
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [wd]
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  change _ = _ * ξ j
  ring

theorem dbv_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hf : DifferentiableAt ℝ f (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dbv (fderiv ℝ (f ∘ Φ) v) ζ = dbv (fderiv ℝ f (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hf (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dbv]

theorem leviV_log_normSq {n : ℕ} {G : V n → ℂ} {x : V n} (hG : ContDiffAt ℂ 2 G x)
    (h0 : G x ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (Complex.normSq (G v)) : ℝ) : ℂ)) x ξ = 0 := by
  have hv := contDiffAt_normSq_comp hG
  have hpos : 0 < Complex.normSq (G x) := Complex.normSq_pos.2 h0
  have hk : ContDiffAt ℝ 2 Real.log (Complex.normSq (G x)) := Real.contDiffAt_log.2 hpos.ne'
  have h := leviChain n Real.log (fun y => Complex.normSq (G y)) x ξ hv hk
  rw [h, leviV_normSq_comp hG]
  simp only [wd_normSq_comp hG]
  have hfac : ∑ j, wd n j G x * conj (G x) * ξ j = conj (G x) * ∑ j, wd n j G x * ξ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, Complex.normSq_mul, Complex.normSq_conj, Real.deriv_log', deriv_inv]
  have hne : (Complex.normSq (G x) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  ring

private theorem dv_fderiv_comp_holomorphic {n : ℕ} {h : V n → ℂ} {Φ : V n → V n} {v : V n}
    (hh : DifferentiableAt ℝ h (Φ v)) (hΦ : DifferentiableAt ℂ Φ v) (ζ : V n) :
    dv (fderiv ℝ (h ∘ Φ) v) ζ = dv (fderiv ℝ h (Φ v)) (fderiv ℂ Φ v ζ) := by
  rw [fderiv_comp v hh (hΦ.restrictScalars ℝ), hΦ.fderiv_restrictScalars ℝ]
  simp [dv]

private theorem dv_fderiv_conj_holomorphic_eq_zero {n : ℕ} {c : V n → ℂ} {y : V n} (hc : DifferentiableAt ℂ c y)
    (ζ : V n) : dv (fderiv ℝ (fun v => conj (c v)) y) ζ = 0 := by
  have h := (hc.restrictScalars ℝ).hasFDerivAt.star
  have hL : fderiv ℂ c y (I • ζ) = I * fderiv ℂ c y ζ := by rw [map_smul, smul_eq_mul]
  have hfun : (fun v => conj (c v)) = fun v => star (c v) := rfl
  rw [hfun, h.fderiv, hc.fderiv_restrictScalars ℝ]
  simp only [dv, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', hL]
  simp only [ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem dv_add' {n : ℕ} (L M : V n →L[ℝ] ℂ) (ζ : V n) :
    dv (L + M) ζ = dv L ζ + dv M ζ := by
  simp only [dv, ContinuousLinearMap.add_apply]
  ring

private theorem dv_sum_smul {n : ℕ} (a : Fin n → ℂ) (L : Fin n → V n →L[ℝ] ℂ) (ζ : V n) :
    dv (∑ k, a k • L k) ζ = ∑ k, a k * dv (L k) ζ := by
  simp only [dv, ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem leviV_comp {n : ℕ} {f : V n → ℂ} {Φ : V n → V n} {y : V n}
    (hf : ContDiffAt ℝ 2 f (Φ y)) (hΦ : ContDiffAt ℂ 2 Φ y) (ξ : Fin n → ℂ) :
    leviV n (f ∘ Φ) y ξ = leviV n f (Φ y) (fderiv ℂ Φ y (WithLp.toLp 2 ξ)).ofLp := by
  have hΦR : ContDiffAt ℝ 2 Φ y := hΦ.restrict_scalars ℝ
  rw [leviV_eq_dv (hf.comp y hΦR) ξ, leviV_eq_dv hf]
  simp only [WithLp.toLp_ofLp]
  have hfF : DifferentiableAt ℝ (fderiv ℝ f) (Φ y) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA : ∀ k, DifferentiableAt ℝ (wdb n k f) (Φ y) := by
    intro k
    unfold wdb
    have h1 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h2 : DifferentiableAt ℝ (fun v => fderiv ℝ f v (I • bas n k)) (Φ y) :=
      hfF.clm_apply (differentiableAt_const _)
    have h3 : DifferentiableAt ℝ
        (fun v => fderiv ℝ f v (bas n k) + I * fderiv ℝ f v (I • bas n k)) (Φ y) :=
      h1.add (h2.const_mul I)
    simpa only [div_eq_mul_inv] using h3.mul_const (2⁻¹ : ℂ)
  have hΦd : DifferentiableAt ℂ Φ y := hΦ.differentiableAt (by norm_num)
  have hDΦ : DifferentiableAt ℂ (fderiv ℂ Φ) y :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : ∀ k, DifferentiableAt ℂ (fun v => (fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) y := fun k =>
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiableAt.comp y
      (hDΦ.clm_apply (differentiableAt_const _))
  have hev : (fun v => dbv (fderiv ℝ (f ∘ Φ) v) (WithLp.toLp 2 ξ)) =ᶠ[𝓝 y]
      fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k) := by
    have h1 : ∀ᶠ v in 𝓝 y, ContDiffAt ℝ 2 f (Φ v) :=
      hΦd.continuousAt.eventually (hf.eventually (by simp))
    have h2 : ∀ᶠ v in 𝓝 y, ContDiffAt ℂ 2 Φ v := hΦ.eventually (by simp)
    filter_upwards [h1, h2] with v hv1 hv2
    rw [dbv_comp (hv1.differentiableAt (by norm_num)) (hv2.differentiableAt (by norm_num)),
      ← sum_wdb_eq]
  have hK : HasFDerivAt
      (fun v => ∑ k, wdb n k f (Φ v) * conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
      (∑ k, (wdb n k f (Φ y) • fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y +
        conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f ∘ Φ) y)) y := by
    refine HasFDerivAt.fun_sum fun k _ => ?_
    have ha : HasFDerivAt (wdb n k f ∘ Φ) (fderiv ℝ (wdb n k f ∘ Φ) y) y :=
      ((hA k).comp y (hΦd.restrictScalars ℝ)).hasFDerivAt
    have hb : HasFDerivAt (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k))
        (fderiv ℝ (fun v => conj ((fderiv ℂ Φ v (WithLp.toLp 2 ξ)) k)) y) y :=
      ((hc k).restrictScalars ℝ).star.hasFDerivAt
    exact ha.mul hb
  have hR : (fun w => dbv (fderiv ℝ f w) (fderiv ℂ Φ y (WithLp.toLp 2 ξ))) =
      fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) := by
    funext w
    rw [← sum_wdb_eq]
  have hRD : HasFDerivAt (fun w => ∑ k, wdb n k f w * conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k))
      (∑ k, conj ((fderiv ℂ Φ y (WithLp.toLp 2 ξ)) k) • fderiv ℝ (wdb n k f) (Φ y)) (Φ y) :=
    HasFDerivAt.fun_sum fun k _ => (hA k).hasFDerivAt.mul_const _
  rw [hev.fderiv_eq, hK.fderiv, hR, hRD.fderiv, Finset.sum_add_distrib, dv_add', dv_sum_smul,
    dv_sum_smul, dv_sum_smul]
  simp only [dv_fderiv_conj_holomorphic_eq_zero (hc _), mul_zero, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dv_fderiv_comp_holomorphic (hA k) hΦd]

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourMul
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

def FOURMulStatement' (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h1 h2 : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h1 (tube f Ω) → DifferentiableOn ℂ h2 (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h1 (s + fun k => (m k : ℂ)) = h1 s) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h2 (s + fun k => (m k : ℂ)) = h2 s) →
    ∀ b ∈ Ω, ∀ ν : Fin f → ℤ,
      HasSum (fun ν' : Fin f → ℤ => fourCoeff h1 b ν' * fourCoeff h2 b (ν - ν'))
        (fourCoeff (h1 * h2) b ν)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def fmLine {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) : (Fin f → ℝ) → ℂ :=
  fun x => h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)

theorem fm_coeff_star {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (i : Fin f → ℤ) :
    conj (UnitAddTorus.mFourierCoeff (⇑(star F)) i) = UnitAddTorus.mFourierCoeff (⇑F) (-i) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.star_apply, smul_eq_mul, neg_neg]
  rw [← integral_conj]
  congr 1
  funext t
  simp [UnitAddTorus.mFourier_neg]

theorem fm_coeff_shift {f : ℕ} (F : C(UnitAddTorus (Fin f), ℂ)) (ν i : Fin f → ℤ) :
    UnitAddTorus.mFourierCoeff (⇑(UnitAddTorus.mFourier (-ν) * F)) i =
      UnitAddTorus.mFourierCoeff (⇑F) (i + ν) := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.mul_apply, smul_eq_mul]
  congr 1
  funext t
  rw [neg_add, UnitAddTorus.mFourier_add]
  ring

theorem fm_conv {f : ℕ} (F1 F2 : C(UnitAddTorus (Fin f), ℂ)) (ν : Fin f → ℤ) :
    HasSum (fun ν' => UnitAddTorus.mFourierCoeff (⇑F1) ν' * UnitAddTorus.mFourierCoeff (⇑F2) (ν - ν'))
      (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
  have H := UnitAddTorus.hasSum_prod_mFourierCoeff ((star F1).toLp 2 volume ℂ)
    ((UnitAddTorus.mFourier (-ν) * F2).toLp 2 volume ℂ)
  have H2 : HasSum (fun i => UnitAddTorus.mFourierCoeff (⇑F1) (-i) *
      UnitAddTorus.mFourierCoeff (⇑F2) (i + ν)) (UnitAddTorus.mFourierCoeff (⇑F1 * ⇑F2) ν) := by
    convert (preTransparency := .reducible) H using 1
    · funext i
      rw [UnitAddTorus.mFourierCoeff_toLp, UnitAddTorus.mFourierCoeff_toLp, fm_coeff_star,
        fm_coeff_shift]
    · rw [UnitAddTorus.mFourierCoeff]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (star F1),
        ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ)
          (UnitAddTorus.mFourier (-ν) * F2)] with t h1 h2
      rw [h1, h2]
      simp
      ring
  rw [← (Equiv.neg (Fin f → ℤ)).hasSum_iff]
  convert H2 using 1
  funext i
  simp [sub_neg_eq_add, add_comm]

theorem fm_fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ)
    (hper : ∀ x (n : Fin f → ℤ), fmLine h b (x + fun i => (n i : ℝ)) = fmLine h b x)
    (ν : Fin f → ℤ) :
    fourCoeff h b ν = Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) *
      UnitAddTorus.mFourierCoeff (fsFun (fmLine h b)) ν := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ ν 0, fourCoeff]
  have hset : ({x : Fin f → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin f → ℝ) i) ((0 : Fin f → ℝ) i + 1)}
      : Set (Fin f → ℝ)) = Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1) := by
    ext x; simp
  rw [hset, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (fun i => ((t i : ℝ) : UnitAddCircle)) = fsProj f t := rfl
  beta_reduce
  rw [h1, fsFun_proj _ hper, smul_eq_mul, fs_mFourier_proj]
  simp only [fmLine]
  rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Pi.neg_apply, Int.cast_neg, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination (-2 * (Real.pi : ℂ) * (ν k : ℂ) * (b k : ℂ)) * Complex.I_sq

theorem four_mul' (f : ℕ) : FOURMulStatement' f := by
  intro Ω h1 h2 hΩ hd1 hd2 hp1 hp2 b hb ν
  have hopen : IsOpen (tube f Ω) := hΩ.preimage (by fun_prop)
  have hmem : ∀ x : Fin f → ℝ, (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) ∈ tube f Ω := by
    intro x
    show (fun k => ((x k : ℂ) + (b k : ℂ) * Complex.I).im) ∈ Ω
    convert hb using 1
    ext k
    simp [Complex.add_im]
  have hc : ∀ hh : (Fin f → ℂ) → ℂ, DifferentiableOn ℂ hh (tube f Ω) →
      Continuous (fmLine hh b) := by
    intro hh hd
    have hcc : Continuous (fun y : Fin f → ℝ => (fun k => (y k : ℂ) + (b k : ℂ) * Complex.I)) := by
      fun_prop
    refine continuous_iff_continuousAt.2 fun y => ?_
    exact ((hd _ (hmem y)).differentiableAt (hopen.mem_nhds (hmem y))).continuousAt.comp
      hcc.continuousAt
  have hper : ∀ hh : (Fin f → ℂ) → ℂ,
      (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, hh (s + fun k => (m k : ℂ)) = hh s) →
      ∀ x (n : Fin f → ℤ), fmLine hh b (x + fun i => (n i : ℝ)) = fmLine hh b x := by
    intro hh hp x n
    have := hp _ (hmem x) n
    simp only [fmLine]
    convert this using 2
    ext k
    simp only [Pi.add_apply, Complex.ofReal_add]
    have hn : ((n k : ℝ) : ℂ) = (n k : ℂ) := by norm_cast
    rw [hn]
    ring
  have hper12 : ∀ x (n : Fin f → ℤ),
      fmLine (h1 * h2) b (x + fun i => (n i : ℝ)) = fmLine (h1 * h2) b x := by
    intro x n
    show fmLine h1 b _ * fmLine h2 b _ = fmLine h1 b x * fmLine h2 b x
    rw [hper h1 hp1, hper h2 hp2]
  let F1 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h1 b), fsFun_continuous _ (hc h1 hd1) (hper h1 hp1)⟩
  let F2 : C(UnitAddTorus (Fin f), ℂ) :=
    ⟨fsFun (fmLine h2 b), fsFun_continuous _ (hc h2 hd2) (hper h2 hp2)⟩
  have e12 : fsFun (fmLine (h1 * h2) b) = ⇑F1 * ⇑F2 := rfl
  rw [fm_fourCoeff (h1 * h2) b hper12, e12]
  have H := (fm_conv F1 F2 ν).mul_left (Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)))
  refine H.congr_fun fun ν' => ?_
  rw [fm_fourCoeff h1 b (hper h1 hp1), fm_fourCoeff h2 b (hper h2 hp2)]
  have hE : Complex.exp (2 * Real.pi * ∑ k, (ν k : ℂ) * (b k : ℂ)) =
      Complex.exp (2 * Real.pi * ∑ k, (ν' k : ℂ) * (b k : ℂ)) *
        Complex.exp (2 * Real.pi * ∑ k, ((ν - ν') k : ℂ) * (b k : ℂ)) := by
    rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    ext k
    simp only [Pi.sub_apply, Int.cast_sub]
    ring
  rw [hE]
  simp only [F1, F2, ContinuousMap.coe_mk]
  ring

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
section
open Filter Topology Set
open scoped ContDiff

noncomputable section

namespace ReciprocityTheory.L2DbarEstimates.Y

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

theorem zd_fderiv_symm {k : ℕ} {g : E → ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F}
    {y : E} (h : ∀ᶠ z in 𝓝 y, ∀ (τ : Equiv.Perm (Fin k)) (w : Fin k → E), g z (w ∘ τ) = g z w)
    (τ : Equiv.Perm (Fin k)) (u : E) (w : Fin k → E) :
    fderiv ℂ g y u (w ∘ τ) = fderiv ℂ g y u w := by
  by_cases hg : DifferentiableAt ℂ g y
  · have hev : (fun z => g z (w ∘ τ)) =ᶠ[𝓝 y] fun z => g z w := h.mono fun z hz => hz τ w
    rw [← fderiv_continuousMultilinear_apply_const_apply hg (w ∘ τ) u,
      ← fderiv_continuousMultilinear_apply_const_apply hg w u, hev.fderiv_eq]
  · simp [fderiv_zero_of_not_differentiableAt hg]

theorem zd_iter_two_left (f : E → F) (k : ℕ) (y : E) (m : Fin (k + 2) → E) :
    iteratedFDeriv ℂ (k + 2) f y m =
      fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y (m 0) (m 1) (Fin.tail (Fin.tail m)) := by
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_eq_comp_left,
    LinearIsometryEquiv.comp_fderiv]
  simp [Fin.tail, Fin.succ_zero_eq_one]

theorem zd_iteratedFDeriv_comp_perm {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℂ ∞ f U) :
    ∀ k, ∀ y ∈ U, ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E),
      iteratedFDeriv ℂ k f y (v ∘ σ) = iteratedFDeriv ℂ k f y v := by
  intro k
  induction k with
  | zero =>
    intro y _ σ v
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro y hy
    have hmul : ∀ σ τ : Equiv.Perm (Fin (k + 1)),
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ σ) = iteratedFDeriv ℂ (k + 1) f y v) →
        (∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ) = iteratedFDeriv ℂ (k + 1) f y v) →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ ⇑(σ * τ)) =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro σ τ hσ hτ v
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ, hσ]
    have hstab : ∀ τ' : Equiv.Perm (Fin (k + 1)), τ' 0 = 0 →
        ∀ v : Fin (k + 1) → E, iteratedFDeriv ℂ (k + 1) f y (v ∘ τ') =
          iteratedFDeriv ℂ (k + 1) f y v := by
      intro τ' h0 v
      set p := Equiv.Perm.decomposeFin τ' with hpdef
      have hp : τ' = Equiv.Perm.decomposeFin.symm p := by rw [hpdef, Equiv.symm_apply_apply]
      have hp1 : p.1 = 0 := by
        have := Equiv.Perm.decomposeFin_symm_apply_zero p.1 p.2
        rw [Prod.mk.eta, ← hp, h0] at this
        exact this.symm
      have hτ : τ' = Equiv.Perm.decomposeFin.symm (0, p.2) := by
        conv_lhs => rw [hp]
        congr 1
        exact Prod.ext hp1 rfl
      rw [hτ, iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left]
      have e1 : (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) 0 = v 0 := by
        simp [Equiv.Perm.decomposeFin_symm_apply_zero]
      have e2 : Fin.tail (v ∘ ⇑(Equiv.Perm.decomposeFin.symm ((0 : Fin (k + 1)), p.2))) =
          Fin.tail v ∘ p.2 := by
        funext i
        simp [Fin.tail, Equiv.Perm.decomposeFin_symm_apply_succ]
      rw [e1, e2]
      refine zd_fderiv_symm ?_ p.2 (v 0) (Fin.tail v)
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih z hz
    rcases k with _ | k
    · intro σ v
      have hσ1 : σ = 1 := Equiv.ext fun i => Fin.ext (by
        have h1 := (σ i).isLt
        have h2 := i.isLt
        simp only [Equiv.Perm.coe_one, id_eq]
        omega)
      rw [hσ1]
      rfl
    have hswap01 : ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro v
      have hc : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
        (hf.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (by
          first
          | exact_mod_cast (le_top : ((2 + k : ℕ) : ℕ∞) ≤ ⊤)
          | (norm_cast; exact le_top)
          | exact le_top
          | (rw [← WithTop.coe_natCast, ← WithTop.coe_ofNat, ← WithTop.coe_add]; exact WithTop.coe_le_coe.2 le_top))
      have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
        hc.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
      rw [zd_iter_two_left, zd_iter_two_left]
      have e3 : Fin.tail (Fin.tail (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) 1))) =
          Fin.tail (Fin.tail v) := by
        funext i
        simp only [Fin.tail, Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
      rw [e3]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [hsym (v 1) (v 0)]
    have hswap : ∀ j : Fin (k + 2), ∀ v : Fin (k + 2) → E,
        iteratedFDeriv ℂ (k + 2) f y (v ∘ ⇑(Equiv.swap (0 : Fin (k + 2)) j)) =
          iteratedFDeriv ℂ (k + 2) f y v := by
      intro j
      by_cases hj0 : j = 0
      · subst hj0
        intro v
        rw [Equiv.swap_self]
        rfl
      by_cases hj1 : j = 1
      · subst hj1
        exact hswap01
      have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
      have hconj : Equiv.swap (1 : Fin (k + 2)) j * Equiv.swap 0 1 * Equiv.swap 1 j =
          Equiv.swap 0 j := by
        rw [Equiv.swap_mul_swap_mul_swap h01 (Ne.symm hj0), Equiv.swap_comm]
      have hfix : (Equiv.swap (1 : Fin (k + 2)) j) 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne h01 (Ne.symm hj0)
      rw [← hconj]
      exact hmul _ _ (hmul _ _ (hstab _ hfix) hswap01) (hstab _ hfix)
    intro σ v
    have hfix : (Equiv.swap 0 (σ 0) * σ) 0 = 0 := by
      simp [Equiv.swap_apply_right]
    rw [← Equiv.swap_mul_self_mul (0 : Fin (k + 2)) (σ 0) σ]
    exact hmul _ _ (hswap _) (hstab _ hfix) v

end ReciprocityTheory.L2DbarEstimates.Y
end
end

