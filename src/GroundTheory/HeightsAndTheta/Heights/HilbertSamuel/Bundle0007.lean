module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviFSInvariant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology ComplexConjugate

noncomputable section

namespace LeviFSInvariant

variable {J : Type} [Fintype J]

def sqSum (z : J → ℂ) : ℝ := ∑ p, ‖z p‖ ^ 2

def reInner (a : J → ℂ) : (J → ℂ) →L[ℝ] ℝ :=
  ∑ p, ((a p).re • (Complex.reCLM.comp (ContinuousLinearMap.proj p)) +
    (a p).im • (Complex.imCLM.comp (ContinuousLinearMap.proj p)))

theorem reInner_apply (a b : J → ℂ) :
    reInner a b = ∑ p, ((a p).re * (b p).re + (a p).im * (b p).im) := by
  simp [reInner]

theorem reInner_comm (a b : J → ℂ) : reInner a b = reInner b a := by
  simp only [reInner_apply]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem reInner_self (a : J → ℂ) : reInner a a = sqSum a := by
  simp only [reInner_apply, sqSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem continuous_sqSum : Continuous (sqSum : (J → ℂ) → ℝ) := by
  unfold sqSum
  fun_prop

theorem hasFDerivAt_sqSum (z : J → ℂ) : HasFDerivAt sqSum ((2 : ℝ) • reInner z) z := by
  have h := HasFDerivAt.sum (u := Finset.univ) (A := fun p (x : J → ℂ) => ‖x p‖ ^ 2)
    fun p _ => (hasFDerivAt_apply p z).norm_sq
  rw [show (∑ p ∈ Finset.univ, fun x : J → ℂ => ‖x p‖ ^ 2) = sqSum from by
    funext x; simp [sqSum, Finset.sum_apply]] at h
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, reInner_apply, Complex.inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

def phi (z : J → ℂ) : ℝ := Real.log (sqSum z) * (1 / 2)

theorem hasFDerivAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) :
    HasFDerivAt phi ((sqSum z)⁻¹ • reInner z) z := by
  have h := ((hasFDerivAt_sqSum z).log hz).mul_const (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiffAt_phi {z : J → ℂ} (hz : sqSum z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n phi z := by
  have hs : ContDiff ℝ n (sqSum : (J → ℂ) → ℝ) :=
    ContDiff.sum fun p _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) p)
  exact (hs.contDiffAt.log hz).mul contDiffAt_const

theorem fderiv_fderiv_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (u : J → ℂ) :
    fderiv ℝ (fderiv ℝ phi) z u u =
      sqSum u / sqSum z - 2 * reInner z u ^ 2 / sqSum z ^ 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ phi) z :=
    ((contDiffAt_phi hz (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : fderiv ℝ (fderiv ℝ phi) z u u = fderiv ℝ (fun z' => fderiv ℝ phi z' u) z u := by
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  have hopen : IsOpen {z' : J → ℂ | sqSum z' ≠ 0} := isOpen_ne_fun continuous_sqSum continuous_const
  have heq : (fun z' => fderiv ℝ phi z' u) =ᶠ[𝓝 z]
      fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z' := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    rw [(hasFDerivAt_phi hz').fderiv]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      reInner_comm z' u]
    ring
  have hinv := (hasFDerivAt_inv hz).comp z (hasFDerivAt_sqSum z)
  have hG := (reInner u).hasFDerivAt.mul hinv
  rw [h1, heq.fderiv_eq]
  rw [show (fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z') =
    (⇑(reInner u) * ((fun x : ℝ => x⁻¹) ∘ sqSum)) from rfl, hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, reInner_self, reInner_comm u z]
  field_simp
  ring

theorem leviForm_phi {z : J → ℂ} (hz : sqSum z ≠ 0) (w : J → ℂ) :
    leviForm phi z w = (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) /
      (2 * sqSum z ^ 2) := by
  have hw : sqSum (Complex.I • w) = sqSum w := by
    simp [sqSum]
  unfold leviForm
  rw [fderiv_fderiv_phi hz, fderiv_fderiv_phi hz, hw]
  field_simp
  ring

def herm (a b : J → ℂ) : ℂ := ∑ p, conj (a p) * b p

theorem herm_self (a : J → ℂ) : herm a a = (sqSum a : ℂ) := by
  simp only [herm, sqSum, Complex.ofReal_sum, Complex.ofReal_pow]
  exact Finset.sum_congr rfl fun p _ => Complex.conj_mul' (a p)

theorem herm_swap (a b : J → ℂ) : herm b a = conj (herm a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

theorem reInner_sq_add (a b : J → ℂ) :
    ((reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2 : ℝ) : ℂ) = herm a b * herm b a := by
  have hre : (herm a b).re = reInner a b := by
    simp only [herm, Complex.re_sum, reInner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun p _ => by ring
  have him : (herm a b).im = -reInner a (Complex.I • b) := by
    simp only [herm, Complex.im_sum, reInner_apply, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.I_re, Complex.I_im,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [herm_swap a b, Complex.mul_conj, Complex.normSq_apply, hre, him]
  push_cast
  ring

theorem herm_smul_left (c : ℂ) (a b : J → ℂ) : herm (c • a) b = conj c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem herm_add_right (a b b' : J → ℂ) : herm a (b + b') = herm a b + herm a b' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_add_left (a a' b : J → ℂ) : herm (a + a') b = herm a b + herm a' b := by
  simp only [herm, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem herm_smul_right (c : ℂ) (a b : J → ℂ) : herm a (c • b) = c * herm a b := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem sqSum_ne_zero {a : J → ℂ} (ha : a ≠ 0) : sqSum a ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖a p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end LeviFSInvariant


open LeviFSInvariant in
theorem LeviFSInvariant.proof : LeviFSInvariant.Statement := by
  intro M _ a b c μ ha hc
  have hf : (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) = phi := by
    funext u
    simp only [phi, sqSum]
    ring
  have hca : c • a ≠ 0 := smul_ne_zero hc ha
  rw [hf, leviForm_phi (sqSum_ne_zero hca), leviForm_phi (sqSum_ne_zero ha)]
  have hS : sqSum (c • a) = ‖c‖ ^ 2 * sqSum a := by
    apply Complex.ofReal_injective
    rw [← herm_self, herm_smul_left, herm_smul_right, herm_self]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have key : ∀ a b : M → ℂ,
      ((sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2) : ℝ) : ℂ) =
        herm a a * herm b b - herm a b * herm b a := by
    intro a b
    rw [Complex.ofReal_sub, Complex.ofReal_mul, reInner_sq_add, herm_self, herm_self]
  have hN' : herm (c • a) (c • a) * herm (c • b + μ • a) (c • b + μ • a) -
      herm (c • a) (c • b + μ • a) * herm (c • b + μ • a) (c • a) =
      (((‖c‖ ^ 2) ^ 2 : ℝ) : ℂ) * (herm a a * herm b b - herm a b * herm b a) := by
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
    push_cast
    rw [← Complex.conj_mul']
    ring
  have hN : sqSum (c • a) * sqSum (c • b + μ • a) -
      (reInner (c • a) (c • b + μ • a) ^ 2 + reInner (c • a) (Complex.I • (c • b + μ • a)) ^ 2) =
      (‖c‖ ^ 2) ^ 2 * (sqSum a * sqSum b - (reInner a b ^ 2 + reInner a (Complex.I • b) ^ 2)) := by
    apply Complex.ofReal_injective
    rw [key, Complex.ofReal_mul, key, hN']
  rw [hN, hS]
  have hc2 : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

noncomputable section

namespace LeviHolPerturb

variable {J : Type} [Fintype J]

theorem hasDerivAt_of_contDiffAt_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    (hf : ContDiffAt ℝ 2 f 0) :
    (∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt f (deriv f t) t) ∧ HasDerivAt (deriv f) (deriv (deriv f) 0) 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually (by simp)] with t ht
    exact (ht.differentiableAt (by norm_num)).hasDerivAt
  · have h1 : ContDiffAt ℝ 1 (fun t => fderiv ℝ f t 1) 0 :=
      (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    exact (h1.differentiableAt one_ne_zero).hasDerivAt

theorem deriv_deriv_mul {f g : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) (hg : ContDiffAt ℝ 2 g 0) :
    deriv (deriv fun t => f t * g t) 0 =
      deriv (deriv f) 0 * g 0 + 2 * (deriv f 0 * deriv g 0) + f 0 * deriv (deriv g) 0 := by
  obtain ⟨hf1, hf2⟩ := hasDerivAt_of_contDiffAt_two hf
  obtain ⟨hg1, hg2⟩ := hasDerivAt_of_contDiffAt_two hg
  have hev : deriv (fun t => f t * g t) =ᶠ[𝓝 0] fun t => deriv f t * g t + f t * deriv g t := by
    filter_upwards [hf1, hg1] with t h1 h2
    exact (h1.mul h2).deriv
  rw [hev.deriv_eq]
  refine ((hf2.mul hg1.self_of_nhds).add (hf1.self_of_nhds.mul hg2)).deriv.trans ?_
  ring

theorem deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F} {z : J → ℂ}
    (hf : DifferentiableAt ℝ f z) (e : J → ℂ) :
    deriv (fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ f z e := by
  have hline : HasDerivAt (fun s : ℝ => z + s • e) e 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline hz0.symm).deriv

theorem deriv_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    deriv (deriv fun s : ℝ => f (z + s • e)) 0 = fderiv ℝ (fderiv ℝ f) z e e := by
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z + s • e) e s := fun s =>
    (((hasDerivAt_id s).smul_const e).const_add z).congr_deriv (one_smul ℝ e)
  have hz0 : z + (0 : ℝ) • e = z := by rw [zero_smul, add_zero]
  have hcont : Tendsto (fun s : ℝ => z + s • e) (𝓝 0) (𝓝 z) := by
    have h := (hline 0).continuousAt.tendsto
    rwa [hz0] at h
  have hfe : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have hev : deriv (fun s : ℝ => f (z + s • e)) =ᶠ[𝓝 0] fun s => fderiv ℝ f (z + s • e) e := by
    filter_upwards [hcont.eventually hfe] with s hs
    have h := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hH : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hA : HasFDerivAt (fun y => fderiv ℝ f y e) ((fderiv ℝ (fderiv ℝ f) z).flip e) z := by
    have h := hH.clm_apply (hasFDerivAt_const e z)
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ f (z + s • e) e) (fderiv ℝ (fderiv ℝ f) z e e) 0 :=
    hA.comp_hasDerivAt_of_eq (0 : ℝ) (hline 0) hz0.symm
  rw [hev.deriv_eq]
  exact hd.deriv

theorem contDiffAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : (J → ℂ) → F}
    {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z) (e : J → ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => f (z + s • e)) 0 := by
  have hl : ContDiffAt ℝ 2 (fun s : ℝ => z + s • e) 0 :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
  exact ContDiffAt.comp (g := f) (0 : ℝ) (by simpa using hf) hl

theorem sndDeriv_I_I {φ : (J → ℂ) → ℂ} {z : J → ℂ} (hφ : AnalyticAt ℂ φ z) (a : J → ℂ) :
    fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a) = - fderiv ℝ (fderiv ℝ φ) z a a := by
  have hR : AnalyticAt ℝ φ z := hφ.restrictScalars
  have hT : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) z) z :=
    (((hR.contDiffAt (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hlin : ∀ a b : J → ℂ, fderiv ℝ (fderiv ℝ φ) z a (Complex.I • b) =
      Complex.I • fderiv ℝ (fderiv ℝ φ) z a b := by
    intro a b
    have h1 := hT.clm_apply (hasFDerivAt_const (Complex.I • b) z)
    have h2 := (hT.clm_apply (hasFDerivAt_const b z)).const_smul Complex.I
    have hev : (fun y => fderiv ℝ φ y (Complex.I • b)) =ᶠ[𝓝 z]
        (fun y => Complex.I • fderiv ℝ φ y b) := by
      filter_upwards [hφ.eventually_analyticAt] with y hy
      rw [hy.differentiableAt.fderiv_restrictScalars ℝ]
      simp
    have h3 := (h1.congr_of_eventuallyEq hev.symm).unique h2
    have := congrArg (fun L => L a) h3
    simpa using this
  have hsymm : IsSymmSndFDerivAt ℝ φ z := (hR.contDiffAt (n := ω)).isSymmSndFDerivAt le_top
  calc fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) (Complex.I • a)
      = Complex.I • fderiv ℝ (fderiv ℝ φ) z (Complex.I • a) a := hlin _ _
    _ = Complex.I • fderiv ℝ (fderiv ℝ φ) z a (Complex.I • a) := by rw [hsymm]
    _ = Complex.I • Complex.I • fderiv ℝ (fderiv ℝ φ) z a a := by rw [hlin]
    _ = - fderiv ℝ (fderiv ℝ φ) z a a := by rw [smul_smul, Complex.I_mul_I]; simp

theorem line_key {X : ℝ → ℝ} {A Φ : ℝ → ℂ} (hX : ContDiffAt ℝ 2 X 0) (hA : ContDiffAt ℝ 2 A 0)
    (hΦ : ContDiffAt ℝ 2 Φ 0) (h0 : Φ 0 = 0) (h1 : deriv Φ 0 = 0) :
    deriv (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 = 0 ∧
      deriv (deriv fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) 0 =
        2 * X 0 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
  have hg : (fun t => X t * (‖A t + Φ t‖ ^ 2 - ‖A t‖ ^ 2)) =
      fun t => X t * (2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) := by
    funext t
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  rw [hg]
  obtain ⟨hX1, hX2⟩ := hasDerivAt_of_contDiffAt_two hX
  obtain ⟨hA1, hA2⟩ := hasDerivAt_of_contDiffAt_two hA
  obtain ⟨hΦ1, hΦ2⟩ := hasDerivAt_of_contDiffAt_two hΦ
  have hN2 : ContDiffAt ℝ 2 (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 :=
    (contDiffAt_const.mul (hA.inner ℝ hΦ)).add (hΦ.inner ℝ hΦ)
  have hN0 : (2 * inner ℝ (A 0) (Φ 0) + inner ℝ (Φ 0) (Φ 0) : ℝ) = 0 := by simp [h0]
  have hNd : HasDerivAt (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 0 := by
    have h := ((hA1.self_of_nhds.inner ℝ hΦ1.self_of_nhds).const_mul 2).add
      (hΦ1.self_of_nhds.inner ℝ hΦ1.self_of_nhds)
    exact h.congr_deriv (by simp [h0, h1])
  have hev : deriv (fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) =ᶠ[𝓝 0]
      fun t => 2 * (inner ℝ (A t) (deriv Φ t) + inner ℝ (deriv A t) (Φ t)) +
        (inner ℝ (Φ t) (deriv Φ t) + inner ℝ (deriv Φ t) (Φ t)) := by
    filter_upwards [hA1, hΦ1] with t ha hp
    exact (((ha.inner ℝ hp).const_mul 2).add (hp.inner ℝ hp)).deriv
  have hNdd : deriv (deriv fun t => 2 * inner ℝ (A t) (Φ t) + inner ℝ (Φ t) (Φ t)) 0 =
      2 * inner ℝ (A 0) (deriv (deriv Φ) 0) := by
    rw [hev.deriv_eq]
    have h := ((((hA1.self_of_nhds.inner ℝ hΦ2).add (hA2.inner ℝ hΦ1.self_of_nhds)).const_mul 2).add
      ((hΦ1.self_of_nhds.inner ℝ hΦ2).add (hΦ2.inner ℝ hΦ1.self_of_nhds)))
    refine h.deriv.trans ?_
    simp [h0, h1]
  have key := deriv_deriv_mul hX hN2
  beta_reduce at key
  refine ⟨?_, ?_⟩
  · refine (hX1.self_of_nhds.mul hNd).deriv.trans ?_
    simp [h0]
  · rw [key, hNdd, hN0, hNd.deriv]
    ring

theorem along {ξ : (J → ℂ) → ℝ} {a φ : (J → ℂ) → ℂ} {z : J → ℂ} (hξ : ContDiffAt ℝ 2 ξ z)
    (ha : AnalyticAt ℂ a z) (hφ : AnalyticAt ℂ φ z) (hφ0 : φ z = 0)
    (hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z) (v : J → ℂ)
    (hv : fderiv ℂ φ z v = 0) :
    fderiv ℝ (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v = 0 ∧
      fderiv ℝ (fderiv ℝ fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z v v =
        2 * ξ z * inner ℝ (a z) (fderiv ℝ (fderiv ℝ φ) z v v) := by
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hz0 : z + (0 : ℝ) • v = z := by rw [zero_smul, add_zero]
  have h0 : (fun t : ℝ => φ (z + t • v)) 0 = 0 := by simp [hφ0]
  have h1 : deriv (fun t : ℝ => φ (z + t • v)) 0 = 0 := by
    rw [deriv_line (hφR.differentiableAt (by norm_num)) v,
      hφ.differentiableAt.fderiv_restrictScalars ℝ]
    simpa using hv
  obtain ⟨k1, k2⟩ := line_key (X := fun t => ξ (z + t • v)) (A := fun t => a (z + t • v))
    (Φ := fun t => φ (z + t • v)) (contDiffAt_line hξ v) (contDiffAt_line haR v)
    (contDiffAt_line hφR v) h0 h1
  refine ⟨?_, ?_⟩
  · rw [← deriv_line (hu.differentiableAt (by norm_num)) v]
    exact k1
  · rw [← deriv_deriv_line hu v, ← deriv_deriv_line hφR v]
    rw [show ξ z = ξ (z + (0 : ℝ) • v) by rw [hz0], show a z = a (z + (0 : ℝ) • v) by rw [hz0]]
    exact k2

theorem proof : LeviHolPerturb.Statement := by
  intro J _ ξ a φ z w hξ ha hφ hφ0 hdφ
  have haR : ContDiffAt ℝ 2 a z := ha.restrictScalars.contDiffAt
  have hφR : ContDiffAt ℝ 2 φ z := hφ.restrictScalars.contDiffAt
  have hu : ContDiffAt ℝ 2 (fun x => ξ x * (‖a x + φ x‖ ^ 2 - ‖a x‖ ^ 2)) z :=
    hξ.mul (((haR.add hφR).norm_sq ℝ).sub (haR.norm_sq ℝ))
  have hw := along hξ ha hφ hφ0 hu w hdφ
  have hIw := along hξ ha hφ hφ0 hu (Complex.I • w) (by rw [map_smul, hdφ, smul_zero])
  refine ⟨hu, by simp [hφ0], hw.1, hIw.1, ?_⟩
  unfold leviForm
  rw [hw.2, hIw.2, sndDeriv_I_I hφ w, inner_neg_right]
  ring

end LeviHolPerturb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

variable {J : Type} [Fintype J]

theorem fderiv_fderiv_add_apply {f g : (J → ℂ) → ℝ} {z : J → ℂ} (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) z v v =
      fderiv ℝ (fderiv ℝ f) z v v + fderiv ℝ (fderiv ℝ g) z v v := by
  have hf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hev : fderiv ℝ (fun y => f y + g y) =ᶠ[𝓝 z] fun y => fderiv ℝ f y + fderiv ℝ g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy1 hy2
    exact ((hy1.differentiableAt (by norm_num)).hasFDerivAt.add
      (hy2.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y + fderiv ℝ g y)
      (fderiv ℝ (fderiv ℝ f) z + fderiv ℝ (fderiv ℝ g) z) z := hf'.add hg'
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem fderiv_fderiv_log_apply {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z)
    (v : J → ℂ) :
    fderiv ℝ (fderiv ℝ (fun x => Real.log (F x))) z v v =
      fderiv ℝ (fderiv ℝ F) z v v / F z - (fderiv ℝ F z v) ^ 2 / F z ^ 2 := by
  have hpos' : ∀ᶠ y in 𝓝 z, 0 < F y := continuousAt_const.eventually_lt hF.continuousAt hpos
  have hev : fderiv ℝ (fun x => Real.log (F x)) =ᶠ[𝓝 z] fun y => (F y)⁻¹ • fderiv ℝ F y := by
    filter_upwards [hF.eventually (by simp), hpos'] with y hy hy'
    exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.log hy'.ne').fderiv
  have hH : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun y => (F y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(F z ^ 2)⁻¹)).comp (fderiv ℝ F z)) z :=
    (hasFDerivAt_inv hpos.ne').comp z (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hP := hinv.fun_smul hH
  rw [hev.fderiv_eq, hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply]
  field_simp
  ring

theorem leviForm_log {F : (J → ℂ) → ℝ} {z : J → ℂ} (hF : ContDiffAt ℝ 2 F z) (hpos : 0 < F z) (w : J → ℂ) :
    leviForm (fun x => Real.log (F x)) z w =
      leviForm F z w / F z - ((fderiv ℝ F z w) ^ 2 + (fderiv ℝ F z (Complex.I • w)) ^ 2) / (4 * F z ^ 2) := by
  unfold leviForm
  rw [fderiv_fderiv_log_apply hF hpos, fderiv_fderiv_log_apply hF hpos]
  have : F z ≠ 0 := hpos.ne'
  field_simp
  ring

theorem LeviLogFlat.proof : LeviLogFlat.Statement := by
  intro J _ P u z w hP hu hpos hu0 hdw hdiw hlevi
  have hF : ContDiffAt ℝ 2 (fun x => P x + u x) z := hP.add hu
  have hFpos : 0 < P z + u z := by rw [hu0, add_zero]; exact hpos
  have hd : ∀ v, fderiv ℝ (fun x => P x + u x) z v = fderiv ℝ P z v + fderiv ℝ u z v := by
    intro v
    have h2 : HasFDerivAt (fun x => P x + u x) (fderiv ℝ P z + fderiv ℝ u z) z :=
      (hP.differentiableAt (by norm_num)).hasFDerivAt.add (hu.differentiableAt (by norm_num)).hasFDerivAt
    rw [h2.fderiv]
    rfl
  have hL : leviForm (fun x => P x + u x) z w = leviForm P z w + leviForm u z w := by
    unfold leviForm
    rw [fderiv_fderiv_add_apply hP hu, fderiv_fderiv_add_apply hP hu]
    ring
  rw [leviForm_log hF hFpos, leviForm_log hP hpos, hL, hlevi, hd, hd, hdw, hdiw, hu0]
  simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ComplexFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    P.IsPrime → IsRelevant P →
    ∀ F : MvPolynomial (Σ k, ι k) ℂ, (∀ z ∈ mcPts P, eval z F = 0) →
      F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

