module

public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.CovDet
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

namespace SmoothCutoff

noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bump_of_le_half {s : ℝ} (h : s ≤ 1 / 2) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem bump_of_one_le {s : ℝ} (h : 1 ≤ s) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (x := 20 * (1 - s)) (by linarith), mul_zero]

theorem bump_of_mem {s : ℝ} (h1 : 11 / 20 ≤ s) (h2 : s ≤ 19 / 20) : bump s = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s

theorem prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t :=
  (bump_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim : deriv prim = bump := funext fun t => (prim_hasDerivAt t).deriv

theorem prim_contDiff : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩

theorem prim_monotone : Monotone prim :=
  monotone_of_deriv_nonneg (fun t => (prim_hasDerivAt t).differentiableAt)
    (fun t => by rw [deriv_prim]; exact bump_nonneg t)

theorem prim_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : prim t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  apply bump_of_le_half
  have := (Set.mem_uIcc.1 hs)
  rcases this with h | h <;> linarith [h.1, h.2]

theorem prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (bump_continuous.intervalIntegrable _ _) (bump_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := t) (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact bump_of_one_le hs.1

theorem prim_one_ge : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith

theorem prim_nonneg (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this

theorem prim_le (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this

noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1

theorem chi_hasDerivAt (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1

theorem isCutoff_chi : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]

end SmoothCutoff

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
section
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Filter Topology
open scoped ENNReal

def HoloClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F : ℕ → M → ℂ) (f : M → ℂ),
    SmoothR n X.z ps → (∀ k, Holo n X.z (F k)) → Measurable f →
    Tendsto (fun k => wint n X.z (fun x => F k x - f x) ps) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n X.z G ∧ f =ᵐ[vol n X.z] G

def EvalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (x0 : M), SmoothR n X.z ps →
    ∃ C : ℝ, ∀ F : M → ℂ, Holo n X.z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n X.z F ps

end ReciprocityTheory.L2DbarEstimates.I
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
section
open Complex ComplexConjugate Filter Topology Matrix

namespace ReciprocityTheory.L2DbarEstimates

noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x

def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)

variable {n : ℕ}

theorem contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : (fun y => Complex.normSq (g y)) = fun y => ‖g y‖ ^ 2 :=
    funext fun y => Complex.normSq_eq_norm_sq _
  rw [h2]
  exact h1.norm_sq ℝ

theorem wd_normSq_comp {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hgC : DifferentiableAt ℂ g x := hg.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := hgC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (g y)) x := Complex.conjCLE.differentiableAt.comp x hgR
  rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
    funext fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,
    wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]

theorem leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y →
      DifferentiableAt ℝ (fun z => conj (f z)) y :=
    fun h => Complex.conjCLE.differentiableAt.comp _ h
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y := hg.eventually (by simp)
  have hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    hev.mono fun y hy => hy.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := (hg.differentiableAt (by norm_num)).restrictScalars ℝ

  have hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k) :=
    fun k => hdC.mono fun y hy => wd_of_differentiableAt hy
  have hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0 :=
    fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))
  have hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x :=
    fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)
  have hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => g y * conj (wd n k g y) := by
    intro k
    filter_upwards [hev] with y hy
    have hyC : DifferentiableAt ℂ g y := hy.differentiableAt (by norm_num)
    have hyR : DifferentiableAt ℝ g y := hyC.restrictScalars ℝ
    rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
      funext fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,
      wdb_of_differentiableAt hyC, zero_mul, zero_add]
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    rw [wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero,
      mul_zero, add_zero]
  unfold leviV
  simp_rw [hterm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

theorem leviLogNormSq : LeviLogNormSqStatement := by
  intro n p g x ξ hg hG
  set G : Fin p → ℂ := fun i => g i x with hGdef
  have hpos : 0 < sqNorm G := sqNorm_pos hG
  have hne : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)
  have hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) := Real.contDiffAt_log.mpr hpos.ne'
  have hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm G) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) := by
    have h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
        ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ :=
      leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => contDiffAt_normSq_comp (hg i)) ξ
    rw [h1, sqNorm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    have h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
        ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x :=
      wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j =
      star G ⬝ᵥ (wJac n p g x *ᵥ ξ) := by
    simp only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGdef, Complex.star_def]
    ring
  rw [hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]
  push_cast
  field_simp
  ring

end ReciprocityTheory.L2DbarEstimates
end

-- bundled from ReciprocityTheory.L2DbarEstimates.LeviForms.PolarBallReal
section
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff

theorem polar_finrank (n : ℕ) : finrank ℝ (V n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace_fin]

private theorem nontrivial_V_of_one_le (n : ℕ) (hn : 1 ≤ n) : Nontrivial (ReciprocityTheory.L2DbarEstimates.V n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)

theorem polar_ballReal (n : ℕ) (hn : 1 ≤ n) :
    (volume : Measure (V n)).real (ball 0 1) = Real.pi ^ n / (Nat.factorial n : ℝ) := by
  have hG : Real.Gamma (((2 * n : ℕ) : ℝ) / 2 + 1) = (n.factorial : ℝ) := by
    rw [show ((2 * n : ℕ) : ℝ) / 2 + 1 = (n : ℝ) + 1 by push_cast; ring]
    exact Real.Gamma_nat_eq_factorial n
  have hs : Real.sqrt Real.pi ^ (2 * n) = Real.pi ^ n := by
    rw [pow_mul, Real.sq_sqrt Real.pi_pos.le]
  have hpos : (0 : ℝ) ≤ Real.pi ^ n / (n.factorial : ℝ) := by positivity
  have := nontrivial_V_of_one_le n hn
  rw [measureReal_def, InnerProductSpace.volume_ball, polar_finrank, hG, hs,
    ENNReal.ofReal_one, one_pow, one_mul, ENNReal.toReal_ofReal hpos]

theorem polar_radial (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
      Real.log (b / a) / 2 := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hb : 0 < b := ha.trans_le hab
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsab : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hpt : ∀ y : ℝ, y ^ (2 * n - 1) •
      (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ Icc (Real.sqrt a) (Real.sqrt b)
    · rw [if_pos hy, if_pos hy]
      have hy0 : 0 < y := hsa.trans_le hy.1
      rw [smul_eq_mul, Real.rpow_neg (by positivity), Real.rpow_natCast]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      have hsplit : (y ^ 2) ^ (k + 1) = y ^ (2 * k + 1) * y := by ring
      rw [hsplit, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy0.ne'), one_mul]
    · rw [if_neg hy, if_neg hy, smul_zero]
  calc ∫ y in Ioi (0:ℝ), y ^ (2 * n - 1) •
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y
      = ∫ y in Ioi (0:ℝ), (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => t⁻¹) y := by
        exact congrArg _ (funext hpt)
    _ = ∫ y in Icc (Real.sqrt a) (Real.sqrt b), y⁻¹ := by
        rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          Set.inter_eq_left.mpr (show Icc (Real.sqrt a) (Real.sqrt b) ⊆ Ioi 0 from
            fun y hy => hsa.trans_le hy.1)]
    _ = Real.log (Real.sqrt b / Real.sqrt a) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hsab,
          integral_inv_of_pos hsa hsb]
    _ = Real.log (b / a) / 2 := by
        rw [Real.log_div hsb.ne' hsa.ne', Real.log_sqrt hb.le, Real.log_sqrt ha.le,
          Real.log_div hb.ne' ha.ne']
        ring

theorem polar (n : ℕ) : PolarStatement n := by
  intro hn a b ha hab
  have := nontrivial_V_of_one_le n hn
  have hb : 0 < b := ha.trans_le hab
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔
      (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b) := by
    intro y
    have h0 := norm_nonneg y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc Real.sqrt a ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = ‖y‖ := Real.sqrt_sq h0
      · calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h2
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} := by
    have h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2} :=
      isClosed_le continuous_const (continuous_norm.pow 2)
    have h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b} :=
      isClosed_le (continuous_norm.pow 2) continuous_const
    exact h1.inter h2
  have hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h0 := norm_nonneg y
    have h2 : ‖y‖ ^ 2 ≤ b := hy.2
    nlinarith [mul_self_nonneg (‖y‖ - 1)]
  have hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub
  have hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')
  have hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume :=
    hcont.integrableOn_compact hK
  have hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}]
      (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) :=
    ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_r hnn]
  congr 1
  have hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n,
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator
          (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}
    · rw [if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]
    · rw [if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from
        fun h => hy ((hmem y).2 h))]
  have hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) =
      ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    rw [← integral_indicator hSc.measurableSet]
    exact congrArg _ (funext hpt)
  have hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ =
      (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ),
        y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y := by
    rw [integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]
  rw [hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab,
    nsmul_eq_mul, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

end ReciprocityTheory.L2DbarEstimates.I
end

