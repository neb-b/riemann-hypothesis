module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImageSqIoi
section
namespace GlobalTheory.SquareImageInterval

open MeasureTheory

theorem image_sq_Ioi : (fun r : ℝ => r ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact pow_pos (Set.mem_Ioi.1 hr) 2
  · intro hy
    exact ⟨√y, Real.sqrt_pos.2 hy, Real.sq_sqrt (le_of_lt hy)⟩

theorem main : ∀ (G : ℝ → ENNReal), ∫⁻ (r : ℝ) in Set.Ioi (0 : ℝ), ENNReal.ofReal r * G r
    = ∫⁻ (u : ℝ) in Set.Ioi (0 : ℝ), (2 : ENNReal)⁻¹ * G √u := by
  intro G
  have hinj : Set.InjOn (fun r : ℝ => r ^ 2) (Set.Ioi 0) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    have h2 : a ^ 2 = b ^ 2 := hab
    nlinarith [h2]
  have hder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (fun u => (2 : ENNReal)⁻¹ * G √u)
  rw [image_sq_Ioi] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * x), Real.sqrt_sq (le_of_lt hx'),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal x * G x = (2 * 2⁻¹) * (ENNReal.ofReal x * G x) := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ = 2 * ENNReal.ofReal x * (2⁻¹ * G x) := by ring

end GlobalTheory.SquareImageInterval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsExtra
section
namespace GlobalTheory.PrimeOrderModule

theorem exists_character (S M : Type) [CommRing S] [AddCommGroup M] [Module S M] (T : ℕ)
    (hT : T.Prime) (hM : Nat.card M = T) :
    ∃ χ : S →+* ZMod T, ∀ (a : S) (m : M), χ a = 0 → a • m = 0 := by
  haveI : Fact T.Prime := ⟨hT⟩
  have hZ : Nat.card (ZMod T) = T := Nat.card_zmod T
  let e : M ≃+ ZMod T := addEquivOfPrimeCardEq hM hZ
  have key : ∀ (a : S) (m : M), e (a • m) = e (a • e.symm 1) * e m := by
    intro a m
    have hm : m = (e m).val • e.symm 1 := by
      apply e.injective
      rw [map_nsmul, e.apply_symm_apply, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    calc e (a • m) = e (a • ((e m).val • e.symm 1)) := by rw [← hm]
      _ = (e m).val • e (a • e.symm 1) := by rw [smul_comm, map_nsmul]
      _ = e (a • e.symm 1) * e m := by
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  let χ : S →+* ZMod T :=
    { toFun := fun a => e (a • e.symm 1)
      map_one' := by simp
      map_mul' := fun a b => by rw [mul_smul, key]
      map_zero' := by simp
      map_add' := fun a b => by rw [add_smul, map_add (f := _)] }
  refine ⟨χ, fun a m h => ?_⟩
  apply e.injective
  have h' : e (a • e.symm 1) = 0 := h
  rw [key, h', zero_mul, map_zero]

end GlobalTheory.PrimeOrderModule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsTer
section
namespace GlobalTheory.IterationConvergence

theorem step (w : ℂ) (h : ‖w - 1‖ < 1 / 2) : (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have e2 : w + 1 = 2 - (1 - w) := by ring
  have h2 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by
    have := norm_sub_norm_le (2 : ℂ) (1 - w)
    rw [← e2] at this
    have h1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := norm_sub_rev _ _
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  rw [e, norm_mul]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

theorem iter {z : ℂ} (hz : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) (k : ℕ) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := step (z ^ (2 ^ k)) (hz _)
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [e, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := by gcongr
      _ ≤ _ := hs

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := iter hz k
  have h2 := hz (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

end GlobalTheory.IterationConvergence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace GlobalTheory.GallagherLemma

theorem continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem fourier_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine ae_eq_of_integral_contDiff_smul_eq (continuous_fourier hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
  intro g hg hc
  have hc' : HasCompactSupport (fun x => (g x : ℂ)) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg' with hφ
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun D => D φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h3 : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
  have h4 : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h4, h3] at h1
  simpa [hφx] using h1

theorem integral_norm_sq_Lp (F : Lp ℂ 2 (volume : Measure ℝ)) : ∫ x, ‖F x‖ ^ 2 = ‖F‖ ^ 2 := by
  have := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [inner_self_eq_norm_sq_to_K] at this
  have h : ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact this.symm
  exact_mod_cast h

theorem plancherel {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_ae_eq hf h2
  constructor
  · have h3 : MemLp (𝓕 f) 2 volume :=
      (memLp_congr_ae h).2 (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm h3.aestronglyMeasurable).1 h3
  · calc ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h] with x hx
          rw [hx]
      _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := by
          rw [integral_norm_sq_Lp, integral_norm_sq_Lp, Lp.norm_fourier_eq]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

theorem fourier_indicator (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Set.Ico (l - δ) l).indicator (fun _ => c) v =
      (Set.Ico (l - δ) l).indicator (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) v := by
    intro v
    by_cases hv : v ∈ Set.Ico (l - δ) l <;> simp [hv]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := δ)
    (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) l
  rw [sub_zero] at h2
  rw [← h2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm _ c, mul_assoc c, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_lower (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hc : Continuous fun u : ℝ => cexp ((s * u : ℝ) * I) := by fun_prop
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable (μ := volume) 0 δ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  calc δ / 2 = ∫ u in (0 : ℝ)..δ, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hδ (by simp)
        ((Complex.continuous_re.comp hc).intervalIntegrable _ _) fun u hu => ?_
      rw [exp_ofReal_mul_I_re]
      have h1 : |s * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hu.1]
        exact le_trans (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)) hs
      have h2 := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have h3 : (s * u) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (s * u)]
      linarith

theorem exp_sum (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by
  set f : ℝ → ℂ := fun v => ∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v
    with hf
  have hmem : ∀ (p : ENNReal) (n : ℕ),
      MemLp ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) p volume := fun p n =>
    memLp_indicator_const p measurableSet_Ico.nullMeasurableSet _ (Or.inr (by simp))
  have hint : ∀ n, Integrable ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) volume :=
    fun n => memLp_one_iff_integrable.1 (hmem 1 n)
  have hf1 : Integrable f := integrable_finsetSum _ fun n _ => hint n
  have hf2 : MemLp f 2 := memLp_finsetSum _ fun n _ => hmem 2 n
  obtain ⟨hI, hP⟩ := plancherel hf1 hf2
  have hδ : 0 ≤ 1 / T := by positivity
  have hF : ∀ w : ℝ, 𝓕 f w = (∑ n ∈ S, a n * cexp (-(2 * π * w * l n : ℝ) * I)) *
      ∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I) := by
    intro w
    rw [Finset.sum_mul]
    simp_rw [← fourier_indicator _ _ hδ]
    simp_rw [Real.fourier_real_eq, hf, Finset.smul_sum]
    refine integral_finsetSum _ fun n _ => ?_
    simpa [mul_comm] using (Real.fourierIntegral_convergent_iff w).2 (hint n)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set D : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2 with hD
  have hDc : Continuous D := by fun_prop
  have h1 : ∫ t in (-T)..T, D t = (2 * π) * ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) := by
    have := intervalIntegral.mul_integral_comp_mul_left (f := D) (a := -T / (2 * π))
      (b := T / (2 * π)) (2 * π)
    rw [this, mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  have hle : -T / (2 * π) ≤ T / (2 * π) := by gcongr; linarith
  have h2 : ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) ≤
      ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      ((hDc.comp (by fun_prop : Continuous fun w : ℝ => 2 * π * w)).intervalIntegrable _ _)
      ((hI.const_mul _).intervalIntegrable) fun w hw => ?_
    have hw' : |2 * π * w| ≤ T := by
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hpi).1 hw.1
        linarith
      · have := (le_div_iff₀ hpi).1 hw.2
        linarith
    have hk := kernel_lower (1 / T) (2 * π * w) hδ (by rw [mul_one_div, div_le_one hT]; exact hw')
    rw [hF, norm_mul, mul_pow]
    set k := ‖∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I)‖
    have hk1 : 1 ≤ 2 * T * k := by
      have : 2 * T * (1 / T / 2) = 1 := by field_simp
      rw [← this]; gcongr
    have hk2 : 1 ≤ 4 * T ^ 2 * k ^ 2 := by nlinarith
    have hD0 : 0 ≤ D (2 * π * w) := by positivity
    change D (2 * π * w) ≤ 4 * T ^ 2 * (D (2 * π * w) * k ^ 2)
    nlinarith
  have h3 : ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 ≤
      4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, ← hP, intervalIntegral.integral_of_le hle]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => by positivity))
      (by positivity)
  rw [h1]
  calc _ ≤ (2 * π) * (4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring

theorem gallagher : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by
  refine ⟨8 * π, by positivity, fun N a T hT => ?_⟩
  have h := exp_sum (Finset.Icc 1 N) a (fun n => Real.log n) T (by linarith)
  convert h using 2
  · funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 2
    push_cast
    ring
  · rw [← Real.range_exp, ← Set.image_univ,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [abs_of_pos (Real.exp_pos v), mul_div_cancel₀ _ (Real.exp_pos v).ne', Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Set.indicator_apply, ← Real.exp_add]
    refine if_congr ?_ rfl rfl
    rw [Set.mem_Ico, ← Real.lt_log_iff_exp_lt hn0, ← Real.log_le_iff_le_exp hn0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end GlobalTheory.GallagherLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingLoc
section
namespace GlobalTheory.CoprimeBasisExistence

open NumberField nonZeroDivisors

def coprimeSet (A : Type*) [CommRing A] (m : ℕ) : Submonoid A where
  carrier := {x | ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ (k : A) = x}
  one_mem' := ⟨1, one_pos, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
    exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', by simp⟩

theorem coprimeSet_le (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (m : ℕ) :
    coprimeSet A m ≤ A⁰ := by
  rintro _ ⟨k, hk, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')

theorem mem_of_natCast_mem {R : Type*} [CommRing R] (m : ℕ)
    (hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R)) (P : Ideal R) (hP : P.IsPrime) :
    ∀ n : ℕ, 0 < n → (n : R) ∈ P → (m : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases hc : n.Coprime m
    · exact absurd hnP (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu n hn hc)))
    · have hg0 : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
      have hg1 : 1 < Nat.gcd n m := by
        rw [Nat.Coprime] at hc
        omega
      have hn' : n = Nat.gcd n m * (n / Nat.gcd n m) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
      have hmul : ((Nat.gcd n m : R) * ((n / Nat.gcd n m : ℕ) : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hn']
        exact hnP
      rcases hP.mem_or_mem hmul with h1 | h1
      · obtain ⟨c, hc'⟩ := Nat.gcd_dvd_right n m
        have e : (m : R) = (Nat.gcd n m : R) * (c : R) := by
          rw [← Nat.cast_mul, ← hc']
        rw [e]
        exact P.mul_mem_right _ h1
      · have hlt : n / Nat.gcd n m < n := Nat.div_lt_self hn hg1
        have hpos : 0 < n / Nat.gcd n m := Nat.div_pos (Nat.gcd_le_left m hn) hg0
        exact ih (n / Nat.gcd n m) hlt hpos h1

theorem isPrincipalIdealRing_loc {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 K) R]
    [IsLocalization (coprimeSet (𝓞 K) m) R] : IsPrincipalIdealRing R := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hS R
  have hinj := IsLocalization.injective R hS
  have hm0 : (m : R) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 K) R), map_ne_zero_iff _ hinj]
    exact Nat.cast_ne_zero.mpr hm.ne'
  have hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R) := by
    intro k hk hc
    have := IsLocalization.map_units R (⟨(k : 𝓞 K), k, hk, hc, rfl⟩ : coprimeSet (𝓞 K) m)
    simpa using this
  refine IsPrincipalIdealRing.of_finite_primes ?_
  have hI : Ideal.span {(m : R)} ≠ 0 := by simpa using hm0
  refine (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset ?_
  intro P hP
  have hP : P.IsPrime := hP
  by_cases h0 : P = ⊥
  · exact Or.inl h0
  · refine Or.inr ⟨⟨P, hP, h0⟩, ?_, rfl⟩
    have h1 : P.under (𝓞 K) ≠ ⊥ := (IsLocalization.bot_lt_under_prime _ R hS P h0).ne'
    have h2 := Ideal.absNorm_mem (P.under (𝓞 K))
    have h3 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h4 : ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : R) ∈ P := by
      rw [← map_natCast (algebraMap (𝓞 K) R)]
      exact h2
    have := mem_of_natCast_mem m hu P hP _ (Nat.pos_of_ne_zero h3) h4
    simpa [Ideal.dvd_iff_le] using this

theorem exists_basis_coprime {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_loc (K := K) m hm R
  have hst : IsScalarTower (𝓞 K) R V := ⟨fun a r v => by
    change ((a • (r : K)) • v) = a • ((r : K) • v)
    rw [smul_assoc]⟩

  have key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) →
      ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M := by
    intro M v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact M.nsmul_mem hx b
      · rw [mul_smul]; exact M.nsmul_mem hy a
    | smul r x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩ := IsLocalization.surj (coprimeSet (𝓞 K) m) r
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      have h1 : (a * b) • r • x = c • (a • x) := by
        simp only [map_natCast] at hc
        rw [← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul,
          Nat.cast_smul_eq_nsmul, smul_comm b r]
      rw [h1]
      exact M.smul_mem c hx
  let N : Submodule R V := Submodule.span R (L : Set V)
  have hN : N.FG := by
    obtain ⟨s, hs⟩ := hL
    refine ⟨s, ?_⟩
    simp only [N, ← hs]
    exact (Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Module.IsTorsionFree R V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
    change (r : K) • v = 0 at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  obtain ⟨r, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)
  choose k hk hk' hkL using fun i => key L (e i : V) (e i).2
  refine ⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩
  · have h1 : LinearIndependent R (fun i => (e i : V)) :=
      e.linearIndependent.map' N.subtype N.ker_subtype
    have h2 : LinearIndependent K (fun i => (e i : V)) :=
      (LinearIndependent.iff_fractionRing R K).mp h1
    have h3 := h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))
    convert h3 using 1
    funext i
    simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
  · intro w hw
    have hwN : w ∈ N := Submodule.subset_span hw
    have h1 : w ∈ Submodule.span R
        ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V) := by
      have h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V) := by
        have := congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have hu : IsUnit (k i : R) := by
        have := IsLocalization.map_units R
          (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)
        simpa using this
      obtain ⟨u, hu⟩ := hu
      have h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V)) := by
        rw [← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨a, -, ha, h⟩ := key _ w h1
    exact ⟨a, ha, h⟩

end GlobalTheory.CoprimeBasisExistence
end

