module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
section
open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzTranslate

private theorem fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (a : V) (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : V → F), ContDiff ℝ ∞ g →
      ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by
  induction n with
  | zero =>
    intro F _ _ g hg x m
    simp only [iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro F _ _ g hg x m
    have hg1 : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ n (fderiv ℝ g)) :=
      hg1.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    have hsym : (fun y => fderiv ℝ (fun z => fderiv ℝ g z a) y)
        = fun y => fderiv ℝ (fderiv ℝ g) y a := by
      funext y
      ext w
      rw [fderiv_clm_apply ((hg1.differentiable (by simp)) y) (differentiableAt_const _)]
      simp
      have h2le : minSmoothness ℝ 2 ≤ ∞ := by simp
      exact (ContDiffAt.isSymmSndFDerivAt (hg.contDiffAt (x := y)) h2le) w a
    simp_rw [iteratedFDeriv_succ_apply_right]
    rw [fderiv_clm_apply ((hdiff x).continuousMultilinear_apply_const _) (differentiableAt_const _)]
    simp
    rw [ih (fderiv ℝ g) hg1 x (Fin.init m), hsym]

theorem fderiv_iteratedFDeriv_apply_comm {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m :=
  fun g hg x m => fderiv_iteratedFDeriv_apply_eq_iteratedFDeriv_fderiv a n g hg x m

theorem hasDerivAt_iteratedFDeriv_line {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a s := by
    simpa using ((hasDerivAt_id s).smul_const a).const_add x
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n g) :=
    hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
  have key : fderiv ℝ (iteratedFDeriv ℝ n g) (x + s • a) a
      = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a) := by
    ext m
    rw [← fderiv_continuousMultilinear_apply_const_apply (hd _)]
    exact fderiv_iteratedFDeriv_apply_comm a n g hg _ m
  rw [← key]
  exact (hd _).hasFDerivAt.comp_hasDerivAt s hline

theorem taylor_two {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (φ φ' φ'' : ℝ → G)
    (h1 : ∀ s, HasDerivAt φ (φ' s) s) (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) (M : ℝ)
    (hM : ∀ s, |s| ≤ 1 → ‖φ'' s‖ ≤ M) (t : ℝ) (ht : |t| ≤ 1) :
    ‖φ t - φ 0 - t • φ' 0‖ ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hd1 : ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖φ' s - φ' 0‖ ≤ M * |s| := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ') (f' := φ'')
      (s := Set.Icc (-1) 1) (fun x _ => (h2 x).hasDerivWithinAt)
      (fun x hx => hM x (abs_le.mpr hx)) (convex_Icc _ _) h0 hs
    simpa [Real.norm_eq_abs] using this
  have hψ : ∀ s, HasDerivAt (fun s => φ s - s • φ' 0) (φ' s - φ' 0) s := by
    intro s
    convert (h1 s).sub ((hasDerivAt_id s).smul_const (φ' 0)) using 1 <;> first | rfl | simp
  have ht' : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  have h0' : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have hbound : ∀ x ∈ Set.Icc (-|t|) |t|, ‖φ' x - φ' 0‖ ≤ M * |t| := by
    intro x hx
    have hx1 : |x| ≤ |t| := abs_le.mpr hx
    exact (hd1 x (abs_le.mp (hx1.trans ht))).trans (mul_le_mul_of_nonneg_left hx1 hM0)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => φ s - s • φ' 0) (f' := fun s => φ' s - φ' 0)
    (fun x _ => (hψ x).hasDerivWithinAt) hbound (convex_Icc _ _) h0' ht'
  have e : φ t - φ 0 - t • φ' 0 = (φ t - t • φ' 0) - (φ 0 - (0 : ℝ) • φ' 0) := by
    rw [zero_smul, sub_zero, sub_right_comm]
  rw [e]
  calc _ ≤ M * |t| * ‖t - 0‖ := key
    _ = M * t ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

theorem seminorm_translate_sub_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (f : 𝓢(V, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f) ≤ C * t ^ 2 := by
  set f1 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1def
  set f2 := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2def
  have hf1 : (⇑f1 : V → ℂ) = fun y => fderiv ℝ f y a := rfl
  have hf2 : (⇑f2 : V → ℂ) = fun y => fderiv ℝ f1 y a := rfl
  have hsm : ∀ g : 𝓢(V, ℂ), ContDiff ℝ ∞ ⇑g := fun g => g.smooth ⊤
  have hsmn : ∀ g : 𝓢(V, ℂ), ContDiff ℝ n ⇑g := fun g => (g.smooth ⊤).of_le (mod_cast le_top)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (Finset.Iic (k, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f2 :=
    ⟨_, rfl⟩
  have hL : ∀ y, (1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ n f2 y‖ ≤ 2 ^ k * S := fun y => by
    rw [hS]; exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f2 y
  have hS0 : 0 ≤ 2 ^ k * S := le_trans (by positivity) (hL 0)
  refine ⟨(1 + ‖a‖) ^ k * (2 ^ k * S), fun t ht => ?_⟩
  have hC0 : 0 ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_nonneg (by positivity) hS0
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (mul_nonneg hC0 (sq_nonneg t)) fun x => ?_
  have hcoe : (⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) : V → ℂ)
      = (fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1 := by
    funext y; simp [sub_neg_eq_add]
  have hshift : ContDiff ℝ n (fun y => f (y + t • a)) :=
    (hsmn f).comp (contDiff_id.add contDiff_const)
  have hD : iteratedFDeriv ℝ n ((fun y => f (y + t • a)) - ⇑f - (t : ℂ) • ⇑f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - (t : ℂ) • iteratedFDeriv ℝ n f1 x := by
    rw [iteratedFDeriv_sub_apply, iteratedFDeriv_sub_apply, iteratedFDeriv_const_smul_apply,
      iteratedFDeriv_comp_add_right]
    all_goals first
      | exact hshift.contDiffAt
      | exact (hsmn f).contDiffAt
      | exact (hsmn f1).contDiffAt
      | exact (hshift.sub (hsmn f)).contDiffAt
      | exact ((hsmn f1).const_smul (t : ℂ)).contDiffAt
  have hre : (t : ℂ) • iteratedFDeriv ℝ n f1 x = t • iteratedFDeriv ℝ n f1 x := by
    ext m; simp [Complex.real_smul]
  rw [hcoe, hD, hre]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖x‖ ^ k := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hdf : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
      (c • iteratedFDeriv ℝ n f1 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f (hsm f) x s
    rw [← hf1] at this
    exact this.const_smul c
  have hdf1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
      (c • iteratedFDeriv ℝ n f2 (x + s • a)) s := by
    intro s
    have := hasDerivAt_iteratedFDeriv_line a n f1 (hsm f1) x s
    rw [← hf2] at this
    exact this.const_smul c
  have hbd : ∀ s : ℝ, |s| ≤ 1 →
      ‖c • iteratedFDeriv ℝ n f2 (x + s • a)‖ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := by
    intro s hs
    have h2 : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) hs
    have hxy : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x + s • a‖) := by
      have h3 : ‖x‖ ≤ ‖x + s • a‖ + ‖s • a‖ := by
        have := norm_sub_le (x + s • a) (s • a)
        rwa [add_sub_cancel_right] at this
      nlinarith [norm_nonneg (x + s • a), norm_nonneg a]
    have hpow : c ≤ (1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k := by
      rw [hc, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hxy k
    rw [norm_smul, Real.norm_of_nonneg hc0]
    calc c * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
        ≤ ((1 + ‖a‖) ^ k * (1 + ‖x + s • a‖) ^ k) * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (1 + ‖a‖) ^ k * ((1 + ‖x + s • a‖) ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
      _ ≤ (1 + ‖a‖) ^ k * (2 ^ k * S) := mul_le_mul_of_nonneg_left (hL _) (by positivity)
  have hT := taylor_two (fun s : ℝ => c • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => c • iteratedFDeriv ℝ n f2 (x + s • a)) hdf hdf1 _ hbd t ht
  simp only [zero_smul, add_zero] at hT
  have e : c • iteratedFDeriv ℝ n f (x + t • a) - c • iteratedFDeriv ℝ n f x
      - t • c • iteratedFDeriv ℝ n f1 x
      = c • (iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x) := by
    rw [smul_sub, smul_sub, smul_comm t c]
  rw [e, norm_smul, Real.norm_of_nonneg hc0] at hT
  exact hT

end GlobalTheory.SchwartzTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzVanishingDecomposition
section
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric

noncomputable section

namespace GlobalTheory.SchwartzDiv

section Param

variable {H : Type} [MeasurableSpace H] {ν : Measure H} {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X] {c : H → X} {S : Set X} {φ : H → ℂ}

theorem hasFDerivAt_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) (t₀ : P) :
    HasFDerivAt (fun t => ∫ y, φ y • Θ (t, c y) ∂ν) (∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t₀ ∂ν) t₀ := by
  have hΘs : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
    ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
      (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
  have hΘ' := hΘs.continuous
  have hK : IsCompact (closedBall t₀ 1 ×ˢ S) := (isCompact_closedBall t₀ 1).prod hS
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΘ'.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hΘ.continuous.continuousOn
  have hm : ∀ t, AEStronglyMeasurable (fun y => φ y • Θ (t, c y)) ν := fun t =>
    hφ.1.smul ((hΘ.continuous.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F' := fun t y => φ y • fderiv ℝ (fun s => Θ (s, c y)) t) (bound := fun y => ‖φ y‖ * C)
    (ball_mem_nhds t₀ one_pos) (.of_forall hm) ?_ ?_ ?_ (hφ.norm.mul_const C) ?_
  · refine Integrable.mono' (hφ.norm.mul_const C₀) (hm t₀) ?_
    filter_upwards [hcS] with y hy
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ _ ⟨mem_closedBall_self zero_le_one, hy⟩) (norm_nonneg _)
  · exact hφ.1.smul ((hΘ'.comp (continuous_const.prodMk continuous_id)).comp_aestronglyMeasurable hc)
  · filter_upwards [hcS] with y hy t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC (t, c y) ⟨ball_subset_closedBall ht, hy⟩) (norm_nonneg _)
  · refine .of_forall fun y t _ => ?_
    have hd : ContDiff ℝ ∞ fun s => Θ (s, c y) := hΘ.comp (contDiff_id.prodMk contDiff_const)
    exact ((hd.differentiable (by simp)) t).hasFDerivAt.const_smul (φ y)

theorem contDiff_integral_smul_param (hc : AEStronglyMeasurable c ν) (hS : IsCompact S)
    (hcS : ∀ᵐ y ∂ν, c y ∈ S) (hφ : Integrable φ ν) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W] [IsScalarTower ℝ ℂ W] [CompleteSpace W] {Θ : P × X → W}
    (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ fun t => ∫ y, φ y • Θ (t, c y) ∂ν := by
  rw [contDiff_infty]
  intro n
  induction n generalizing W with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t =>
      (hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t).continuousAt)
  | succ n ih =>
    have hΘ' : ContDiff ℝ ∞ fun p : P × X => fderiv ℝ (fun s => Θ (s, p.2)) p.1 :=
      ContDiff.fderiv (f := fun (p : P × X) (s : P) => Θ (s, p.2)) (g := Prod.fst)
        (hΘ.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst le_rfl
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨fun t => ∫ y, φ y • fderiv ℝ (fun s => Θ (s, c y)) t ∂ν,
      ih hΘ', fun t => hasFDerivAt_integral_smul_param hc hS hcS hφ hΘ t⟩

end Param

def invCut (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1) * t⁻¹

theorem invCut_of_one_le {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by
  rw [invCut, Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem invCut_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : invCut t = 0 := by
  rw [invCut, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem contDiff_invCut : ContDiff ℝ ∞ invCut := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge 0 t with h | h
  · exact ((Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)).contDiffAt).mul (contDiffAt_inv ℝ h.ne')
  · have : invCut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show t < 1 / 2 by linarith)] with s hs
      exact invCut_of_le_half hs.le
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem hasTemperateGrowth_invCut : invCut.HasTemperateGrowth := by
  refine ⟨contDiff_invCut, fun n => ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (contDiff_invCut.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).continuousOn
  refine ⟨0, max C (Nat.factorial n : ℝ), fun x => ?_⟩
  rw [pow_zero, mul_one]
  rcases lt_or_ge x (1 / 2) with h1 | h1
  · have : invCut =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact invCut_of_le_half hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact le_max_of_le_right (Nat.cast_nonneg _)
  rcases le_or_gt x 2 with h2 | h2
  · exact (hC x ⟨h1, h2⟩).trans (le_max_left _ _)
  · have : invCut =ᶠ[𝓝 x] Inv.inv := by
      filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with s hs
      exact invCut_of_one_le hs.le
    rw [(this.iteratedFDeriv ℝ n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_inv]
    refine le_trans ?_ (le_max_right _ _)
    have hx : ‖x ^ (-1 - n : ℤ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (zpow_pos (by linarith) _)]
      exact zpow_le_one_of_nonpos₀ (by linarith) (by omega)
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
    calc (Nat.factorial n : ℝ) * ‖x ^ (-1 - n : ℤ)‖ ≤ Nat.factorial n * 1 := by gcongr
      _ = Nat.factorial n := mul_one _

end GlobalTheory.SchwartzDiv

namespace GlobalTheory.SchwartzDiv

theorem hadamard (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : SchwartzMap V ℂ) (hf0 : f 0 = 0) :
    ∃ (n : ℕ) (L : Fin n → V →L[ℝ] ℝ) (h g : Fin n → SchwartzMap V ℂ),
      (∀ i x, g i x = (L i x : ℂ) * h i x) ∧ ∀ x, f x = ∑ i, g i x := by
  let b := Module.finBasis ℝ V
  let L : Fin (Module.finrank ℝ V) → V →L[ℝ] ℝ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hL : ∀ i x, L i x = b.repr x i := fun i x => by simp [L, Module.Basis.coord_apply]
  let q : V → ℝ := fun x => ∑ i, L i x ^ 2
  have hq : q.HasTemperateGrowth := by
    simp only [q]
    exact Function.HasTemperateGrowth.sum fun i _ => ((L i).hasTemperateGrowth).pow 2
  have hqs : ContDiff ℝ ∞ q := hq.1
  have hfs : ContDiff ℝ ∞ f := f.smooth ⊤
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hfs.fderiv_right (by simp)

  let k : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) (b i)
  have hk : ∀ i, ContDiff ℝ ∞ (k i) := by
    intro i
    have hΘ : ContDiff ℝ ∞ fun p : V × ℝ => fderiv ℝ f (p.2 • p.1) (b i) :=
      (hfd.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_const
    have key := contDiff_integral_smul_param (ν := volume.restrict (Ioc (0 : ℝ) 1)) (c := id)
      (S := Icc (0 : ℝ) 1) (φ := fun _ => (1 : ℂ)) aestronglyMeasurable_id isCompact_Icc
      ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => Ioc_subset_Icc_self ht)
      (integrableOn_const (by simp)) hΘ
    convert key using 2 with x
    simp [k, intervalIntegral.integral_of_le zero_le_one]
  have key : ∀ x, f x = ∑ i, (L i x : ℂ) * k i x := by
    intro x
    have hc : ∀ v : V, Continuous fun t : ℝ => fderiv ℝ f (t • x) v := fun v =>
      (hfd.continuous.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
    have h1 : ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x = f ((1 : ℝ) • x) - f ((0 : ℝ) • x) := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => f (t • x)) (fun t _ => ?_)
        ((hc x).intervalIntegrable _ _)
      have := (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
      simp only [one_smul] at this
      exact this
    rw [one_smul, zero_smul, hf0, sub_zero] at h1
    rw [← h1]
    have h2 : ∀ t : ℝ, fderiv ℝ f (t • x) x = ∑ i, (L i x : ℂ) * fderiv ℝ f (t • x) (b i) := by
      intro t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ i, b.repr x i • b i) by rw [b.sum_repr], map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Complex.real_smul, hL]
    simp_rw [h2]
    rw [intervalIntegral.integral_finsetSum (f := fun i t => (L i x : ℂ) * fderiv ℝ f (t • x) (b i))
      fun i _ => (continuous_const.mul (hc (b i))).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun i _ => intervalIntegral.integral_const_mul _ _

  let β : V → ℝ := fun x => 1 - q x * invCut (q x)
  have hβs : ContDiff ℝ ∞ β := contDiff_const.sub (hqs.mul (contDiff_invCut.comp hqs))
  have hβ0 : ∀ x, 1 ≤ q x → β x = 0 := by
    intro x hx
    simp only [β]
    rw [invCut_of_one_le hx, mul_inv_cancel₀ (by linarith), sub_self]
  have hnorm : ∀ x, q x < 1 → ‖x‖ ≤ ∑ i, ‖b i‖ := by
    intro x hx
    have hLi : ∀ i, |L i x| ≤ 1 := by
      intro i
      have : L i x ^ 2 ≤ q x :=
        Finset.single_le_sum (f := fun j => L j x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      exact (sq_le_one_iff_abs_le_one _).1 (by linarith)
    calc ‖x‖ = ‖∑ i, L i x • b i‖ := by simp only [hL, b.sum_repr]
      _ ≤ ∑ i, ‖L i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_left (norm_nonneg _) (hLi i)
  have hβc : HasCompactSupport (fun x => (β x : ℂ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : V) (∑ i, ‖b i‖)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have : 1 ≤ q x := by
      by_contra h
      exact absurd (hnorm x (not_le.1 h)) (not_le.2 hx)
    rw [hβ0 x this, Complex.ofReal_zero]
  have hnear : ∀ i, HasCompactSupport ((fun x => (β x : ℂ)) * k i) := fun i => hβc.mul_right
  have hnears : ∀ i, ContDiff ℝ ∞ ((fun x => (β x : ℂ)) * k i) := fun i =>
    (Complex.ofRealCLM.contDiff.comp hβs).mul (hk i)

  let a : Fin (Module.finrank ℝ V) → V → ℂ := fun i x => ((L i x * invCut (q x) : ℝ) : ℂ)
  have ha : ∀ i, (a i).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp ((L i).hasTemperateGrowth.mul (hasTemperateGrowth_invCut.comp hq))
  have hLc : ∀ i, (fun x => (L i x : ℂ)).HasTemperateGrowth := fun i =>
    Function.Complex.hasTemperateGrowth_ofReal.comp (L i).hasTemperateGrowth
  let h : Fin (Module.finrank ℝ V) → SchwartzMap V ℂ := fun i =>
    (hnear i).toSchwartzMap (hnears i) + SchwartzMap.smulLeftCLM ℂ (a i) f
  have hh : ∀ i x, h i x = (β x : ℂ) * k i x + a i x * f x := by
    intro i x
    have e : ((hnear i).toSchwartzMap (hnears i) : V → ℂ) x = (β x : ℂ) * k i x := rfl
    simp only [h, SchwartzMap.add_apply, e, SchwartzMap.smulLeftCLM_apply_apply (ha i), smul_eq_mul]
  refine ⟨Module.finrank ℝ V, L, h, fun i => SchwartzMap.smulLeftCLM ℂ (fun x => (L i x : ℂ)) (h i),
    fun i x => by rw [SchwartzMap.smulLeftCLM_apply_apply (hLc i), smul_eq_mul], fun x => ?_⟩
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hLc _), smul_eq_mul, hh]
  have e1 : ∀ i, (L i x : ℂ) * ((β x : ℂ) * k i x + a i x * f x) =
      (β x : ℂ) * ((L i x : ℂ) * k i x) + ((L i x ^ 2 * invCut (q x) : ℝ) : ℂ) * f x := by
    intro i; simp only [a]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, ← Finset.mul_sum, ← key x,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_mul]
  simp only [β, q]
  push_cast
  ring

end GlobalTheory.SchwartzDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsFiniteFlatRankOfFiniteFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem isPullback_fromSpec_app_preimage_of_affine {X T : Scheme.{0}} (p : X ⟶ T) {U : T.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (p.app U)) p hU.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec p hU hV]) (by simp)).flip

theorem sections_finite_flat_rank_of_finite_flat :
    ∀ (X T : Scheme.{0}) (p : X ⟶ T) [IsFinite p] [Flat p] (r : ℕ), (∀ t, p.finrank t = r) →
      ∀ (U : T.Opens), IsAffineOpen U →
        letI := (p.app U).hom.toAlgebra;
        Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧ Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) ∧
          ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(X, p ⁻¹ᵁ U) q = r := by
  intro X T p _ _ r hr U hU
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := hU.preimage p
  have hpb := isPullback_fromSpec_app_preimage_of_affine p hU hV
  have hfin : IsFinite (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb ‹_›
  have hflat : Flat (Spec.map (p.app U)) := MorphismProperty.of_isPullback hpb ‹_›
  have h1 : (p.app U).hom.Finite := (IsFinite.SpecMap_iff _).1 hfin
  have h2 : (p.app U).hom.Flat := Flat.SpecMap_iff.1 hflat
  letI := (p.app U).hom.toAlgebra
  haveI : Module.Finite Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h1
  haveI : Module.Flat Γ(T, U) Γ(X, p ⁻¹ᵁ U) := h2
  refine ⟨inferInstance, inferInstance, fun q ↦ ?_⟩
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb q
  rw [hr] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralLeOfExpanding
section
open MeasureTheory

namespace GlobalTheory

theorem volume_le_mul_volume_image_of_expanding (N : ℕ) (S : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (hK : 0 ≤ K)
    (hf : ∀ t ∈ S, ∀ t' ∈ S, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    volume S ≤ ENNReal.ofReal (K ^ N) * volume (f '' S) := by
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    have := hf a ha b hb
    rw [hab, sub_self, norm_zero, mul_zero] at this
    exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
  have hg : ∀ a ∈ S, Function.invFunOn f S (f a) = a := fun a ha => hinj.leftInvOn_invFunOn ha
  have hlip : LipschitzOnWith K.toNNReal (Function.invFunOn f S) (f '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hg a ha, hg b hb, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK]
    exact hf a ha b hb
  have himg : Function.invFunOn f S '' (f '' S) = S := hinj.invFunOn_image subset_rfl
  have h := hlip.hausdorffMeasure_image_le (d := (Fintype.card (Fin N) : ℝ)) (by positivity)
  rw [himg, hausdorffMeasure_pi_real, Fintype.card_fin, ENNReal.rpow_natCast] at h
  rw [ENNReal.ofReal_pow hK]
  exact h

theorem setIntegral_le_of_expanding (N : ℕ) (A Q : Set (Fin N → ℝ)) (K : ℝ)
    (f : (Fin N → ℝ) → (Fin N → ℝ)) (h₁ h₂ : (Fin N → ℝ) → ℝ)
    (hA : IsCompact A) (hQ : IsCompact Q) (hK : 0 ≤ K) (c₁ : Continuous h₁) (c₂ : Continuous h₂)
    (n₁ : ∀ t, 0 ≤ h₁ t) (n₂ : ∀ t, 0 ≤ h₂ t) (hm : ∀ t ∈ A, f t ∈ Q ∧ h₁ t ≤ h₂ (f t))
    (hf : ∀ t ∈ A, ∀ t' ∈ A, ‖t - t'‖ ≤ K * ‖f t - f t'‖) :
    ∫ t in A, h₁ t ≤ K ^ N * ∫ t in Q, h₂ t := by
  have i₁ : IntegrableOn h₁ A volume := c₁.continuousOn.integrableOn_compact hA
  have i₂ : IntegrableOn h₂ Q volume := c₂.continuousOn.integrableOn_compact hQ
  have hKN : 0 ≤ K ^ N := pow_nonneg hK N
  have hI₂ : 0 ≤ ∫ t in Q, h₂ t := integral_nonneg n₂
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKN hI₂), ENNReal.ofReal_mul hKN,
    ofReal_integral_eq_lintegral_ofReal i₁ (Filter.Eventually.of_forall n₁),
    ofReal_integral_eq_lintegral_ofReal i₂ (Filter.Eventually.of_forall n₂),
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₁) c₁.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (Filter.Eventually.of_forall n₂) c₂.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun r => ?_
  have m₁ : MeasurableSet {a | r < h₁ a} := measurableSet_lt measurable_const c₁.measurable
  have m₂ : MeasurableSet {a | r < h₂ a} := measurableSet_lt measurable_const c₂.measurable
  rw [Measure.restrict_apply m₁, Measure.restrict_apply m₂]
  refine (volume_le_mul_volume_image_of_expanding N ({a | r < h₁ a} ∩ A) K f hK
    (fun t ht t' ht' => hf t ht.2 t' ht'.2)).trans ?_
  gcongr
  rintro _ ⟨a, ⟨ha, haA⟩, rfl⟩
  exact ⟨lt_of_lt_of_le ha (hm a haA).2, (hm a haA).1⟩

end GlobalTheory
end

