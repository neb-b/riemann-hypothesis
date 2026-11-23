module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.Imports
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem dens (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCut : CutoffStatement n M) (hUR : UnweightRelStatement n M)
    (hUB : UnweightBackStatement n M) (hLoc : LocalizeStatement n M)
    (hCh : ChartFlatStatement n M) : DensStatement n M := by
  intro z hz e ph ψ he hph hψ hcut f w σ hf hw hσ hadj hone
  refine hCut z hz e ph ψ he hph hψ hcut ?_ f w σ hf hw hσ hadj hone
  intro f w σ hf hw hσ hadj hone hcf hcw hcσ
  obtain ⟨hG, hD, hS, hdiv, hdbar, hcG, hcD, hcS⟩ :=
    hUR z hz ph ψ f w σ hph hψ hf hw hσ hadj hone
  refine hUB z hz ph ψ f w σ hph hψ hf hw hσ hcf hcw hcσ ?_
  exact hLoc z hz (fun e' G D S he' => hCh z hz e' G D S he') _ _ _ hG hD hS hdiv hdbar
    (hcG hcf) (hcD hcw) (hcS hcf hcσ)

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.IntegrableFd
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

namespace FlatWeightedEstimates

lemma lint_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (f : α → E)
    (μ : Measure α) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero hf
  have e : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [e] at h
  simp only [ENNReal.rpow_natCast] at h
  simpa using h.symm

lemma tendsto_lint {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {l : Filter ι}
    {μ : Measure α} (F : ι → α → E) (h : Tendsto (fun i => eLpNorm (F i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x, ‖F i x‖ₑ ^ 2 ∂μ) l (𝓝 0) := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (F i) μ :=
    (h.eventually (Iio_mem_nhds ENNReal.zero_lt_top)).mono fun _ hi =>
      aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  have heq : (fun i => ∫⁻ x, ‖F i x‖ₑ ^ 2 ∂μ) =ᶠ[l]
      (fun i => eLpNorm (F i) 2 μ ^ 2) := hm.mono fun i hi => lint_sq (F i) μ hi
  exact (by simpa using ENNReal.Tendsto.pow (n := 2) h :
    Tendsto (fun i => eLpNorm (F i) 2 μ ^ 2) l (𝓝 0)).congr' heq.symm

lemma enorm_sq_V {n : ℕ} (x : V n) : ‖x‖ₑ ^ 2 = ∑ j, ‖x j‖ₑ ^ 2 := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_pow (norm_nonneg _) 2

lemma integrable_fd {n : ℕ} {f : V n → ℂ} (hf : LocallyIntegrable f volume) {φ : V n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (u : V n) :
    Integrable (fun y => f y * fderiv ℝ φ y u) volume := by
  have h1 : Continuous (fun y => fderiv ℝ φ y u) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  exact hf.integrable_smul_right_of_hasCompactSupport h1 (hc.fderiv_apply (𝕜 := ℝ) u)

lemma int_comb {n : ℕ} {f : V n → ℂ} (hf : LocallyIntegrable f volume) {φ : V n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (a b : ℂ) (u w : V n) :
    Integrable (fun y => f y * (a * fderiv ℝ φ y u + b * fderiv ℝ φ y w)) volume ∧
    ∫ y, f y * (a * fderiv ℝ φ y u + b * fderiv ℝ φ y w) =
      a * (∫ y, f y * fderiv ℝ φ y u) + b * ∫ y, f y * fderiv ℝ φ y w := by
  have h1 := (integrable_fd hf hφ hc u).const_mul a
  have h2 := (integrable_fd hf hφ hc w).const_mul b
  have e : (fun y => f y * (a * fderiv ℝ φ y u + b * fderiv ℝ φ y w)) =
      fun y => a * (f y * fderiv ℝ φ y u) + b * (f y * fderiv ℝ φ y w) := by
    funext y; ring
  rw [e]
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul]

lemma wd_eq (n : ℕ) (j : Fin n) (φ : V n → ℂ) (y : V n) :
    wd n j φ y = 1 / 2 * fderiv ℝ φ y (bas n j) + (-Complex.I / 2) *
      fderiv ℝ φ y (Complex.I • bas n j) := by
  unfold wd; ring

lemma wdb_eq (n : ℕ) (j : Fin n) (φ : V n → ℂ) (y : V n) :
    wdb n j φ y = 1 / 2 * fderiv ℝ φ y (bas n j) + (Complex.I / 2) *
      fderiv ℝ φ y (Complex.I • bas n j) := by
  unfold wdb; ring

def cD (n : ℕ) (p : Fin (n * 2)) : ℂ := ![1 / 2, -Complex.I / 2] (finProdFinEquiv.symm p).2

def vD (n : ℕ) (p : Fin (n * 2)) : V n :=
  ![bas n (finProdFinEquiv.symm p).1, Complex.I • bas n (finProdFinEquiv.symm p).1]
    (finProdFinEquiv.symm p).2

lemma reindex {n : ℕ} (H : Fin n × Fin 2 → ℂ) :
    ∑ p : Fin (n * 2), H (finProdFinEquiv.symm p) = ∑ j, (H (j, 0) + H (j, 1)) := by
  rw [Equiv.sum_comp finProdFinEquiv.symm H, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

lemma dop_div {n : ℕ} (h : Fin n → V n → ℂ) (y : V n) :
    B.Dop (cD n) (vD n) (fun p => h (finProdFinEquiv.symm p).1) y = ∑ j, wd n j (h j) y := by
  have := reindex (n := n) (fun q => ![(1 : ℂ) / 2, -Complex.I / 2] q.2 *
    fderiv ℝ (h q.1) y (![bas n q.1, Complex.I • bas n q.1] q.2))
  exact this.trans (Finset.sum_congr rfl fun j _ => by simp [wd_eq])

def cS : Fin 4 → ℂ := ![1 / 2, Complex.I / 2, -1 / 2, -Complex.I / 2]

def vS (n : ℕ) (j k : Fin n) : Fin 4 → V n :=
  ![bas n j, Complex.I • bas n j, bas n k, Complex.I • bas n k]

lemma dop_sb' {n : ℕ} (j k : Fin n) (g : Fin 4 → V n → ℂ) (a b : V n → ℂ) (h0 : g 0 = a)
    (h1 : g 1 = a) (h2 : g 2 = b) (h3 : g 3 = b) (y : V n) :
    B.Dop cS (vS n j k) g y = wdb n j a y - wdb n k b y := by
  simp [B.Dop, Fin.sum_univ_four, cS, vS, wdb_eq, h0, h1, h2, h3]
  ring

end FlatWeightedEstimates

open FlatWeightedEstimates in
theorem flatGraph (n : ℕ) (hGraph : B.GraphSt (V n) volume ℝ) (hSmooth : B.SmoothSt (V n) volume)
    (hSupp : B.SupportSt (V n) volume) (hStd : B.StdSt (V n) volume) : FlatGraphStatement n := by
  intro Ω K G D S hΩ hK hKΩ hvan hG hD hS hdiv hsb
  obtain ⟨r, hr, hrΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨Metric.cthickening r K, hK.cthickening, hrΩ, fun δ hδ => ?_⟩
  have hGj : ∀ j, MemLp (fun u => G u j) 2 volume := fun j =>
    (EuclideanSpace.proj j : V n →L[ℂ] ℂ).comp_memLp' hG
  have hSjk : ∀ j k, MemLp (fun u => S u j k) 2 volume := fun j k =>
    ((ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj j : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).comp_memLp' hS
  have hGl : ∀ j, LocallyIntegrable (fun u => G u j) volume := fun j =>
    (hGj j).locallyIntegrable (by norm_num)
  have hWD : B.IsWeakD volume (cD n) (vD n)
      (fun p => fun u => G u (finProdFinEquiv.symm p).1) D := by
    refine ⟨fun p => hGl _, hD.locallyIntegrable (by norm_num), fun φ hφ hc => ?_⟩
    have hI := fun j => int_comb (hGl j) hφ hc (1 / 2) (-Complex.I / 2) (bas n j)
      (Complex.I • bas n j)
    have e1 := hdiv φ hφ hc
    simp only [wd_eq] at e1
    rw [integral_finsetSum _ (fun j _ => (hI j).1),
      Finset.sum_congr rfl (fun j _ => (hI j).2)] at e1
    have h2 := reindex (n := n) (fun q => ![(1 : ℂ) / 2, -Complex.I / 2] q.2 *
      ∫ y, G y q.1 * fderiv ℝ φ y (![bas n q.1, Complex.I • bas n q.1] q.2))
    have h3 : ∑ p, cD n p * ∫ x, (fun u => G u (finProdFinEquiv.symm p).1) x *
        fderiv ℝ φ x (vD n p) = ∑ j, (1 / 2 * (∫ y, G y j * fderiv ℝ φ y (bas n j)) +
          -Complex.I / 2 * ∫ y, G y j * fderiv ℝ φ y (Complex.I • bas n j)) :=
      h2.trans (Finset.sum_congr rfl fun j _ => by simp)
    rw [h3, e1, neg_neg]
  have hWS : ∀ j k, B.IsWeakD volume cS (vS n j k)
      (fun p => ![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)
      (fun u => S u j k) := by
    intro j k
    refine ⟨fun p => ?_, (hSjk j k).locallyIntegrable (by norm_num), fun φ hφ hc => ?_⟩
    · fin_cases p <;> exact hGl _
    have hk := int_comb (hGl k) hφ hc (1 / 2) (Complex.I / 2) (bas n j) (Complex.I • bas n j)
    have hj := int_comb (hGl j) hφ hc (1 / 2) (Complex.I / 2) (bas n k) (Complex.I • bas n k)
    have e1 := hsb φ hφ hc j k
    simp only [wdb_eq] at e1
    rw [integral_sub hk.1 hj.1, hk.2, hj.2] at e1
    rw [Fin.sum_univ_four]
    simp only [cS, vS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    linear_combination e1
  have hKr : ∀ t : ℝ, 0 < t → (B.Kernel.std (V n) volume t).r = t := fun t ht => by
    simp [B.Kernel.std, B.Kernel.ofBump, B.stdBump, ht]
  have hGD := hGraph (𝓝[>] 0) (fun t => B.Kernel.std (V n) volume t) hStd _ _ _ _ _ hWD
    (fun p => hGj _) hD
  have hGS := fun j k => hGraph (𝓝[>] 0) (fun t => B.Kernel.std (V n) volume t) hStd _ _ _ _ _
    (hWS j k) (fun p => by fin_cases p <;> exact hGj _) (hSjk j k)
  have T1 : Tendsto (fun t => ∑ j, ∫⁻ y,
      ‖B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y - G y j‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ
      (fun j _ => tendsto_lint _ (hGD.1 (finProdFinEquiv (j, 0))))
    simpa using this
  have T2 := tendsto_lint _ hGD.2
  have T3 : Tendsto (fun t => ∑ j, ∑ k, ∫⁻ y, ‖(B.Dop cS (vS n j k)
      (fun p => B.moll (B.Kernel.std (V n) volume t)
        (![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)) -
      fun u => S u j k) y‖ₑ ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun j _ => tendsto_finsetSum Finset.univ
      (fun k _ => tendsto_lint _ (hGS j k).2))
    simpa using this
  have e4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have e5 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < r := nhdsWithin_le_nhds (Iio_mem_nhds hr)
  have ev := (((T1.eventually (gt_mem_nhds hδ)).and (T2.eventually (gt_mem_nhds hδ))).and
    (T3.eventually (gt_mem_nhds hδ))).and (e4.and e5)
  obtain ⟨t, ⟨⟨h1, h2⟩, h3⟩, ht0', htr'⟩ := ev.exists
  have hmc : ∀ j, ContDiff ℝ ∞ (B.moll (B.Kernel.std (V n) volume t) (fun u => G u j)) :=
    fun j => hSmooth _ _ (hGl j)
  refine ⟨fun y => WithLp.toLp 2 (fun j => B.moll (B.Kernel.std (V n) volume t)
    (fun u => G u j) y), ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_piLp' 2 fun j => hmc j
  · intro y hy
    have hz : ∀ j, B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y = 0 := by
      intro j
      by_contra hne
      have hm := hSupp (B.Kernel.std (V n) volume t) (fun u => G u j) (Function.mem_support.2 hne)
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.1 hm
      apply hy
      have haK : a ∈ K := by
        by_contra haK
        exact ha (by simp [(hvan a haK).1])
      refine Metric.mem_cthickening_of_dist_le _ a r K haK ?_
      rw [hKr t ht0', mem_ball_zero_iff] at hb
      rw [dist_eq_norm, add_sub_cancel_left]
      linarith
    beta_reduce
    rw [show (fun j => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) y) = 0 from funext hz]
    simp
  · refine lt_of_le_of_lt (le_of_eq ?_) h1
    refine (lintegral_congr fun y => ?_).trans (lintegral_finsetSum' _ (fun j _ => ?_))
    · rw [enorm_sq_V]
      rfl
    · exact ((hmc j).continuous.aestronglyMeasurable.sub
        (hGj j).aestronglyMeasurable).eNorm.pow_const 2
  · refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h2
    exact congrArg (fun s => ‖s - D y‖ₑ ^ 2)
      (dop_div (fun j => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j)) y).symm
  · let Q : Fin n → Fin n → V n → ℝ≥0∞ := fun j k y => ‖(B.Dop cS (vS n j k)
        (fun p => B.moll (B.Kernel.std (V n) volume t)
          (![fun u => G u k, fun u => G u k, fun u => G u j, fun u => G u j] p)) -
        fun u => S u j k) y‖ₑ ^ 2
    have hmeas : ∀ j k, AEMeasurable (Q j k) volume := fun j k =>
      ((Finset.measurable_sum _ fun p _ => (measurable_fderiv_apply_const ℝ _ _).const_mul
        _).aestronglyMeasurable.sub (hSjk j k).aestronglyMeasurable).eNorm.pow_const 2
    have hsum : ∫⁻ y, ∑ j, ∑ k, Q j k y = ∑ j, ∑ k, ∫⁻ y, Q j k y := by
      rw [lintegral_finsetSum' _ (fun j _ => Finset.aemeasurable_fun_sum _ fun k _ => hmeas j k)]
      exact Finset.sum_congr rfl fun j _ => lintegral_finsetSum' _ fun k _ => hmeas j k
    refine lt_of_le_of_lt (le_trans (lintegral_mono fun y => ?_) hsum.le) h3
    have hA : ∀ j k, Q j k y =
        ‖wdb n j (fun u => B.moll (B.Kernel.std (V n) volume t) (fun u => G u k) u) y -
          wdb n k (fun u => B.moll (B.Kernel.std (V n) volume t) (fun u => G u j) u) y -
          S y j k‖ₑ ^ 2 := fun j k => by
      simp only [Q]
      rw [Pi.sub_apply, dop_sb' j k _ _ _ rfl rfl rfl rfl y]
      rfl
    refine le_of_le_of_eq ?_ (Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hA j k).symm
    beta_reduce
    unfold sq2
    refine le_trans (ENNReal.ofReal_le_ofReal (half_le_self (by positivity))) (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.PrimZeroOfNonpos
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

namespace EulerCharacteristicLength

def prim (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0:ℝ)..t, f x

theorem prim_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (prim f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem prim_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (prim f) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (prim_hasDerivAt hf.continuous t).differentiableAt, ?_⟩
  have : deriv (prim f) = f := funext fun t => (prim_hasDerivAt hf.continuous t).deriv
  rw [this]; exact hf

theorem prim_zero_of_nonpos {f : ℝ → ℝ} (hf : ∀ x, x ≤ 0 → f x = 0) {t : ℝ} (ht : t ≤ 0) :
    prim f t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
  · simp
  intro x hx
  rw [uIcc_of_ge ht] at hx
  exact hf x hx.2

theorem prim_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, x ≤ 0 → f x = 0) (hf : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ prim f t := by
  rcases le_total t 0 with ht | ht
  · rw [prim_zero_of_nonpos hf0 ht]
  · exact intervalIntegral.integral_nonneg ht (fun x _ => hf x)

theorem prim_pos {f : ℝ → ℝ} (hc : Continuous f) (hf : ∀ x, 0 < x → 0 < f x) {t : ℝ}
    (ht : 0 < t) : 0 < prim f t :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
    (fun x hx => hf x hx.1) ht

def P : ℝ → ℝ := prim expNegInvGlue

def sig : ℝ → ℝ := prim P

theorem rho_contDiff : ContDiff ℝ ∞ expNegInvGlue := expNegInvGlue.contDiff
theorem primitive_contDiff₂ : ContDiff ℝ ∞ P := prim_contDiff rho_contDiff
theorem sig_contDiff : ContDiff ℝ ∞ sig := prim_contDiff primitive_contDiff₂
theorem primitive_hasDerivAt (t : ℝ) : HasDerivAt P (expNegInvGlue t) t :=
  prim_hasDerivAt rho_contDiff.continuous t
theorem sig_hasDerivAt (t : ℝ) : HasDerivAt sig (P t) t := prim_hasDerivAt primitive_contDiff₂.continuous t
theorem P_zero {t : ℝ} (ht : t ≤ 0) : P t = 0 :=
  prim_zero_of_nonpos (fun _ hx => expNegInvGlue.zero_of_nonpos hx) ht
theorem sig_zero {t : ℝ} (ht : t ≤ 0) : sig t = 0 := prim_zero_of_nonpos (fun _ hx => P_zero hx) ht
theorem P_nonneg (t : ℝ) : 0 ≤ P t :=
  prim_nonneg (fun _ hx => expNegInvGlue.zero_of_nonpos hx) expNegInvGlue.nonneg t
theorem sig_nonneg (t : ℝ) : 0 ≤ sig t := prim_nonneg (fun _ hx => P_zero hx) P_nonneg t
theorem twoPow_pos {t : ℝ} (ht : 0 < t) : 0 < P t :=
  prim_pos rho_contDiff.continuous (fun _ hx => expNegInvGlue.pos_of_pos hx) ht
theorem sig_pos {t : ℝ} (ht : 0 < t) : 0 < sig t :=
  prim_pos primitive_contDiff₂.continuous (fun _ hx => twoPow_pos hx) ht
theorem P_mono : Monotone P :=
  monotone_of_deriv_nonneg (fun t => (primitive_hasDerivAt t).differentiableAt)
    (fun t => by rw [(primitive_hasDerivAt t).deriv]; exact expNegInvGlue.nonneg t)
theorem sig_mono : Monotone sig :=
  monotone_of_deriv_nonneg (fun t => (sig_hasDerivAt t).differentiableAt)
    (fun t => by rw [(sig_hasDerivAt t).deriv]; exact P_nonneg t)

def Fs (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * sig (t - (a + k))
def Fs1 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * P (t - (a + k))
def Fs2 (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, c k * expNegInvGlue (t - (a + k))

theorem Fs_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs c a m) (Fs1 c a m t) t := by
  unfold Fs Fs1
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (sig_hasDerivAt _)).const_mul (c k)

theorem Fs1_hasDerivAt (c : ℕ → ℝ) (a : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (Fs1 c a m) (Fs2 c a m t) t := by
  unfold Fs1 Fs2
  apply HasDerivAt.fun_sum
  intro k _
  exact (HasDerivAt.comp_sub_const t (a + k) (primitive_hasDerivAt _)).const_mul (c k)

theorem Fs_contDiff (c : ℕ → ℝ) (a : ℝ) (m : ℕ) : ContDiff ℝ ∞ (Fs c a m) := by
  unfold Fs
  exact ContDiff.sum fun k _ => contDiff_const.mul (sig_contDiff.comp (contDiff_id.sub contDiff_const))

def chiF (c : ℕ → ℝ) (a : ℝ) (t : ℝ) : ℝ := ∑' k : ℕ, c k * sig (t - (a + k))

theorem chiF_eq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) : chiF c a t = Fs c a m t := by
  unfold chiF Fs
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have : (m:ℝ) ≤ k := by exact_mod_cast hk
  rw [sig_zero (by linarith), mul_zero]

theorem chiF_eventuallyEq {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    chiF c a =ᶠ[𝓝 t] Fs c a m :=
  Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => chiF_eq hs

theorem deriv_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (chiF c a) t = Fs1 c a m t := by
  rw [(chiF_eventuallyEq ht).deriv_eq, (Fs_hasDerivAt c a m t).deriv]

theorem deriv2_chiF {c : ℕ → ℝ} {a t : ℝ} {m : ℕ} (ht : t < a + m) :
    deriv (deriv (chiF c a)) t = Fs2 c a m t := by
  have h : deriv (chiF c a) =ᶠ[𝓝 t] Fs1 c a m :=
    Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) fun _ hs => deriv_chiF hs
  rw [h.deriv_eq, (Fs1_hasDerivAt c a m t).deriv]

theorem exists_m (a t : ℝ) : ∃ m : ℕ, t < a + m := by
  obtain ⟨m, hm⟩ := exists_nat_gt (t - a)
  exact ⟨m, by linarith⟩

theorem chiF_contDiff (c : ℕ → ℝ) (a : ℝ) : ContDiff ℝ ∞ (chiF c a) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨m, hm⟩ := exists_m a t
  exact (Fs_contDiff c a m).contDiffAt.congr_of_eventuallyEq (chiF_eventuallyEq hm)

end EulerCharacteristicLength

open EulerCharacteristicLength in
theorem chi : ChiStatement := by
  intro a R hR
  choose B hB using hR
  have hμpos : 0 < min (sig 1) (P 1) := lt_min (sig_pos one_pos) (twoPow_pos one_pos)
  set μ := min (sig 1) (P 1) with hμ
  set c : ℕ → ℝ := fun k => max 0 (B (a + k + 2)) / μ with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => div_nonneg (le_max_left _ _) hμpos.le
  refine ⟨chiF c a, chiF_contDiff c a, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have h0 : ∀ k : ℕ, c k * sig (t - (a + k)) = 0 := fun k => by
      have := k.cast_nonneg (α := ℝ)
      rw [sig_zero (by linarith), mul_zero]
    simp only [chiF, h0, tsum_zero]
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [chiF_eq hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (sig_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (P_nonneg _)
  · intro t
    obtain ⟨m, hm⟩ := exists_m a t
    rw [deriv2_chiF hm]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc0 k) (expNegInvGlue.nonneg _)
  · intro t ht
    set k := ⌊t - a - 1⌋₊ with hk
    have hk1 : (k:ℝ) ≤ t - a - 1 := Nat.floor_le (by linarith)
    have hk2 : t - a - 1 < k + 1 := Nat.lt_floor_add_one _
    have hm : t < a + ((k + 2 : ℕ) : ℝ) := by push_cast; linarith
    have hkm : k ∈ Finset.range (k + 2) := Finset.mem_range.2 (by omega)
    have hRB : R t ≤ B (a + k + 2) := hB (a + k + 2) ⟨t, by simp only [mem_Iic]; linarith, rfl⟩
    have hcμ : c k * μ = max 0 (B (a + k + 2)) := by
      simp only [hcdef]; field_simp
    have hs1 : 1 ≤ t - (a + k) := by linarith
    have hbase : R t ≤ c k * μ := by rw [hcμ]; exact hRB.trans (le_max_right _ _)
    constructor
    · rw [chiF_eq hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (sig_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * sig (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (sig_nonneg _)) hkm
    · rw [deriv_chiF hm]
      refine hbase.trans ((mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (P_mono hs1))
        (hc0 k)).trans ?_)
      exact Finset.single_le_sum (f := fun k => c k * P (t - (a + k)))
        (fun i _ => mul_nonneg (hc0 i) (P_nonneg _)) hkm

end

end ReciprocityTheory.L2DbarEstimates.F
end

