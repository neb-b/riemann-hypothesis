module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem eval_smul_homog (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum,
    MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℂ))]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ m ⟨k, y⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem mcPts_smul {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts J) :
    (fun p => c p.1 * z p) ∈ mcPts J := by
  obtain ⟨S0, hS0, rfl⟩ := hJ
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hle : Ideal.span S0 ≤ RingHom.ker ((MvPolynomial.eval (fun p => c p.1 * z p)).comp
        (MvPolynomial.map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS0 s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
      rw [eval_smul_homog s a ha c z, hz.2 s (Ideal.subset_span hs), mul_zero]
    have := hle hf
    simpa using this

theorem mem_mcPts_of_sameOrbit {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (hz' : z' ∈ mcPts J) : z ∈ mcPts J := by
  obtain ⟨c, hc, rfl⟩ := h
  exact mcPts_smul hJ c hc hz'

theorem segre_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (fun p => c p.1 * z p) = (∏ k, c k) • segre z := by
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

theorem segre_update [DecidableEq K] (z : (Σ k, ι k) → ℂ) (p : (k : K) → ι k) (k : K) (i : ι k) :
    segre z (Function.update p k i) = z ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, z ⟨l, p l⟩ := by
  unfold segre
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun l hl => ?_
    simp [Finset.ne_of_mem_erase hl]

theorem sameOrbit_of_segre {z z' : (Σ k, ι k) → ℂ} (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (μ : ℂ)
    (hμ : μ ≠ 0) (h : segre z = μ • segre z') : SameOrbit z z' := by
  classical
  choose p0 hp0 using hz'
  have hz0 : ∀ k, z ⟨k, p0 k⟩ ≠ 0 := by
    have hs : segre z p0 ≠ 0 := by
      rw [h, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ (Finset.prod_ne_zero_iff.mpr fun k _ => hp0 k)
    intro k hk
    exact hs (Finset.prod_eq_zero (Finset.mem_univ k) hk)
  have hR : ∀ k, ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hz0 l
  have hR' : ∀ k, ∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩ ≠ 0 :=
    fun k => Finset.prod_ne_zero_iff.mpr fun l _ => hp0 l
  refine ⟨fun k => μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / ∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩,
    fun k => div_ne_zero (mul_ne_zero hμ (hR' k)) (hR k), ?_⟩
  funext q
  obtain ⟨k, i⟩ := q
  have e := congrFun h (Function.update p0 k i)
  rw [Pi.smul_apply, smul_eq_mul, segre_update, segre_update] at e
  show z ⟨k, i⟩ = μ * (∏ l ∈ Finset.univ.erase k, z' ⟨l, p0 l⟩) / (∏ l ∈ Finset.univ.erase k, z ⟨l, p0 l⟩) * z' ⟨k, i⟩
  field_simp [hR k]
  linear_combination e

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeN
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology Real

private theorem log_max_norm_le_circleAverage_of_analyticOnNhd {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    Real.log (max ‖h 0‖ 1) ≤ Real.circleAverage (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 := by
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI : CircleIntegrable (fun ζ => Real.log (max ‖h ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hh.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  rcases le_or_gt ‖h 0‖ 1 with h0 | h0
  · rw [max_eq_right h0, Real.log_one]
    have := Real.circleAverage_mono (circleIntegrable_const (0 : ℝ) 0 1) hI
      (fun x _ => Real.log_nonneg (le_max_right _ _))
    rwa [Real.circleAverage_const] at this
  · have hne : h 0 ≠ 0 := by intro e; rw [e, norm_zero] at h0; linarith
    have hh' : AnalyticOnNhd ℂ h (closedBall 0 |1|) := by rwa [abs_one]
    rw [max_eq_left h0.le]
    have hJ := AnalyticOnNhd.circleAverage_log_norm (c := 0) (R := 1) hh' hne
    have hdn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hh'
    have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor h (closedBall 0 |1|)) u : ℝ) *
        Real.log (1 * ‖0 - u‖⁻¹) := by
      apply finsum_nonneg
      intro u
      by_cases hu : u ∈ closedBall (0 : ℂ) |1|
      · apply mul_nonneg
        · exact_mod_cast hdn u
        · rw [one_mul, zero_sub, norm_neg, Real.log_inv]
          rw [abs_one, mem_closedBall, dist_zero_right] at hu
          exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg u) hu)
      · have hz : (MeromorphicOn.divisor h (closedBall 0 |1|)) u = 0 := by
          by_contra hz
          exact hu ((MeromorphicOn.divisor h _).supportWithinDomain hz)
        rw [hz]; simp
    have hlog : CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 :=
      MeromorphicOn.circleIntegrable_log_norm (fun x hx => (hh x (hs hx)).meromorphicAt)
    calc Real.log ‖h 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖h ζ‖) 0 1 := by
          rw [hJ]; linarith
      _ ≤ _ := Real.circleAverage_mono hlog hI (fun x _ => by
          by_cases hx0 : h x = 0
          · simp [hx0]
          · exact Real.log_le_log (norm_pos_iff.2 hx0) (le_max_left _ _))

theorem isPsh_logmax {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {f : (Fin D → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ReciprocityTheory.AnForm.A.IsPsh U (fun z => Real.log (max ‖f z‖ ε)) := by
  refine ⟨?_, fun z w hdisc => ?_⟩
  · exact ContinuousOn.upperSemicontinuousOn (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm hf.continuousOn) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right hε).ne'))
  set g : ℂ → ℂ := fun ζ => (ε : ℂ)⁻¹ * f (z + ζ • w) with hg
  have hga : AnalyticOnNhd ℂ g (closedBall 0 1) := by
    intro ζ hζ
    have hz : z + ζ • w ∈ U := hdisc ζ (by simpa using hζ)
    have hφ : AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ :=
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hc : AnalyticAt ℂ (fun ζ : ℂ => f (z + ζ • w)) ζ :=
      AnalyticAt.comp (g := f) (f := fun ζ : ℂ => z + ζ • w) (hf _ hz) hφ
    exact analyticAt_const.mul hc
  have hs : sphere (0 : ℂ) |1| ⊆ closedBall 0 1 := by rw [abs_one]; exact sphere_subset_closedBall
  have hI2 : CircleIntegrable (fun ζ => Real.log (max ‖g ζ‖ 1)) 0 1 :=
    ContinuousOn.circleIntegrable' (ContinuousOn.log
      (ContinuousOn.sup (ContinuousOn.norm (hga.continuousOn.mono hs)) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne'))
  have hkey : ∀ ζ : ℂ, Real.log (max ‖f (z + ζ • w)‖ ε) = Real.log ε + Real.log (max ‖g ζ‖ 1) := by
    intro ζ
    have hnorm : ‖g ζ‖ = ‖f (z + ζ • w)‖ / ε := by
      simp only [hg, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      rw [div_eq_inv_mul]
    rw [hnorm, ← Real.log_mul hε.ne' (lt_max_of_lt_right one_pos).ne', mul_max_of_nonneg _ _ hε.le,
      show ε * (‖f (z + ζ • w)‖ / ε) = ‖f (z + ζ • w)‖ by field_simp, mul_one]
  have hfun : (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) =
      fun ζ => Real.log ε + Real.log (max ‖g ζ‖ 1) := funext hkey
  refine ⟨?_, ?_⟩
  · show CircleIntegrable (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun]
    exact (circleIntegrable_const _ _ _).add hI2
  · show Real.log (max ‖f z‖ ε) ≤ Real.circleAverage (fun ζ : ℂ => Real.log (max ‖f (z + ζ • w)‖ ε)) 0 1
    rw [hfun, Real.circleAverage_fun_add (circleIntegrable_const _ _ _) hI2, Real.circleAverage_const]
    have h0 := hkey 0
    simp only [zero_smul, add_zero] at h0
    rw [h0]
    linarith [log_max_norm_le_circleAverage_of_analyticOnNhd hga]

theorem integrableOn_log_norm_closedBall {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) {z0 : Fin D → ℂ} {t : ℝ} (ht : 0 < t)
    (hS2 : ball z0 (2 * t) ⊆ U) (hz0 : f z0 ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall z0 t) := by
  set B := closedBall z0 t with hBdef
  have hBU : B ⊆ U := fun x hx =>
    hS2 (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)))
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBfin : volume B < ⊤ := measure_closedBall_lt_top
  have hfc : ContinuousOn f B := hf.continuousOn.mono hBU
  set c : ℝ := min ‖f z0‖ 1 with hc
  have hc0 : 0 < c := lt_min (norm_pos_iff.2 hz0) one_pos
  set ε : ℕ → ℝ := fun n => c / ((n : ℝ) + 1) with hεdef
  have hε0 : ∀ n, 0 < ε n := fun n => div_pos hc0 (by positivity)
  have hεc : ∀ n, ε n ≤ c := fun n =>
    div_le_self hc0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε1 : ∀ n, ε n ≤ 1 := fun n => (hεc n).trans (min_le_right _ _)
  have hεanti : ∀ m n : ℕ, m ≤ n → ε n ≤ ε m := fun m n hmn =>
    div_le_div_of_nonneg_left hc0.le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hmn; linarith)
  set φ : ℕ → (Fin D → ℂ) → ℝ := fun n x => Real.log (max ‖f x‖ (ε n)) with hφdef
  set φ1 : (Fin D → ℂ) → ℝ := fun x => Real.log (max ‖f x‖ 1) with hφ1def
  have hsub : ∀ n, IntegrableOn (φ n) B ∧ φ n z0 ≤ ⨍ x in B, φ n x := fun n =>
    ReciprocityTheory.AnForm.A.subMeanPolydisc_thm D U (φ n) z0 t hU (isPsh_logmax hU hf (hε0 n)) ht hBU
  have hφc : ∀ n, ContinuousOn (φ n) B := fun n =>
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right (hε0 n)).ne')
  have hφ1c : ContinuousOn φ1 B :=
    ContinuousOn.log (ContinuousOn.sup (ContinuousOn.norm hfc) continuousOn_const)
      (fun x _ => (lt_max_of_lt_right one_pos).ne')
  have hφ1i : IntegrableOn φ1 B := ContinuousOn.integrableOn_compact (isCompact_closedBall z0 t) hφ1c
  have hφz0 : ∀ n, φ n z0 = Real.log ‖f z0‖ := fun n => by
    simp only [hφdef]
    rw [max_eq_left ((hεc n).trans (min_le_left _ _))]
  have hφle : ∀ n x, φ n x ≤ φ1 x := fun n x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hε1 n))
  have hφanti : ∀ m n : ℕ, m ≤ n → ∀ x, φ n x ≤ φ m x := fun m n hmn x =>
    Real.log_le_log (lt_max_of_lt_right (hε0 n)) (max_le_max le_rfl (hεanti m n hmn))
  set V := (volume B).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (measure_closedBall_pos volume z0 ht).ne' hBfin.ne
  have hlow : ∀ n, V * Real.log ‖f z0‖ ≤ ∫ x in B, φ n x := by
    intro n
    have h1 : Real.log ‖f z0‖ ≤ V⁻¹ * ∫ x in B, φ n x := by
      have h2 := (hsub n).2
      rw [setAverage_eq, smul_eq_mul] at h2
      exact (hφz0 n).symm.le.trans h2
    have h3 := mul_le_mul_of_nonneg_left h1 hV.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul] at h3
  set G : (Fin D → ℂ) → ℝ := fun x => φ1 x - Real.log ‖f x‖ with hGdef
  have hG0 : ∀ x, 0 ≤ G x := by
    intro x
    simp only [hGdef, hφ1def, sub_nonneg]
    by_cases hx : f x = 0
    · simp [hx]
    · exact Real.log_le_log (norm_pos_iff.2 hx) (le_max_left _ _)
  have hpt : ∀ x, ENNReal.ofReal (G x) ≤ ⨆ n, ENNReal.ofReal (φ1 x - φ n x) := by
    intro x
    by_cases hx : f x = 0
    · have : G x = 0 := by simp [hGdef, hφ1def, hx]
      rw [this, ENNReal.ofReal_zero]; exact zero_le
    · have hpos : 0 < ‖f x‖ := norm_pos_iff.2 hx
      obtain ⟨n, hn⟩ := exists_nat_gt (c / ‖f x‖)
      have hn' : ε n ≤ ‖f x‖ := by
        rw [div_lt_iff₀ hpos] at hn
        show c / ((n : ℝ) + 1) ≤ ‖f x‖
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      refine le_iSup_of_le n (le_of_eq ?_)
      congr 1
      simp only [hGdef, hφdef, max_eq_left hn']
  have hmeasn : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ1 x - φ n x)) (volume.restrict B) :=
    fun n => ((hφ1c.sub (hφc n)).aemeasurable hBm).ennreal_ofReal
  have hsup : ∫⁻ x in B, ⨆ n, ENNReal.ofReal (φ1 x - φ n x) =
      ⨆ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) :=
    lintegral_iSup' hmeasn (Filter.Eventually.of_forall fun x m n hmn =>
      ENNReal.ofReal_le_ofReal (sub_le_sub_left (hφanti m n hmn x) _))
  have hbound : ∀ n, ∫⁻ x in B, ENNReal.ofReal (φ1 x - φ n x) ≤
      ENNReal.ofReal ((∫ x in B, φ1 x) - V * Real.log ‖f z0‖) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => φ1 x - φ n x) (hφ1i.sub (hsub n).1)
      (Filter.Eventually.of_forall fun x => sub_nonneg.2 (hφle n x))]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sub hφ1i (hsub n).1]
    linarith [hlow n]
  have hfin : ∫⁻ x in B, ENNReal.ofReal (G x) < ⊤ :=
    lt_of_le_of_lt ((lintegral_mono hpt).trans (hsup.le.trans (iSup_le hbound))) ENNReal.ofReal_lt_top
  have hlogm : AEStronglyMeasurable (fun x => Real.log ‖f x‖) (volume.restrict B) :=
    (Real.measurable_log.comp_aemeasurable ((ContinuousOn.norm hfc).aemeasurable hBm)).aestronglyMeasurable
  have hGi : IntegrableOn G B :=
    ⟨(hφ1c.aestronglyMeasurable hBm).sub hlogm,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0)).2 hfin⟩
  refine (hφ1i.sub hGi).congr_fun (fun x _ => ?_) hBm
  simp [hGdef]

theorem logAbsLocInt' (D : ℕ) (U : Set (Fin D → ℂ)) (f : (Fin D → ℂ) → ℂ) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : LocallyIntegrableOn (fun z => Real.log ‖f z‖) U volume := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  by_cases h : ∃ z0 ∈ ball z (r / 5), f z0 ≠ 0
  · obtain ⟨z0, hz0, hfz0⟩ := h
    refine ⟨closedBall z0 (2 * (r / 5)), ?_,
      integrableOn_log_norm_closedBall hU hf (by positivity) ?_ hfz0⟩
    · apply mem_nhdsWithin_of_mem_nhds
      refine Filter.mem_of_superset (ball_mem_nhds z (by positivity : (0 : ℝ) < r / 5)) ?_
      intro x hx
      rw [mem_closedBall]
      rw [mem_ball] at hx hz0
      calc dist x z0 ≤ dist x z + dist z z0 := dist_triangle _ _ _
        _ ≤ 2 * (r / 5) := by rw [dist_comm z z0]; linarith
    · intro x hx
      apply hball
      rw [mem_ball] at hx hz0 ⊢
      calc dist x z ≤ dist x z0 + dist z0 z := dist_triangle _ _ _
        _ < r := by linarith
  · push_neg at h
    refine ⟨ball z (r / 5), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (by positivity)), ?_⟩
    exact IntegrableOn.congr_fun integrableOn_zero (fun x hx => by simp [h x hx]) measurableSet_ball

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  [∀ k, DecidableEq (ι k)]

variable (ι) in
def segMono (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℂ := ∏ k, X ⟨k, i k⟩

theorem eval_segMono (i : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) : eval z (segMono ι i) = segre z i := by
  simp [segMono, segre, map_prod]

theorem segMono_homog (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkW ι) (segMono ι i) (fun _ => 1) := by
  have := IsWeightedHomogeneous.prod (w := blkW ι) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))
    (fun k => blkW ι ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℂ _ _)
  unfold segMono
  convert this using 1
  funext k'
  simp [blkW, Finset.sum_apply, Pi.single_apply]

variable {e : ℕ}

def psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    MvPolynomial (Σ k, ι k) ℂ :=
  ∑ i, C (Ψ (fun i' => if i = i' then 1 else 0) j) * segMono ι i

theorem eval_psiPoly (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1))
    (z : (Σ k, ι k) → ℂ) : eval z (psiPoly Ψ j) = Ψ (segre z) j := by
  have hs : segre z = ∑ i, segre z i • (fun i' => if i = i' then (1 : ℂ) else 0) := by
    funext i'
    simp [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psiPoly, map_sum, map_mul, eval_C, eval_segMono]
  conv_rhs => rw [hs]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem psiPoly_homog (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (j : Fin (e + 1)) :
    IsWeightedHomogeneous (blkW ι) (psiPoly Ψ j) (fun _ => 1) := by
  have hmem : psiPoly Ψ j ∈ weightedHomogeneousSubmodule ℂ (blkW ι) (fun _ => 1) := by
    unfold psiPoly
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [C_mul']
    exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (segMono_homog i))
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp hmem

variable (ι) in
def idealC (P : Ideal (MRing ι)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.map (map (Int.castRingHom ℂ)) P

theorem eval_idealC {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {f}
    (hf : f ∈ idealC ι P) : eval z f = 0 := by
  have hle : idealC ι P ≤ RingHom.ker (eval z) := by
    rw [idealC, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 g hg
  exact hle hf

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem idealC_homog {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    (idealC ι P).IsHomogeneous (weightedHomogeneousSubmodule ℂ (blkW ι)) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [idealC, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨a, ha⟩ := hS g hg
  exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (isWeightedHomogeneous_map_of_isMultiHomog ha)⟩

theorem segre_rel {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (i : (k : K) → ι k) :
    ∃ r : ℕ, 0 < r ∧ ∃ G : Fin (e + 1) → MvPolynomial ((k : K) → ι k) ℂ,
      (∀ j, (G j).totalDegree ≤ r - 1) ∧
      ∀ z ∈ mcPts P, segre z i ^ r = ∑ j, Ψ (segre z) j * eval (segre z) (G j) := by
  classical
  set J : Ideal (MvPolynomial (Σ k, ι k) ℂ) := idealC ι P ⊔ Ideal.span (Set.range (psiPoly Ψ)) with hJ
  have hvan : segMono ι i ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz0
    rw [MvPolynomial.mem_zeroLocus_iff] at hz0
    have hz : ∀ p ∈ J, eval z p = 0 := fun p hp => hz0 p hp
    change eval z (segMono ι i) = 0
    by_contra hne
    have hmc : z ∈ mcPts P := by
      refine ⟨fun k => ⟨i k, ?_⟩, fun f hf => ?_⟩
      · intro h0
        apply hne
        rw [eval_segMono]
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · exact hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))
    apply hΨ z hmc
    funext j
    have := hz (psiPoly Ψ j) (Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩))
    rw [eval_psiPoly] at this
    exact this
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hvan
  obtain ⟨n, hn⟩ := hvan
  have hn1 : segMono ι i ^ (n + 1) ∈ J := by
    rw [pow_succ]
    exact J.mul_mem_right _ hn
  obtain ⟨g, hg, a, ha, hga⟩ := Submodule.mem_sup.mp hn1
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
  have hcomp : ∀ j, ∃ G : MvPolynomial ((k : K) → ι k) ℂ, G.totalDegree ≤ n ∧ ∀ z : (Σ k, ι k) → ℂ,
      eval z (weightedHomogeneousComponent (blkW ι) (fun _ => n) (c j)) = eval (segre z) G :=
    fun j => diag_of_homog n (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  choose G hG1 hG2 using hcomp
  refine ⟨n + 1, Nat.succ_pos n, G, fun j => by simpa using hG1 j, ?_⟩
  intro z hz
  have hD : (fun _ : K => n + 1) = (fun _ : K => n) + (fun _ : K => 1) := by
    funext k; simp
  have hseg : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (segMono ι i ^ (n + 1)) =
      segMono ι i ^ (n + 1) := by
    have hh := (segMono_homog (ι := ι) i).pow (n + 1)
    have hh' : (n + 1) • (fun _ : K => (1 : ℕ)) = fun _ : K => n + 1 := by funext k; simp
    rw [hh'] at hh
    exact weightedHomogeneousComponent_eq_self hh
  have hgc : weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) g ∈ idealC ι P := by
    have h := (idealC_homog hP) (fun _ : K => n + 1) hg
    rw [← weightedDecomposition.decompose'_apply ℂ (blkW ι) g (fun _ : K => n + 1)]
    exact h
  have hterm : ∀ j, weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1) (c j * psiPoly Ψ j) =
      weightedHomogeneousComponent (blkW ι) (fun _ : K => n) (c j) * psiPoly Ψ j := by
    intro j
    rw [hD]
    exact comp_mul_homog (psiPoly_homog Ψ j) (c j) _
  have heq := congrArg (weightedHomogeneousComponent (blkW ι) (fun _ : K => n + 1)) hga
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hseg, map_add (f := _), ← hc, map_sum] at heq
  simp only [hterm] at heq
  have hev := congrArg (eval z) heq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, eval_idealC hz hgc, zero_add, map_pow, eval_segMono] at hev
  rw [← hev]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, hG2, eval_psiPoly, mul_comm]

theorem fibreFinite : FibreFiniteStatement := by
  intro K _ ι _ P e Ψ hP hΨ y
  classical
  choose r hr G hG hrel using fun i => segre_rel hP.2.1.2.1 Ψ hΨ i
  let H : ((k : K) → ι k) → MvPolynomial ((k : K) → ι k) ℂ := fun i =>
    ∑ j, C ((Fin.cons 1 y : Fin (e + 1) → ℂ) j) * G i j
  refine (fibSys_finite r H (fun i => ?_)).subset ?_
  · refine lt_of_le_of_lt ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_))
      (Nat.sub_lt (hr i) one_pos)
    exact (totalDegree_mul _ _).trans (by simpa using hG i j)
  · rintro w ⟨z, hz, rfl, hΨz⟩ i
    rw [hrel i z hz, hΨz]
    simp [H]

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.KerEqBotOfCoord
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M OnePoint Filter Topology MeasureTheory

namespace ProjectiveLineResolution


end ProjectiveLineResolution

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

