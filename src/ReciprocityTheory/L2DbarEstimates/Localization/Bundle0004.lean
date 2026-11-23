module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.LeviZCoordChart
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

private theorem coe_symm_apply_of_isChart_val {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (y : M) (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    e'.symm =ᶠ[𝓝 (z y)] e.symm := by

  have hzy : z y = e' y := he' hy'
  have hzy2 : z y = e y := he hy
  have hopen : IsOpen (e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source)) :=
    e.open_target.inter (e'.isOpen_inter_preimage_symm e.open_source)
  have hmem : z y ∈ e.target ∩ (e'.target ∩ e'.symm ⁻¹' e.source) := by
    refine ⟨by rw [hzy2]; exact e.map_source hy, by rw [hzy]; exact e'.map_source hy', ?_⟩
    show e'.symm (z y) ∈ e.source
    rw [hzy, e'.left_inv hy']
    exact hy
  filter_upwards [hopen.mem_nhds hmem] with w hw
  obtain ⟨_, hw2, hw3⟩ := hw
  have ha : e'.symm w ∈ e'.source := e'.map_target hw2
  have hea : e (e'.symm w) = w := by
    rw [← he hw3, he' ha, e'.right_inv hw2]
  calc e'.symm w = e.symm (e (e'.symm w)) := (e.left_inv hw3).symm
    _ = e.symm w := by rw [hea]

private theorem wdb_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wdb n k F p = wdb n k G p := by
  unfold wdb
  rw [h.fderiv_eq]

private theorem wd_apply_congr_of_eventuallyEq (n : ℕ) (k : Fin n) {F G : V n → ℂ} {p : V n} (h : F =ᶠ[𝓝 p] G) :
    wd n k F p = wd n k G p := by
  unfold wd
  rw [h.fderiv_eq]

private theorem db_apply_eq_wdb_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : db n z k f y = wdb n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold db
  rw [dite_eq_left hex]
  apply wdb_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

private theorem d_apply_eq_wd_of_mem_source {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : Fin n)
    (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : M)
    (hy : y ∈ e.source) : d n z k f y = wd n k (f ∘ e.symm) (z y) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ y ∈ e.source := ⟨e, he, hy⟩
  unfold d
  rw [dite_eq_left hex]
  apply wd_apply_congr_of_eventuallyEq
  exact (coe_symm_apply_of_isChart_val n z e (Classical.choose hex) he (Classical.choose_spec hex).1 y hy
    (Classical.choose_spec hex).2).fun_comp f

theorem leviZ_coord_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (l : Fin n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    EqOn ((fun y => z y l) ∘ e.symm) (fun w : V n => w l) e.target := by
  intro w hw
  simp only [Function.comp_apply]
  rw [he (e.map_target hw), e.right_inv hw]

theorem leviZ_wd_coord (n : ℕ) (j l : Fin n) (y : V n) :
    wd n j (fun w : V n => w l) y = if j = l then 1 else 0 := by
  have hL : fderiv ℝ (fun w : V n => w l) y =
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) :=
    ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ).fderiv
  unfold wd
  rw [hL]
  by_cases h : j = l
  · subst h
    simp [bas, PiLp.single_apply, Complex.I_mul_I]
  · simp [bas, PiLp.single_apply, h, Ne.symm h]

theorem leviZ_d_coord {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (j l : Fin n) (x : M) :
    d n z j (fun y => z y l) x = if j = l then 1 else 0 := by
  obtain ⟨e, hx, hze⟩ := hz x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hzx : z x ∈ e.target := by rw [he hx]; exact e.map_source hx
  rw [d_apply_eq_wd_of_mem_source n z j _ e he x hx,
    wd_apply_congr_of_eventuallyEq n j (G := fun w : V n => w l) (by
      filter_upwards [e.open_target.mem_nhds hzx] with w hw
      exact leviZ_coord_chart n z l e he hw)]
  exact leviZ_wd_coord n j l (z x)

private theorem wdb_sum_mul_conj_eq_coord (n : ℕ) (k : Fin n) (p : V n) :
    wdb n k (fun w : V n => ∑ l, w l * conj (w l)) p = p k := by
  have hP : ∀ l, HasFDerivAt (fun w : V n => w l)
      ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) p :=
    fun l => (EuclideanSpace.proj l : V n →L[ℂ] ℂ).hasFDerivAt.restrictScalars ℝ
  have hC : ∀ l, HasFDerivAt (fun w : V n => conj (w l))
      (Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    fun l => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp p (hP l)
  have hF : HasFDerivAt (fun w : V n => ∑ l, w l * conj (w l))
      (∑ l, (p l • Complex.conjCLE.toContinuousLinearMap.comp
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ) +
        conj (p l) • (EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)) p :=
    HasFDerivAt.fun_sum (fun l _ => (hP l).mul (hC l))
  unfold wdb
  rw [hF.fderiv]
  simp [bas, PiLp.single_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Complex.conj_I,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linear_combination ((starRingEnd ℂ (p.ofLp k) - p.ofLp k) / 2) * Complex.I_sq

theorem leviNormSq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : LeviNormSqStatement n M := by
  intro z hz
  have hchart : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := by
    intro x
    obtain ⟨e, hx, hze⟩ := hz x
    exact ⟨e, fun y _ => congrFun hze y, hx⟩

  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      EqOn ((fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) ∘ e.symm) (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ))
        e.target := by
    intro e he w hw
    simp only [Function.comp_apply]
    rw [he (e.map_target hw), e.right_inv hw]
  have hsq : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ l, w l * conj (w l) := by
    funext w
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine ⟨fun e he => ?_, fun x ξ => ?_⟩
  · have hsm : ContDiffOn ℝ ∞ (fun w : V n => ∑ l, w l * conj (w l)) e.target := by
      refine ContDiffOn.sum (fun l _ => ?_)
      have hPc : ContDiff ℝ ∞ (fun w : V n => w l) :=
        ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ).contDiff
      have hCc : ContDiff ℝ ∞ (fun w : V n => conj (w l)) :=
        (Complex.conjCLE.toContinuousLinearMap.comp
          ((EuclideanSpace.proj l : V n →L[ℂ] ℂ).restrictScalars ℝ)).contDiff
      exact (hPc.mul hCc).contDiffOn
    rw [← hsq] at hsm
    exact hsm.congr (hloc e he)
  ·
    have hdb : ∀ k, db n z k (fun y => ((‖z y‖ ^ 2 : ℝ) : ℂ)) = fun y => z y k := by
      intro k
      funext y
      obtain ⟨e, he, hy⟩ := hchart y
      have hzy : z y ∈ e.target := by rw [he hy]; exact e.map_source hy
      rw [db_apply_eq_wdb_of_mem_source n z k _ e he y hy,
        wdb_apply_congr_of_eventuallyEq n k (G := fun w : V n => ∑ l, w l * conj (w l)) (by
          rw [← hsq]
          filter_upwards [e.open_target.mem_nhds hzy] with w hw
          exact hloc e he hw)]
      exact wdb_sum_mul_conj_eq_coord n k (z y)
    simp only [Levi, hdb, leviZ_d_coord n z hz]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.Primed
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem primed_lintegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a F G : α → ℝ≥0∞) (hF : AEMeasurable F μ) (hG : AEMeasurable G μ)
    (h : ∀ x, a x ^ 2 ≤ F x * G x) :
    (∫⁻ x, a x ∂μ) ^ 2 ≤ (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
  have hpt : ∀ x, a x ≤ F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := by
    intro x
    calc a x = (a x ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      _ ≤ (F x * G x) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow (h x) (by norm_num)
      _ = F x ^ (1 / 2 : ℝ) * G x ^ (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (hF.pow_const (1 / 2 : ℝ)) (hG.pow_const (1 / 2 : ℝ))
  have hsq : ∀ y : ℝ≥0∞, (y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = y := by
    intro y; rw [← ENNReal.rpow_mul]; norm_num
  simp only [hsq, Pi.mul_apply] at hH
  have hle : ∫⁻ x, a x ∂μ ≤ (∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ) :=
    (lintegral_mono hpt).trans hH
  calc (∫⁻ x, a x ∂μ) ^ 2
      ≤ ((∫⁻ x, F x ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ x, G x ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, F x ∂μ) * ∫⁻ x, G x ∂μ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 2),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

theorem primed_ofReal_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hm : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf) hm]
    exact ENNReal.ofReal_toReal_le
  · rw [integral_non_aestronglyMeasurable hm]
    simp

theorem primed_inner_norm (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (F0 : M → ℂ)
    (g : M → V n) (x : M) :
    ‖⟪dbarF n z F0 x, g x⟫_ℂ‖ = ‖dbarDot n z F0 x (fun j => g x j)‖ := by
  have : ⟪dbarF n z F0 x, g x⟫_ℂ = starRingEnd ℂ (dbarDot n z F0 x (fun j => g x j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dbarF, dbarDot, PiLp.inner_apply, map_sum, mul_comm]
  rw [this, Complex.norm_conj]

theorem primedIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hAP : APStatement n M) : PrimedIneqStatement n M := by
  intro z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hpp hlevi hA g hg
  have cR : ∀ f : M → ℝ, SmoothR n z f → Continuous f := fun f hf => by
    exact (Complex.continuous_re.comp (Smooth.continuous n z hz _ hf)).congr fun x => by simp
  have cph' := cR ph' hph'
  have cψ := cR ψ hψ
  have cg : ∀ j, Continuous fun x => g x j := fun j => Ck.continuous n z hz 2 _ (hg j).1
  have cLevi : ∀ q : M → ℝ, SmoothR n z q →
      Continuous fun x => (Levi n z q x (fun j => g x j)).re := by
    intro q hq
    refine Complex.continuous_re.comp ?_
    unfold Levi
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    exact ((Smooth.continuous n z hz _ (Smooth.d n z j _ (Smooth.db n z k _ hq))).mul
      (cg j)).mul (Complex.continuous_conj.comp (cg k))
  have cdS : Continuous fun x => dSqR n z ψ x := by
    unfold dSqR
    exact continuous_finsetSum _ fun j _ =>
      ((Smooth.continuous n z hz _ (Smooth.d n z j _ hψ)).norm.pow 2)
  have hnorm : ∀ x, ‖g x‖ ^ 2 = ∑ j, ‖g x j‖ ^ 2 := fun x => EuclideanSpace.norm_sq_eq (g x)
  have cgn : Continuous fun x => ‖g x‖ ^ 2 := by
    simp_rw [hnorm]; exact continuous_finsetSum _ fun j _ => (cg j).norm.pow 2
  have hKc : IsCompact (⋃ j, tsupport (fun x => g x j)) :=
    isCompact_iUnion fun j => (hg j).2
  have hgK : ∀ x, x ∉ (⋃ j, tsupport (fun x => g x j)) → g x = 0 := by
    intro x hx
    simp only [mem_iUnion, not_exists] at hx
    ext j
    exact image_eq_zero_of_notMem_tsupport (f := fun x => g x j) (hx j)
  set Q : M → ℝ := fun x => ((Levi n z ph' x (fun j => g x j)).re -
      (1 + 1 / ε) * dSqR n z ψ x * ‖g x‖ ^ 2) * Real.exp (-ph' x) with hQ
  have cQ : Continuous Q := ((cLevi ph' hph').sub ((continuous_const.mul cdS).mul cgn)).mul
    (Real.continuous_exp.comp cph'.neg)
  have sQ : HasCompactSupport Q := HasCompactSupport.intro hKc fun x hx => by
    simp [hQ, hgK x hx, Levi]
  have iQ : Integrable Q (vol n z) := integrable_of_continuous_real n z hz Q cQ sQ
  have hL0 : ∀ x, 0 ≤ (Levi n z ph x (fun j => g x j)).re := fun x => hlev x _
  have hLQ : ∀ x, (Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x) ≤ Q x := by
    intro x
    have h1 := hlevi x (fun j => g x j)
    beta_reduce at h1
    rw [← hnorm x] at h1
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hQ0 : ∀ x, 0 ≤ Q x := fun x =>
    (mul_nonneg (hL0 x) (Real.exp_pos _).le).trans (hLQ x)
  have hap := hAP z hz ph' ψ ε g (SmoothR.ckR n z 2 ph' hph') (SmoothR.ckR n z 1 ψ hψ) hε hg
  set Gf : M → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((Levi n z ph x (fun j => g x j)).re * Real.exp (-ph' x)) with hGf
  set Ff : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) with hFf
  have hG : ∫⁻ x, Gf x ∂vol n z ≤ ENNReal.ofReal (1 + ε) *
      wint n z (tstar n z (w1 ph' ψ) (w2 ph' ψ) g) (w1 ph' ψ) + n2 n z (sbar n z g) ph' := by
    calc ∫⁻ x, Gf x ∂vol n z ≤ ∫⁻ x, ENNReal.ofReal (Q x) ∂vol n z :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hLQ x)
      _ = ENNReal.ofReal (∫ x, Q x ∂vol n z) :=
          (ofReal_integral_eq_lintegral_ofReal iQ (Eventually.of_forall hQ0)).symm
      _ ≤ ENNReal.ofReal ((1 + ε) * (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) :=
          ENNReal.ofReal_le_ofReal hap
      _ ≤ ENNReal.ofReal (1 + ε) * ENNReal.ofReal (∫ x, ‖tstar n z (fun y => ph' y - 2 * ψ y)
            (fun y => ph' y - ψ y) g x‖ ^ 2 * Real.exp (-(ph' x - 2 * ψ x)) ∂vol n z) +
            ENNReal.ofReal (∫ x, sq2 n (sbar n z g x) * Real.exp (-ph' x) ∂vol n z) := by
          rw [← ENNReal.ofReal_mul (by linarith)]; exact ENNReal.ofReal_add_le
      _ ≤ _ := by
          gcongr
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
          · exact primed_ofReal_integral_le _ _ fun x =>
              mul_nonneg (by unfold sq2; positivity) (Real.exp_pos _).le
  have hF : ∫⁻ x, Ff x ∂vol n z ≤ ∫⁻ x, h x * ENNReal.ofReal (Real.exp (-ph x)) ∂vol n z :=
    lintegral_mono fun x => by
      simp only [hFf]
      gcongr
      linarith [hpp x]
  have mF : AEMeasurable Ff (vol n z) :=
    (hh.mul (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul cψ).sub cph')).measurable)).aemeasurable
  have mG : AEMeasurable Gf (vol n z) :=
    (ENNReal.continuous_ofReal.comp ((cLevi ph hph).mul
      (Real.continuous_exp.comp cph'.neg))).measurable.aemeasurable
  set I : M → ℂ := fun x => ⟪dbarF n z F0 x, g x⟫_ℂ * (Real.exp (-w2 ph' ψ x) : ℂ) with hI
  have hpt : ∀ x, ‖I x‖ₑ ^ 2 ≤ Ff x * Gf x := by
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [hI, hFf, hGf]
    rw [norm_mul, primed_inner_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), mul_pow]
    have he : Real.exp (-w2 ph' ψ x) ^ 2 = Real.exp (2 * ψ x - ph' x) * Real.exp (-ph' x) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; simp only [w2]; ring
    rw [he, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_mul (hL0 x)]
    calc ENNReal.ofReal (‖dbarDot n z F0 x (fun j => g x j)‖ ^ 2) *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x)))
        ≤ h x * ENNReal.ofReal (Levi n z ph x (fun j => g x j)).re *
          (ENNReal.ofReal (Real.exp (2 * ψ x - ph' x)) * ENNReal.ofReal (Real.exp (-ph' x))) := by
          gcongr; exact hdom x _
      _ = _ := by ring
  show ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) ≤ _
  calc ENNReal.ofReal (‖∫ x, I x ∂vol n z‖ ^ 2) = ‖∫ x, I x ∂vol n z‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ (∫⁻ x, ‖I x‖ₑ ∂vol n z) ^ 2 := by
        gcongr; exact enorm_integral_le_lintegral_enorm _
    _ ≤ (∫⁻ x, Ff x ∂vol n z) * ∫⁻ x, Gf x ∂vol n z :=
        primed_lintegral_sq_le _ _ _ _ mF mG hpt
    _ ≤ _ := mul_le_mul' hF hG

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.SSmooth
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem weakSSmooth (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : WeakSSmoothStatement n M := by
  intro z hz f hf φ hφ j k
  have hφ1 : Ck n z 1 φ := Smooth.ck n z 1 φ hφ.1
  have hcd : ∀ i : Fin n, HasCompactSupport (db n z i φ) := fun i =>
    hφ.2.mono' ((subset_tsupport _).trans (tsupport_db_subset n z i φ))
  have hcont : ∀ i : Fin n, Continuous (db n z i φ) := fun i =>
    Ck.continuous n z hz 0 _ (Ck.db n z 0 i φ hφ1)
  have hfc : ∀ i : Fin n, Continuous (fun y => f y i) := fun i => Ck.continuous n z hz 1 _ (hf i)
  have hI1 : ∀ a b : Fin n, Integrable (fun x => f x a * db n z b φ x) (vol n z) := fun a b =>
    integrable_of_continuous n z hz _ ((hfc a).mul (hcont b)) ((hcd b).mul_left)
  have hI2 : ∀ a b : Fin n, Integrable (fun x => db n z b (fun y => f y a) x * φ x) (vol n z) :=
    fun a b => integrable_of_continuous n z hz _
      ((Ck.continuous n z hz 0 _ (Ck.db n z 0 b _ (hf a))).mul (Ck.continuous n z hz 1 _ hφ1))
      hφ.2.mul_left
  have h1 := integral_db_mul n z hz j (fun y => f y k) φ (hf k) hφ1 hφ.2
  have h2 := integral_db_mul n z hz k (fun y => f y j) φ (hf j) hφ1 hφ.2
  have hL : ∫ x, (f x k * db n z j φ x - f x j * db n z k φ x) ∂vol n z
      = ∫ x, f x k * db n z j φ x ∂vol n z - ∫ x, f x j * db n z k φ x ∂vol n z :=
    integral_sub (hI1 k j) (hI1 j k)
  have hR : ∫ x, sbar n z f x j k * φ x ∂vol n z
      = ∫ x, db n z j (fun y => f y k) x * φ x ∂vol n z
        - ∫ x, db n z k (fun y => f y j) x * φ x ∂vol n z := by
    rw [← integral_sub (hI2 k j) (hI2 j k)]
    congr 1
    funext x
    simp only [sbar, sub_mul]
  rw [hL, hR, h1, h2]
  ring

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[𝓝 (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ 𝓝 (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[𝓝 (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma fderiv_wdb_apply_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) (v : V n) :
    fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hF : fderiv ℝ (wdb n k h) y0 = (2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k))) := by
    rw [heq]
    exact HasFDerivAt.fderiv hW
  rw [hF]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

theorem sbarDbar (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SbarDbarStatement n M := by
  intro z hz g hg x
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ 𝓝 (z x) := e0.open_target.mem_nhds hy0
  have hcd : ContDiffAt ℝ 2 (g ∘ e0.symm) (z x) := by
    have := (hg e0 he0).contDiffAt hnb
    simpa using this
  have hd : DifferentiableAt ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) :=
    (hcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym : ∀ v w : V n, fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (g ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcd.isSymmSndFDerivAt (by simp) v w
      | exact hcd.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc : ∀ k : Fin n,
      ((fun y => db n z k g y) ∘ e0.symm) =ᶠ[𝓝 (z x)] wdb n k (g ∘ e0.symm) := by
    intro k
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 k g _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  funext j k
  show db n z j (fun y => db n z k g y) x - db n z k (fun y => db n z j g y) x = 0
  rw [db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0, db_eq_wdb_comp_chart_symm z e0 he0 k _ x hx0]
  unfold wdb
  rw [(hloc k).fderiv_eq, (hloc j).fderiv_eq,
    fderiv_wdb_apply_eq k _ _ hd (bas n j), fderiv_wdb_apply_eq k _ _ hd (Complex.I • bas n j),
    fderiv_wdb_apply_eq j _ _ hd (bas n k), fderiv_wdb_apply_eq j _ _ hd (Complex.I • bas n k),
    hsym (bas n k) (bas n j), hsym (bas n k) (Complex.I • bas n j),
    hsym (Complex.I • bas n k) (bas n j), hsym (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.F
end

