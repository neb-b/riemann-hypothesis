module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
public import Lemmata.MiscLemmasF.Imports
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeak
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem holoWeak_bound {n : ℕ} {Ω K : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hu : DifferentiableOn ℂ u Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (v : V n) :
    ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ u x v‖ ≤ C := by
  first | exact Bl.SecondBlockLemmaG.goal1 .. | (apply Bl.SecondBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaG.goal1 <;> assumption)

theorem holoWeak : HoloWeakStatement := by
  intro n Ω u hΩ hu
  refine ⟨hu.continuousOn.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro g hg v
  obtain ⟨hgs, hgc, hgΩ⟩ := hg
  have hK : IsCompact (tsupport g) := hgc
  have huK : ContinuousOn u (tsupport g) := hu.continuousOn.mono hgΩ
  have hg1 : ContDiff ℝ 1 g := hgs.of_le (by exact_mod_cast le_top)
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hg'c : ∀ w : V n, Continuous fun x => fderiv ℝ g x w := fun w =>
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hzero : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hzero' : ∀ w x, x ∉ tsupport g → fderiv ℝ g x w = 0 := fun w x hx => by
    rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
  have hint : ∀ h : V n → ℂ, Continuous h → (∀ x, x ∉ tsupport g → h x = 0) →
      Integrable (fun x => u x * h x) := by
    intro h hh hh0
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport g) ?_ ?_
    · exact (huK.mul hh.continuousOn).integrableOn_compact hK
    · intro x hx; simp [hh0 x hx]
  have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hibp : ∀ w : V n, ∫ x, u x * fderiv ℝ g x w = - ∫ x, fderiv ℝ u x w * g x := by
    intro w
    obtain ⟨C, hC⟩ := holoWeak_bound hΩ hu hK hgΩ w
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · refine Integrable.mono' (hgi.norm.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
      · exact (measurable_fderiv_apply_const ℝ u w).aestronglyMeasurable.mul
          hgs.continuous.aestronglyMeasurable
      · by_cases hx : x ∈ tsupport g
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
        · simp [hzero x hx]
    · exact hint _ (hg'c w) (hzero' w)
    · exact hint _ hgs.continuous hzero
    · intro x hx
      exact ((hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))).restrictScalars ℝ
    · intro x _
      exact hgd x
  have hlin : ∀ x, fderiv ℝ u x (I • v) * g x = I * (fderiv ℝ u x v * g x) := by
    intro x
    by_cases hx : x ∈ tsupport g
    · have hux : DifferentiableAt ℂ u x :=
        (hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))
      rw [hux.fderiv_restrictScalars (𝕜 := ℝ)]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
      ring
    · simp [hzero x hx]
  have hΩ0 : ∀ x, x ∉ Ω → u x * dbarDir g x v = 0 := by
    intro x hx
    have hx' : x ∉ tsupport g := fun h => hx (hgΩ h)
    simp [dbarDir, fderiv_of_notMem_tsupport ℝ hx']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hΩ0]
  have e1 : (fun x => u x * dbarDir g x v) =
      fun x => u x * fderiv ℝ g x (I • v) - I * (u x * fderiv ℝ g x v) := by
    funext x; simp only [dbarDir]; ring
  rw [e1, integral_sub (hint _ (hg'c _) (hzero' _)) ((hint _ (hg'c _) (hzero' _)).const_mul I),
    integral_const_mul, hibp (I • v), hibp v]
  simp only [hlin]
  rw [integral_const_mul]
  ring

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def rotAbout {n : ℕ} (c : V n) (a : ℂ) (z : V n) : V n := c + a • (z - c)

theorem rotAbout_sub {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (z : V n) :
    ‖rotAbout c a z - c‖ = ‖z - c‖ := by
  simp [rotAbout, norm_smul, ha]

theorem rotAbout_mem_ball_iff {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) (z : V n) :
    rotAbout c a z ∈ ball c R ↔ z ∈ ball c R := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, rotAbout_sub c ha]

theorem measurePreserving_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurePreserving (rotAbout c a) volume volume :=
  (measurePreserving_add_left volume c).comp
    ((measurePreserving_smul_unit a ha).comp (measurePreserving_sub_right volume c))

theorem measurableEmbedding_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) :
    MeasurableEmbedding (rotAbout c a) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  let h : V n ≃ₜ V n :=
    { toFun := rotAbout c a
      invFun := fun z => c + a⁻¹ • (z - c)
      left_inv := fun z => by simp [rotAbout, smul_smul, inv_mul_cancel₀ ha0]
      right_inv := fun z => by simp [rotAbout, smul_smul, mul_inv_cancel₀ ha0]
      continuous_toFun := by unfold rotAbout; fun_prop
      continuous_invFun := by fun_prop }
  exact h.measurableEmbedding

theorem indicator_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ) {β : Type*}
    [Zero β] (g : V n → β) (z : V n) :
    (ball c R).indicator (fun z => g (rotAbout c a z)) z =
      (ball c R).indicator g (rotAbout c a z) := by
  by_cases hz : z ∈ ball c R
  · rw [indicator_of_mem hz, indicator_of_mem ((rotAbout_mem_ball_iff c ha R z).2 hz)]
  · rw [indicator_of_notMem hz,
      indicator_of_notMem (fun h => hz ((rotAbout_mem_ball_iff c ha R z).1 h))]

theorem setLIntegral_rotAbout {n : ℕ} (c : V n) {a : ℂ} (ha : ‖a‖ = 1) (R : ℝ)
    (g : V n → ℝ≥0∞) :
    ∫⁻ z in ball c R, g (rotAbout c a z) = ∫⁻ z in ball c R, g z := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    lintegral_congr fun z => indicator_rotAbout c ha R g z]
  exact (measurePreserving_rotAbout c ha).lintegral_comp_emb (measurableEmbedding_rotAbout c ha) _

theorem norm_exp_mul_I_eq_one (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem continuous_rotAbout_exp {n : ℕ} (c : V n) :
    Continuous (fun p : ℝ × V n => rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) := by
  unfold rotAbout; fun_prop

theorem continuousOn_comp_rotAbout {n : ℕ} {c : V n} {R : ℝ} {u : V n → ℂ}
    (hu : DifferentiableOn ℂ u (ball c R)) (s : Set ℝ) :
    ContinuousOn (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
      (s ×ˢ ball c R) := by
  refine hu.continuousOn.comp (continuous_rotAbout_exp c).continuousOn ?_
  rintro ⟨θ, z⟩ ⟨_, hz⟩
  exact (rotAbout_mem_ball_iff c (norm_exp_mul_I_eq_one θ) R z).2 hz

theorem mv : MVStatement := by
  intro n c R u r hu hr
  have hT1 := norm_exp_mul_I_eq_one
  have hrot : ∀ θ : ℝ, ∫⁻ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ =
        ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖ := by
    intro θ
    have h := setLIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z‖ₑ ^ 2 * r ‖z - c‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hmeas : AEMeasurable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    rw [Measure.prod_restrict]
    have h1 := ((continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aemeasurable
      (μ := volume.prod volume) (measurableSet_Ioc.prod measurableSet_ball)).enorm.pow_const 2
    have h2 : Measurable fun p : ℝ × V n => r ‖p.2 - c‖ :=
      hr.comp ((measurable_snd.sub_const c).norm)
    exact h1.mul h2.aemeasurable
  have hvol : volume (Ioc (0 : ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioc, sub_zero]
  have key : (∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi) =
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← hvol, ← setLIntegral_const, ← lintegral_lintegral_swap hmeas]
    exact lintegral_congr fun θ => (hrot θ).symm
  have hmr : Measurable fun z : V n => r ‖z - c‖ := hr.comp (measurable_id.sub_const c).norm
  have low : ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ ≤
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← lintegral_const_mul _ hmr]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcz : Continuous fun θ : ℝ => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) :=
      hu.continuousOn.comp_continuous (by unfold rotAbout; fun_prop)
        (fun θ => (rotAbout_mem_ball_iff c (hT1 θ) R z).2 hz)
    have hm : Measurable fun θ : ℝ =>
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 :=
      hcz.measurable.enorm.pow_const 2
    rw [lintegral_mul_const _ hm]
    gcongr
    exact circle_mean_sq hu hw
  have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  refine (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 ?_
  calc ‖u c‖ₑ ^ 2 * (∫⁻ z in ball c R, r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi)
      = ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ := by ring
    _ ≤ _ := low
    _ = _ := key.symm

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollLeClosedBall
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem moll_le_closedBall (n : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x z : V n,
      moll n t z ≤ C / volume.real (closedBall x t) := by
  obtain ⟨C, hC⟩ := moll_le n
  refine ⟨C, fun t ht x z => ?_⟩
  have hvol : volume.real (closedBall x t) = volume.real (ball (0 : V n) t) := by
    rcases subsingleton_or_nontrivial (V n) with hV | hV
    · have h1 : closedBall x t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y x]; exact mem_closedBall_self ht.le
      have h2 : ball (0 : V n) t = univ := eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y 0]; exact mem_ball_self ht
      rw [h1, h2]
    · simp only [measureReal_def]
      rw [Measure.addHaar_closedBall_eq_addHaar_ball, Measure.addHaar_ball_center]
  rw [hvol]
  exact hC t ht z

theorem mollify_tendsto_ae {n : ℕ} {u : V n → ℂ} (hu : Integrable u) :
    ∀ᵐ x, Tendsto (fun t => mollify n t u x) (𝓝[>] 0) (𝓝 (u x)) := by
  obtain ⟨C, hC⟩ := moll_le_closedBall n
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (μ := volume)
    hu.locallyIntegrable 1] with x hx
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hav : Tendsto (fun t : ℝ => ⨍ y in closedBall x t, ‖u y - u x‖) (𝓝[>] 0) (𝓝 0) :=
    hx (l := 𝓝[>] (0 : ℝ)) (fun _ => x) id tendsto_id (by
      filter_upwards [hpos] with t ht
      exact mem_closedBall_self (by simp only [id, one_mul]; exact ht.le))
  have hg : Tendsto (fun t : ℝ => ∫ y, moll n t (x - y)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with t ht
    show (1 : ℝ) = ∫ y, moll n t (x - y)
    rw [integral_sub_left_eq_self (moll n t) volume x, moll_integral n ht]
  have hsupp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Function.support (fun y => moll n t (x - y)) ⊆ closedBall x t := by
    filter_upwards [hpos] with t ht
    intro y hy
    have h := moll_tsupport n ht (subset_tsupport (moll n t) (show x - y ∈ Function.support (moll n t) from hy))
    rw [mem_closedBall, dist_zero_right] at h
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    linarith
  have hbd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y, |moll n t (x - y)| ≤ C / volume.real (closedBall x t) := by
    filter_upwards [hpos] with t ht
    intro y
    rw [abs_of_nonneg (moll_nonneg _ _ _)]
    exact hC t ht x _
  have key := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
    (a := fun t => closedBall x t) (g := fun t y => moll n t (x - y)) C hav
    (Eventually.of_forall fun _ => hu.integrableOn) hg hsupp hbd
  refine key.congr (fun t => ?_)
  simp only [mollify, Complex.real_smul]

end ReciprocityTheory.L2DbarEstimates.C
end

-- bundled from ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegConv
section
namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

noncomputable def smulFlip : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).flip

theorem smulFlip_apply (a : ℂ) (r : ℝ) : smulFlip a r = (r : ℂ) * a := by
  simp only [smulFlip, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
    Complex.real_smul]

theorem mollify_eq_convolution_smulFlip (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = convolution u (moll n t) smulFlip volume := by
  ext x
  simp only [mollify, convolution_def, smulFlip_apply]

theorem moll_contDiff_one (n : ℕ) (t : ℝ) : ContDiff ℝ 1 (moll n t) := (moll_contDiff n t).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))

theorem moll_sub_eq_zero {n : ℕ} {t : ℝ} (ht : 0 < t) {x y : V n}
    (hy : y ∉ closedBall x (t / 2)) : moll n t (x - y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  apply hy
  have := moll_tsupport n ht h
  rw [mem_closedBall, dist_zero_right] at this
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
  exact this

theorem isTest_moll_sub {n : ℕ} {Ω : Set (V n)} {t : ℝ} {x : V n} (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) : IsTest Ω (fun y => ((moll n t (x - y) : ℝ) : ℂ)) := by
  have hz : ∀ y ∉ closedBall x (t / 2), ((moll n t (x - y) : ℝ) : ℂ) = 0 := fun y hy => by
    rw [moll_sub_eq_zero ht hy, Complex.ofReal_zero]
  refine ⟨?_, HasCompactSupport.intro (isCompact_closedBall x (t / 2)) hz, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((moll_contDiff n t).comp (contDiff_const.sub contDiff_id))
  · exact (closure_minimal (Function.support_subset_iff'.2 hz) isClosed_closedBall).trans
      ((closedBall_subset_closedBall (by linarith)).trans hx)

theorem fderiv_moll_sub {n : ℕ} {t : ℝ} (x y w : V n) :
    fderiv ℝ (fun y => ((moll n t (x - y) : ℝ) : ℂ)) y w
      = -((fderiv ℝ (moll n t) (x - y) w : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ (moll n t) (x - y) :=
    (moll_contDiff_one n t).differentiable one_ne_zero (x - y)
  have h1 : HasFDerivAt (fun y : V n => x - y) (-ContinuousLinearMap.id ℝ (V n)) y :=
    (hasFDerivAt_id y).const_sub x
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp y (hd.hasFDerivAt.comp y h1)
  rw [show (fun y => ((moll n t (x - y) : ℝ) : ℂ)) =
    Complex.ofRealCLM ∘ (moll n t ∘ fun y => x - y) from rfl, h2.fderiv]
  simp

theorem differentiableAt_of_fderiv_I {n : ℕ} {f : V n → ℂ} {x : V n}
    (hf : DifferentiableAt ℝ f x)
    (h : ∀ v, fderiv ℝ f x (I • v) = I * fderiv ℝ f x v) : DifferentiableAt ℂ f x := by
  have hsmul : ∀ (c : ℂ) (v : V n), fderiv ℝ f x (c • v) = c * fderiv ℝ f x v := by
    intro c v
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
    rw [map_add (f := _), map_smul, map_smul, h, Complex.real_smul, Complex.real_smul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let g' : V n →L[ℂ] ℂ :=
    ⟨⟨⟨fderiv ℝ f x, (fderiv ℝ f x).map_add⟩, fun c v => by simpa using hsmul c v⟩,
      (fderiv ℝ f x).continuous⟩
  exact (differentiableAt_iff_restrictScalars ℝ hf).2 ⟨g', ContinuousLinearMap.ext fun _ => rfl⟩

theorem mollify_differentiableAt {n : ℕ} {Ω : Set (V n)} {u : V n → ℂ} {t : ℝ} {x : V n}
    (hΩ : IsOpen Ω) (hu : Integrable u) (hw : WeakHolo Ω u) (ht : 0 < t)
    (hx : closedBall x t ⊆ Ω) :
    DifferentiableAt ℂ (mollify n t u) x := by
  have hcs := moll_hasCompactSupport n ht
  have hc1 := moll_contDiff_one n t
  have hli : LocallyIntegrable u volume := hu.locallyIntegrable
  have hD := hcs.hasFDerivAt_convolution_right (L := smulFlip) hli hc1 x
  have hcont : ∀ v, Continuous (fun a => fderiv ℝ (moll n t) a v) := fun v =>
    (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ v, Integrable (fun s => ((fderiv ℝ (moll n t) (x - s) v : ℝ) : ℂ) * u s) := by
    intro v
    have := (((hcs.fderiv_apply (𝕜 := ℝ) v).convolutionExists_right smulFlip hli (hcont v)) x)
    simpa [ConvolutionExistsAt, smulFlip_apply] using this
  rw [mollify_eq_convolution_smulFlip]
  apply differentiableAt_of_fderiv_I hD.differentiableAt
  intro w
  rw [hD.fderiv, convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero),
    convolution_precompR_apply smulFlip hli (hcs.fderiv (𝕜 := ℝ)) (hc1.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, smulFlip_apply]

  have h0 := hw.2 (fun y => ((moll n t (x - y) : ℝ) : ℂ)) (isTest_moll_sub ht hx) w
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at h0
  · simp only [dbarDir, fderiv_moll_sub] at h0
    have hsplit : ∫ z, u z * (-((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) -
        I * -((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ)) =
        I * (∫ z, ((fderiv ℝ (moll n t) (x - z) w : ℝ) : ℂ) * u z) -
          ∫ z, ((fderiv ℝ (moll n t) (x - z) (I • w) : ℝ) : ℂ) * u z := by
      rw [← integral_const_mul, ← integral_sub ((hint w).const_mul I) (hint (I • w))]
      congr 1
      ext z
      ring
    rw [hsplit] at h0
    linear_combination -h0
  · intro z hz
    have hxz : x - z ∉ tsupport (moll n t) := fun h => hz (hx (by
      have := moll_tsupport n ht h
      rw [mem_closedBall, dist_zero_right] at this
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      linarith))
    have h0 : fderiv ℝ (moll n t) (x - z) = 0 := by
      by_contra hne
      exact hxz (support_fderiv_subset ℝ (Function.mem_support.2 hne))
    simp [dbarDir, fderiv_moll_sub, h0]

end ReciprocityTheory.L2DbarEstimates.C
end

