module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtWeak
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDisjointMeetsComponents
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem exists_preconnected_infinite_nhds {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hn : 1 ≤ n) (e : OpenPartialHomeomorph Y (V n)) (x : Y) (hx : x ∈ e.source) :
    ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ B.Infinite := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩
  · have h := e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)
    rwa [e.left_inv hx] at h
  · exact (convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · refine Set.Infinite.image (e.symm.injOn.mono hsub) ?_
    haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)
    exact infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)

theorem exists_finite_disjoint_meets_components :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn S hS
  have h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S := by
    intro x
    obtain ⟨B, hB, hc, hi⟩ :=
      exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)
    obtain ⟨P, hP, hPS⟩ := (hi.diff hS).nonempty
    exact ⟨B, hB, hc, P, hP, hPS⟩
  choose B hB hc P hP hPS using h1
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)
  refine ⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact hPS x
  · intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloAeEq
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2LimitHolomorphic

open Set

variable {n : ℕ}

theorem exists_pos_le_on_compact {W K : Set (V n)} {ρ : V n → ℝ} (hρ : ContinuousOn ρ W)
    (hpos : ∀ v ∈ W, 0 < ρ v) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ ρ v := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hρ.mono hKW)
  exact ⟨ρ x, hpos x (hKW hx), fun v hv => hmin hv⟩

theorem lintegral_sq_le {W K : Set (V n)} {ρ : V n → ℝ} {c : ℝ} (hc : 0 < c)
    (hK : MeasurableSet K) (hKW : K ⊆ W) (hcK : ∀ v ∈ K, c ≤ ρ v) (g : V n → ℂ) :
    ∫⁻ v in K, ‖g v‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in W, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
  calc ∫⁻ v in K, ‖g v‖ₑ ^ 2
      ≤ ∫⁻ v in K, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
        apply setLIntegral_mono' hK
        intro v hv
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ c⁻¹ * ρ v := by
          rw [le_inv_mul_iff₀ hc]; simpa using hcK v hv
        have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖g v‖)
        nlinarith
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ v in K, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr

theorem integrableOn_of_limit {W K : Set (V n)} {ρ : V n → ℝ} {u : ℕ → V n → ℂ}
    {f : V n → ℂ} (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v)
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    (hK : IsCompact K) (hKW : K ⊆ W) : IntegrableOn f K := by
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_on_compact hρ hpos hK hKW
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hum : IntegrableOn (u m) K := ((hu m).continuousOn.mono hKW).integrableOn_compact hK
  have hfK : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.mono_measure (Measure.restrict_mono hKW le_rfl)).aestronglyMeasurable
  have hfin : ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_sq_le hc hK.measurableSet hKW hcK (fun v => f v - u m v))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm.trans ENNReal.one_lt_top))
  have hd : IntegrableOn (fun v => f v - u m v) K := by
    refine ⟨hfK.sub hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ v in K, ‖f v - u m v‖ₑ < ⊤
    have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
      intro x
      rcases le_total x 1 with h | h
      · exact h.trans le_self_add
      · calc x = x * 1 := (mul_one x).symm
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := (sq x).symm
          _ ≤ 1 + x ^ 2 := le_add_self
    calc ∫⁻ v in K, ‖f v - u m v‖ₑ ≤ ∫⁻ v in K, (1 + ‖f v - u m v‖ₑ ^ 2) :=
          lintegral_mono fun v => hpt _
      _ = volume K + ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hfin⟩
  exact (hd.add hum).congr_fun (fun v _ => by simp) hK.measurableSet

theorem enorm_integral_mul_le {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {d h : V n → ℂ}
    (hd : AEMeasurable d (volume.restrict W)) (hh : Continuous h) :
    ‖∫ v in W, d v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
  have hρm : AEMeasurable ρ (volume.restrict W) := hρ.aemeasurable hW.measurableSet
  have hsq : AEMeasurable (fun v => Real.sqrt (ρ v)) (volume.restrict W) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hρm
  have ham : AEMeasurable (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)))
      (volume.restrict W) := (hd.norm.mul hsq).ennreal_ofReal
  have hbm : AEMeasurable (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)))
      (volume.restrict W) := (hh.measurable.norm.aemeasurable.div hsq).ennreal_ofReal
  have hab : EqOn (fun v => ‖d v * h v‖ₑ)
      ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
        fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) W := by
    intro v hv
    have hs : 0 < Real.sqrt (ρ v) := Real.sqrt_pos.2 (hpos v hv)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_mul]
    congr 1
    field_simp
  have ha2 : EqOn (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      Real.sq_sqrt (hpos v hv).le]
  have hb2 : EqOn (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, div_pow,
      Real.sq_sqrt (hpos v hv).le]
  calc ‖∫ v in W, d v * h v‖ₑ ≤ ∫⁻ v in W, ‖d v * h v‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ v in W, ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
          fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) v :=
        setLIntegral_congr_fun hW.measurableSet hab
    _ ≤ (∫⁻ v in W, ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ v in W, ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two ham hbm
    _ = _ := by
        rw [setLIntegral_congr_fun hW.measurableSet ha2,
          setLIntegral_congr_fun hW.measurableSet hb2]

theorem integral_mul_eq_zero {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {u : ℕ → V n → ℂ} {f : V n → ℂ}
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    {h : V n → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h) (hsupp : tsupport h ⊆ W)
    (h0 : ∀ m, ∫ v in W, u m v * h v = 0) : ∫ v in W, f v * h v = 0 := by
  have hkc : Continuous fun v => ‖h v‖ ^ 2 / ρ v := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hhc.norm.pow 2).continuousAt.div (hρ.continuousAt (hW.mem_nhds hx))
        (hpos x hx).ne'
    · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
      have hev : (fun v => ‖h v‖ ^ 2 / ρ v) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with v hv
        simp [hv]
      exact continuousAt_const.congr hev.symm
  have hks : HasCompactSupport fun v => ‖h v‖ ^ 2 / ρ v := by
    refine hhs.mono fun x hx => ?_
    intro h1
    apply hx
    simp [h1]
  have hH : ∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (hkc.integrable_of_hasCompactSupport hks).lintegral_lt_top
  by_cases hfi : Integrable (fun v => f v * h v) (volume.restrict W)
  swap
  · exact integral_undef hfi
  have key : ∀ m, ‖∫ v in W, f v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
    intro m
    have hUi : Integrable (fun v => u m v * h v) (volume.restrict W) := by
      have h1 : IntegrableOn (fun v => u m v * h v) (tsupport h) :=
        (((hu m).continuousOn.mono hsupp).mul hhc.continuousOn).integrableOn_compact hhs
      exact h1.of_forall_sdiff_eq_zero hW.measurableSet fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2]
    have heq : ∫ v in W, f v * h v = ∫ v in W, (f v - u m v) * h v := by
      simp_rw [sub_mul]
      rw [integral_sub hfi hUi, h0 m, sub_zero]
    rw [heq]
    exact enorm_integral_mul_le hW hρ hpos
      (hf.sub ((hu m).continuousOn.aemeasurable hW.measurableSet)) hhc
  have hT : Tendsto (fun m =>
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m =>
        (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1
      (b := (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hH.ne))
    simpa using this
  have hle := ge_of_tendsto' hT key
  exact enorm_eq_zero.mp (le_antisymm hle bot_le)

theorem tsupport_dbarDir_subset (g : V n → ℂ) (w : V n) :
    tsupport (fun z => C.dbarDir g z w) ⊆ tsupport g := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  refine Function.mem_support.2 fun h0 => Function.mem_support.1 hz ?_
  simp [C.dbarDir, h0]

theorem exists_holo_ae_eq : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  intro n W ρ u f hW hρ hpos hu hf hlim
  have hwh : C.WeakHolo W f := by
    refine ⟨(locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK =>
      integrableOn_of_limit hρ hpos hu hf hlim hK hKW, ?_⟩
    intro g hg w
    obtain ⟨hhc, hhs⟩ := C.dbarDir_continuous_hasCompactSupport hg.1 hg.2.1 w
    exact integral_mul_eq_zero hW hρ hpos hu hf hlim hhc hhs
      ((tsupport_dbarDir_subset g w).trans hg.2.2)
      (fun m => (C.holoWeak n W (u m) hW (hu m)).2 g hg w)
  obtain ⟨U, hU, hfU⟩ := C.reg n W f hW hwh
  exact ⟨U, hU, hfU.symm⟩

end GlobalTheory.L2LimitHolomorphic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloQuadraticAddLeviIsLittleO
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.TaylorLevi

theorem taylor_two {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (p : E)
    (hφ : ContDiffAt ℝ 2 φ p) :
    (fun v => φ v - φ p - fderiv ℝ φ p (v - p) - fderiv ℝ (fderiv ℝ φ) p (v - p) (v - p) / 2)
      =o[𝓝 p] (fun v => ‖v - p‖ ^ 2) := by
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  have hB : HasFDerivAt (fderiv ℝ φ) B p :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : ∀ u w, B u w = B w u := fun u w =>
    (hφ.isSymmSndFDerivAt (by simp)) u w
  have hdiff := eventually_differentiableAt_of_contDiffAt hφ
  have hlo := hB.isLittleO
  set g : E → ℝ := fun w => φ w - D (w - p) - 1 / 2 * B (w - p) (w - p)
  have hg : ∀ w, DifferentiableAt ℝ φ w → HasFDerivAt g (fderiv ℝ φ w - D - B (w - p)) w := by
    intro w hw
    have h1 : HasFDerivAt (fun x : E => x - p) (ContinuousLinearMap.id ℝ E) w :=
      (hasFDerivAt_id w).sub_const p
    have h2 : HasFDerivAt (fun y => B (y - p) (y - p)) _ w := B.hasFDerivAt_of_bilinear h1 h1
    have h3 := (hw.hasFDerivAt.sub (D.hasFDerivAt.comp w h1)).sub (HasFDerivAt.const_mul h2 (1 / 2 : ℝ))
    refine h3.congr_fderiv ?_
    ext u
    simp
    rw [hsymm u w, hsymm u p]
    ring
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h4 := (Asymptotics.isLittleO_iff.1 hlo) hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h4.and hdiff)
  filter_upwards [Metric.ball_mem_nhds p hδ] with v hv
  have hsub : closedBall p ‖v - p‖ ⊆ ball p δ := by
    apply closedBall_subset_ball
    rw [← dist_eq_norm]; exact mem_ball.1 hv
  have hmvt := (convex_closedBall p ‖v - p‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := g) (C := c * ‖v - p‖)
    (fun w hw => (hg w (hball w (hsub hw)).2).hasFDerivWithinAt)
    (fun w hw => by
      have hw' := hball w (hsub hw)
      have e1 : ‖fderiv ℝ φ w - D - B (w - p)‖ ≤ c * ‖w - p‖ := by
        simpa using hw'.1
      have e2 : ‖w - p‖ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      exact e1.trans (mul_le_mul_of_nonneg_left e2 hc.le))
    (mem_closedBall_self (norm_nonneg _)) (by rw [mem_closedBall, dist_eq_norm])
  have : g v - g p = φ v - φ p - D (v - p) - B (v - p) (v - p) / 2 := by
    simp only [g]; rw [sub_self]; simp; ring
  rw [this] at hmvt
  rw [norm_pow, norm_norm]
  calc _ ≤ c * ‖v - p‖ * ‖v - p‖ := hmvt
    _ = c * ‖v - p‖ ^ 2 := by ring

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

variable {n : ℕ}

noncomputable section

theorem rmVec_coord (h : V n) : rmVec (fun j => h j) = h := by
  ext i
  simp [rmVec, bas, PiLp.single_apply, Pi.single_apply]

def linCoef (D : V n →L[ℝ] ℝ) (j : Fin n) : ℂ :=
  (D (bas n j) : ℂ) - Complex.I * (D (Complex.I • bas n j) : ℂ)

def quadCoef (B : V n →L[ℝ] V n →L[ℝ] ℝ) (j k : Fin n) : ℂ :=
  ((B (bas n j) (bas n k) - B (Complex.I • bas n j) (Complex.I • bas n k) : ℝ) : ℂ)
    - Complex.I * ((B (Complex.I • bas n j) (bas n k) + B (bas n j) (Complex.I • bas n k) : ℝ) : ℂ)

theorem lin_re (D : V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, linCoef D j * ξ j).re = D (rmVec ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rmVec, map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rm_cplx_smul_eq]
  simp [linCoef, Complex.mul_re]
  ring

theorem quad_re (B : V n →L[ℝ] V n →L[ℝ] ℝ) (ξ : Fin n → ℂ) :
    (∑ j, ∑ k, quadCoef B j k * ξ j * ξ k).re =
      B (rmVec ξ) (rmVec ξ) - B (Complex.I • rmVec ξ) (Complex.I • rmVec ξ) := by
  rw [rm_I_smul_vec, rmVec, rm_bil_sum, rm_bil_sum, Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rm_bil_expand B (ξ j) (ξ k), rm_bil_expand B (Complex.I * ξ j) (Complex.I * ξ k)]
  simp [quadCoef, Complex.mul_re, Complex.mul_im]
  ring

end

end GlobalTheory.TaylorLevi

namespace GlobalTheory.TaylorLevi

theorem exists_holo_quadratic_add_levi : ∀ (n : ℕ) (φ : V n → ℝ) (p : V n), ContDiffAt ℝ 2 φ p →
    ∃ q : V n → ℂ, Differentiable ℂ q ∧
      (fun v : V n => φ v - 2 * (q v).re
        - (leviV n (fun w => ((φ w : ℝ) : ℂ)) p (fun j => (v - p) j)).re)
        =o[𝓝 p] (fun v : V n => ‖v - p‖ ^ 2) := by
  intro n φ p hφ
  set D := fderiv ℝ φ p
  set B := fderiv ℝ (fderiv ℝ φ) p
  refine ⟨fun v => (φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
      + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8, ?_, ?_⟩
  · have hc : ∀ j, Differentiable ℂ (fun v : V n => (v - p) j) := fun j =>
      (EuclideanSpace.proj j : V n →L[ℂ] ℂ).differentiable.comp (differentiable_id.sub_const p)
    fun_prop
  · refine (taylor_two φ p hφ).congr' ?_ (EventuallyEq.refl _ _)
    filter_upwards with v
    have hL := rm_levi_re_ofReal φ p hφ (fun j => (v - p) j)
    have hA := lin_re D (fun j => (v - p) j)
    have hQ := quad_re B (fun j => (v - p) j)
    rw [rmVec_coord] at hL hA hQ
    have hq : ((φ p : ℂ) / 2 + (∑ j, linCoef D j * (v - p) j) / 2
        + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k) / 8).re
        = φ p / 2 + (∑ j, linCoef D j * (v - p) j).re / 2
          + (∑ j, ∑ k, quadCoef B j k * (v - p) j * (v - p) k).re / 8 := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.ofReal_re]
    rw [hq, hA, hQ]
    linarith

end GlobalTheory.TaylorLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombSectionsNeZeroOnFinset
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LinComb


open Polynomial in
theorem exists_pow_ne_zero {Y : Type} (N : ℕ) (T : Finset Y) (v : Y → Fin N → ℂ)
    (hv : ∀ P ∈ T, v P ≠ 0) : ∃ x : ℂ, ∀ P ∈ T, ∑ k : Fin N, x ^ (k : ℕ) * v P k ≠ 0 := by
  classical
  let q : Y → ℂ[X] := fun P => ∑ k : Fin N, C (v P k) * X ^ (k : ℕ)
  have hcoeff : ∀ P (k : Fin N), (q P).coeff k = v P k := by
    intro P k
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
    simp
  have hq : ∀ P ∈ T, q P ≠ 0 := by
    intro P hP h0
    apply hv P hP
    funext k
    have := hcoeff P k
    rw [h0, coeff_zero] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (T.biUnion fun P => (q P).roots.toFinset)
  refine ⟨x, fun P hP h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨P, hP, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (hq P hP), IsRoot.def]
  simp only [q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.OTY.LinComb

theorem GlobalTheory.OTY.exists_linComb_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ ι La _ A L N s T hs hT
  classical
  obtain ⟨x, hx⟩ := GlobalTheory.OTY.LinComb.exists_pow_ne_zero N T (fun P k => s k (A.pick P) P) (by
    intro P hP h0
    apply hT P hP
    intro k
    exact congrFun h0 k)
  refine ⟨fun i y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y, ⟨?_, ?_⟩, fun P hP => hx P hP, ?_⟩
  · intro i
    have : ((fun y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y) ∘ (A.chart i).symm)
        = ∑ k : Fin N, (fun v => x ^ (k : ℕ) * (s k i ∘ (A.chart i).symm) v) := by
      funext v; simp [Finset.sum_apply]
    rw [this]
    exact DifferentiableOn.sum fun k _ => ((hs k).1 i).const_mul _
  · intro i j y hy hi hj
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hs k).2 i j y hy hi hj]
    ring
  · refine ⟨1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2, by positivity, fun y => ?_⟩
    simp only [WeightedAtlas.nsq, WeightedAtlas.sqn]
    rw [← Finset.sum_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ≤ ∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => norm_mul _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin N => ‖x ^ (k : ℕ)‖)
      (fun k => ‖s k (A.pick y) y‖)
    have h3 : 0 ≤ ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by positivity
    calc ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ^ 2
        ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖) ^ 2 := by gcongr
      _ ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := h2
      _ ≤ (1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by
        gcongr; linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHomToStrictlyHenselianNormalStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (i : A →+* T), IsLocalHom i →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : HenselianLocalRing A')
      (_ : IsSepClosed (ResidueField A')) (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (ι : A →+* A') (α : A' →+* T), α.comp ι = i ∧ IsLocalHom α := by
  first | (exact @GlobalTheory.exists_strictlyHenselian_normal_between) | (exact GlobalTheory.exists_strictlyHenselian_normal_between) | (intros; apply GlobalTheory.exists_strictlyHenselian_normal_between  <;> assumption)
end

