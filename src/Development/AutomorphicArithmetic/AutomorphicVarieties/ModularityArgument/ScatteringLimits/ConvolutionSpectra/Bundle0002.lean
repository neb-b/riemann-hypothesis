module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.AeIntegral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvApprox
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avApprox :
    (∀ a b : ℝ, a < b → ∃ ψ, Bump ψ a b) ∧ (∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a)) ∧
      ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (h : H) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ ψ a b, Bump ψ a b → -δ ≤ a → b ≤ δ → ‖F.av (fun t => (ψ t : ℂ)) h - h‖ ≤ ε := by
  have two : ∀ ψ a b, Bump ψ a b → HasCompactSupport ψ ∧ Integrable (fun t => (ψ t : ℂ)) ∧ ∫ t, ψ t ^ 2 ≤ 2 / (b - a) := by
    intro ψ a b h
    have hs : HasCompactSupport ψ := HasCompactSupport.intro isCompact_Icc h.supp
    have hi : Integrable ψ := h.cont.integrable_of_hasCompactSupport hs
    refine ⟨hs, hi.ofReal, ?_⟩
    have : ∫ t, ψ t ^ 2 ≤ ∫ t, 2 / (b - a) * ψ t :=
      integral_mono_of_nonneg (Eventually.of_forall fun t => sq_nonneg _) (hi.const_mul _)
        (Eventually.of_forall fun t => by show ψ t ^ 2 ≤ _; rw [sq]; exact mul_le_mul_of_nonneg_right (h.le t) (h.nonneg t))
    rwa [integral_const_mul, h.total, mul_one] at this
  refine ⟨fun a b hab => ?_, two, ?_⟩
  · have hd : 0 < b - a := sub_pos.2 hab
    let f : ℝ → ℝ := fun t => 6 / (b - a) ^ 3 * max 0 ((t - a) * (b - t))
    have hsupp : ∀ t, t ∉ Icc a b → f t = 0 := fun t ht => by
      have : (t - a) * (b - t) ≤ 0 := by
        rcases not_and_or.1 ht with h | h <;> push Not at h <;> nlinarith
      simp [f, max_eq_left this]
    refine ⟨f, by fun_prop, fun t => by positivity, fun t => ?_, hsupp, ?_⟩
    · have : max 0 ((t - a) * (b - t)) ≤ (b - a) ^ 2 / 4 := max_le (by positivity) (by nlinarith [sq_nonneg (a + b - 2 * t)])
      calc f t ≤ 6 / (b - a) ^ 3 * ((b - a) ^ 2 / 4) := by simp only [f]; gcongr
        _ = 3 / 2 / (b - a) := by field_simp; norm_num
        _ ≤ 2 / (b - a) := by gcongr; norm_num
    · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab.le]
      have : ∫ t in a..b, f t = ∫ t in a..b, 6 / (b - a) ^ 3 * (-t ^ 2 + (a + b) * t - a * b) := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hab.le] at ht
        simp only [f]
        rw [max_eq_right (mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2))]; ring
      rw [this, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub, intervalIntegral.integral_add,
        intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, integral_pow, integral_id, intervalIntegral.integral_const]
      · simp only [smul_eq_mul]; field_simp; ring
      all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro H _ _ _ F h ε hε
    obtain ⟨δ, hδ, H1⟩ := Metric.continuousAt_iff.1 ((F.cont h).continuousAt (x := 0)) ε hε
    refine ⟨δ / 2, by positivity, fun ψ a b hψ ha hb => ?_⟩
    obtain ⟨hs, hi, -⟩ := two ψ a b hψ
    obtain ⟨i, e⟩ := ((avSpec F).2.2.2 _ hi).1 h
    have hr : Integrable ψ := hψ.cont.integrable_of_hasCompactSupport hs
    have e2 : h = ∫ t, (ψ t : ℂ) • h := by rw [integral_smul_const, integral_complex_ofReal, hψ.total]; simp
    rw [e]
    conv_lhs => rw [show (∫ t, (ψ t : ℂ) • F.U t h) - h = (∫ t, (ψ t : ℂ) • F.U t h) - ∫ t, (ψ t : ℂ) • h from congrArg _ e2]
    rw [← integral_sub i (hi.smul_const h)]
    refine (norm_integral_le_of_norm_le (hr.mul_const ε) (Eventually.of_forall fun t => ?_)).trans_eq
      (by rw [integral_mul_const, hψ.total, one_mul])
    rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hψ.nonneg t)]
    by_cases ht : t ∈ Icc a b
    · have := H1 (x := t) (by rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      rw [F.zero, dist_eq_norm] at this
      exact mul_le_mul_of_nonneg_left this.le (hψ.nonneg t)
    · simp [hψ.supp t ht]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CobLaws
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cobLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), F.Cob 0 ∧ (∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') ∧ F.Cob (h - h')) ∧ (∀ (c : ℂ) h, F.Cob h → F.Cob (c • h)) ∧
      (∀ h, F.rev.Cob h ↔ F.Cob h) ∧ (∀ s h, F.Cob (h - F.U s h)) ∧ (∀ h, F.Cob h → ∃ C, ∀ t, ‖∫ s in (0 : ℝ)..t, F.U s h‖ ≤ C) ∧
      (F.Null → ∀ h h' (c : ℝ), F.Cob h → Tendsto (fun a => ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ) atTop (𝓝 0)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → ∀ h, F.Cob h → F'.Cob (Y h) := by
  intro H _ _ _ F
  have ii : ∀ h a b, IntervalIntegrable (fun s => F.U s h) volume a b := fun h a b => (F.cont h).intervalIntegrable a b
  have hs : ∀ (c : ℂ) h, F.Cob h → F.Cob (c • h) := fun c h ⟨k, hk⟩ =>
    ⟨c • k, fun t => by simp only [map_smul]; rw [intervalIntegral.integral_smul, hk, smul_sub]⟩
  have ha : ∀ h h', F.Cob h → F.Cob h' → F.Cob (h + h') := fun h h' ⟨k, hk⟩ ⟨k', hk'⟩ =>
    ⟨k + k', fun t => by simp only [map_add (f := _)]; rw [intervalIntegral.integral_add (ii _ _ _) (ii _ _ _), hk, hk']; abel⟩
  have hr : ∀ (F : Flow H) h, F.Cob h → F.rev.Cob h := fun F h ⟨k, hk⟩ => ⟨-k, fun t => by
    show ∫ s in (0 : ℝ)..t, F.U (-s) h = F.U (-t) (-k) - -k
    rw [intervalIntegral.integral_comp_neg fun s => F.U s h, neg_zero, intervalIntegral.integral_symm, hk, map_neg]; abel⟩
  refine ⟨⟨0, fun t => by simp⟩, fun h h' a b => ⟨ha _ _ a b, ?_⟩, hs, fun h => ⟨fun x => ?_, hr F h⟩, fun s h => ?_,
    fun h ⟨k, hk⟩ => ⟨‖k‖ + ‖k‖, fun t => ?_⟩, fun hn h h' c ⟨k, hk⟩ => ?_, ?_⟩
  · simpa [sub_eq_add_neg] using ha _ _ a (hs (-1) _ b)
  · obtain ⟨k, hk⟩ := hr F.rev h x
    exact ⟨k, fun t => by simpa [Flow.rev] using hk t⟩
  · refine ⟨-∫ r in (0 : ℝ)..s, F.U r h, fun t => ?_⟩
    simp only [map_sub, ← F.add]
    have hc : Continuous fun r => F.U (r + s) h := (F.cont h).comp (continuous_id.add continuous_const)
    rw [intervalIntegral.integral_sub (ii _ _ _) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_comp_add_right fun r => F.U r h, map_neg, ← (F.U t).intervalIntegral_comp_comm (ii _ _ _)]
    simp only [← F.add]
    rw [intervalIntegral.integral_comp_add_left fun r => F.U r h, zero_add, add_zero]
    have e1 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 t) (ii h t (t + s))
    have e2 := intervalIntegral.integral_add_adjacent_intervals (ii h 0 s) (ii h s (t + s))
    rw [eq_sub_of_add_eq e1, ← e2]; abel
  · rw [hk]; exact (norm_sub_le _ _).trans_eq (by rw [F.norm])
  · have e : ∀ a, ∫ s in (c - a)..(c + a), ⟪h', F.U s h⟫_ℂ = ⟪h', F.U (c + a) k⟫_ℂ - ⟪h', F.U (c - a) k⟫_ℂ := fun a => by
      have := (innerSL ℂ h').intervalIntegral_comp_comm (ii h (c - a) (c + a))
      simp only [innerSL_apply_apply] at this
      rw [this, ← intervalIntegral.integral_interval_sub_left (ii h 0 _) (ii h 0 _), hk, hk, ← inner_sub_right]
      congr 1; abel
    simp only [e]
    simpa [sub_eq_add_neg] using ((hn k h').1.comp (tendsto_atTop_add_const_left _ c tendsto_id)).add
      ((hn k h').2.comp (tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot)).neg
  · intro G _ _ _ F' Y hY h ⟨k, hk⟩
    exact ⟨Y k, fun t => by simp only [← hY]; rw [Y.intervalIntegral_comp_comm (ii _ _ _), hk, map_sub]⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.convSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, (∀ᵐ x : ℝ, conv κ u x = ∫ t : ℝ, κ t (u (x + t))) ∧
      Integrable (fun t => (κ t).compLpL 2 volume (sh V t u)) ∧ conv κ u = ∫ t, (κ t).compLpL 2 volume (sh V t u) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  let c : (V →L[ℂ] W) →L[ℂ] (L V →L[ℂ] L W) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A
  have hi : ∀ u : L V, Integrable (fun t => (κ t).compLpL 2 volume (sh V t u)) := fun u => by
    refine Continuous.integrable_of_hasCompactSupport ((c.continuous.comp hk.1).clm_apply ((shF V).cont u)) ?_
    refine hk.2.mono fun t ht h0 => ht ?_
    show c (κ t) (sh V t u) = 0
    rw [h0, map_zero, ContinuousLinearMap.zero_apply]
  have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let A : L V →ₗ[ℂ] L W :=
    { toFun := fun u => ∫ t, (κ t).compLpL 2 volume (sh V t u)
      map_add' := fun x y => by simp only [map_add (f := _)]; exact integral_add (hi x) (hi y)
      map_smul' := fun a x => by simp only [map_smul, RingHom.id_apply]; exact integral_smul a _ }
  have hb : ∀ u, ‖A u‖ ≤ (∫ t, ‖κ t‖) * ‖u‖ := fun u => by
    rw [← integral_mul_const]
    refine norm_integral_le_of_norm_le (hk1.norm.mul_const _) (Eventually.of_forall fun t => ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [show ‖sh V t u‖ = ‖u‖ from (shF V).norm t u]
    gcongr
    exact ContinuousLinearMap.norm_compLpL_le _
  have hae : ∀ u : L V, ∀ᵐ x : ℝ, (A u : L W) x = ∫ t : ℝ, κ t (u (x + t)) := fun u => by
    refine ae_integral volume _ (hi u) (fun p => κ p.1 (u (p.2 + p.1))) ?_ (Eventually.of_forall fun t => ?_)
    · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (u : ℝ → V) (p.2 + p.1)) (volume.prod volume) :=
        ((Lp.stronglyMeasurable u).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable
      exact (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable h1
    · filter_upwards [(κ t).coeFn_compLpL (sh V t u), sh_ae V t u] with x a b
      rw [a, b]
  have sp := Classical.epsilon_spec (p := fun C : L V →L[ℂ] L W => ∀ u, ∀ᵐ x : ℝ, C u x = ∫ t : ℝ, κ t (u (x + t)))
    ⟨A.mkContinuous _ hb, hae⟩
  refine fun u => ⟨sp u, hi u, Lp.ext ?_⟩
  filter_upwards [sp u, hae u] with x a b
  exact a.trans b.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutLaws :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s t : Set ℝ), MeasurableSet s → MeasurableSet t →
      cut V s ∘L cut V t = cut V (s ∩ t) ∧ IsSelfAdjoint (cut V s) ∧ (Disjoint s t → cut V (s ∪ t) = cut V s + cut V t) ∧ cut V univ = 1 ∧ cut V ∅ = 0 ∧
      (∀ u, ‖cut V s u‖ ≤ ‖u‖) ∧ (∀ a : ℝ, sh V a ∘L cut V s = cut V ((fun x => x + a) ⁻¹' s) ∘L sh V a) ∧
      (∀ u : L V, cut V s u = u ↔ ∀ᵐ x : ℝ, x ∉ s → u x = 0) ∧ ∀ u : L V, ‖cut V s u‖ ^ 2 = ∫ x in s, ‖u x‖ ^ 2 := by
  intro V _ _ _ _ s t hs ht
  have c := cutSpec (V := V)
  have nsq : ∀ u : L V, ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := fun u => by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner u u)]
    simp only [inner_self_eq_norm_sq]
  refine ⟨?_, ?_, fun hd => ?_, ?_, ?_, fun u => ?_, fun a => ?_, fun u => ?_, fun u => ?_⟩
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c s hs (cut V t u), c t ht u, c _ (hs.inter ht) u] with x h1 h2 h3
    rw [ContinuousLinearMap.comp_apply, h1, h3]
    by_cases a : x ∈ s <;> by_cases b : x ∈ t <;> simp [a, b, h2]
  · refine LinearMap.IsSymmetric.isSelfAdjoint fun u v => ?_
    simp only [ContinuousLinearMap.coe_coe, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [c s hs u, c s hs v] with x h1 h2
    rw [h1, h2]
    by_cases a : x ∈ s <;> simp [a]
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c s hs u, c t ht u, c _ (hs.union ht) u, Lp.coeFn_add (cut V s u) (cut V t u)] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.add_apply, h3, h4, Pi.add_apply, h1, h2, indicator_union_of_disjoint hd]
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c _ .univ u] with x h1
    rw [h1]; simp
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [c _ .empty u, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with x h1 h2
    rw [h1, ContinuousLinearMap.zero_apply, h2]; simp
  · refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [c s hs u] with x h
    rw [h]; exact norm_indicator_le_norm_self _ _
  · refine ContinuousLinearMap.ext fun u => Lp.ext ?_
    filter_upwards [sh_ae V a (cut V s u), (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (c s hs u),
      c _ (measurable_add_const a hs) (sh V a u), sh_ae V a u] with x h1 h2 h3 h4
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1, h2, h3]
    by_cases b : x + a ∈ s <;> simp [b, h4]
  · constructor
    · intro h
      filter_upwards [c s hs u] with x h1 hx
      rw [h] at h1
      rw [h1, indicator_of_notMem hx]
    · intro h
      refine Lp.ext ?_
      filter_upwards [c s hs u, h] with x h1 h2
      rw [h1]
      by_cases b : x ∈ s
      · simp [b]
      · simp [b, h2 b]
  · rw [nsq, ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [c s hs u] with x h
    rw [h]
    by_cases b : x ∈ s <;> simp [b]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResCob
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resCob :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H) (k : H), F.Cob (k - F.av wR k) ∧
      ∫ t in Iic (0 : ℝ), Real.exp t * ‖F.U t k - k‖ ^ 2 = 2 * ‖k‖ ^ 2 - 2 * (⟪k, F.av wR k⟫_ℂ).re := by
  intro H _ _ _ F k
  have hw := (avSpec F).2.1
  have sp := fun h => ((avSpec F).2.2.2 _ hw).1 h
  have cg : Continuous fun r : ℝ => (Real.exp r : ℂ) • F.U r k := by
    have := F.cont k
    fun_prop
  have ig : ∀ t, IntegrableOn (fun r : ℝ => (Real.exp r : ℂ) • F.U r k) (Iic t) := fun t =>
    Integrable.mono' ((integrableOn_exp_Iic t).mul_const ‖k‖) cg.aestronglyMeasurable
      (Eventually.of_forall fun r => by simp [norm_smul, F.norm])
  have R0 : ∀ h, F.av wR h = ∫ r in Iic (0 : ℝ), (Real.exp r : ℂ) • F.U r h := fun h => by
    rw [(sp h).2, ← integral_indicator measurableSet_Iic]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Iic (0 : ℝ) <;> simp [wR, hr]
  constructor
  · set c := F.av wR k with hc
    have Ut : ∀ t, F.U t c = (Real.exp (-t) : ℂ) • (c + ∫ r in (0 : ℝ)..t, (Real.exp r : ℂ) • F.U r k) := fun t => by
      rw [hc, R0, ← intervalIntegral.integral_Iic_sub_Iic (ig 0) (ig t), add_sub_cancel,
        ← (F.U t).integral_comp_comm (ig 0), ← integral_smul, ← integral_indicator measurableSet_Iic,
        ← integral_indicator measurableSet_Iic, ← integral_add_right_eq_self _ (-t)]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ≤ t
      · simp only [indicator_of_mem (show r + -t ∈ Iic (0 : ℝ) by simpa using hr), indicator_of_mem (show r ∈ Iic t from hr),
          map_smul, ← F.add, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add]
        congr 3 <;> ring
      · simp only [indicator_of_notMem (show r + -t ∉ Iic (0 : ℝ) by simpa using hr), indicator_of_notMem (show r ∉ Iic t from hr)]
    have der : ∀ t, HasDerivAt (fun t => F.U t c) (F.U t (k - c)) t := fun t => by
      have d1 : HasDerivAt (fun t : ℝ => (Real.exp (-t) : ℂ)) (-(Real.exp (-t) : ℂ)) t := by
        simpa using ((hasDerivAt_neg t).exp).ofReal_comp
      have d2 := (cg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c
      have d3 := d1.smul d2
      refine (d3.congr_of_eventuallyEq (Eventually.of_forall Ut)).congr_deriv ?_
      symm
      rw [map_sub, Ut, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
        one_smul, neg_smul, sub_eq_add_neg]
    refine ⟨c, fun t => ?_⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => der s) ((F.cont _).intervalIntegrable _ _), F.zero]
  · have i1 : IntegrableOn (fun r : ℝ => ⟪k, (Real.exp r : ℂ) • F.U r k⟫_ℂ) (Iic 0) := (ig 0).const_inner k
    rw [R0, ← integral_inner (ig 0), ← RCLike.re_to_complex, ← integral_re i1, ← integral_const_mul]
    have e : 2 * ‖k‖ ^ 2 = ∫ t in Iic (0 : ℝ), Real.exp t * (2 * ‖k‖ ^ 2) := by
      rw [integral_mul_const, integral_exp_Iic_zero, one_mul]
    rw [e, ← integral_sub ((integrableOn_exp_Iic 0).mul_const _) (i1.re.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [norm_sub_rev (F.U t k) k, @norm_sub_sq ℂ, F.norm, inner_smul_right, RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
end

