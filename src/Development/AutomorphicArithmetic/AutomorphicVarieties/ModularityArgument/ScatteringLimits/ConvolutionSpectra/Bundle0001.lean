module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.Bundle0009
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avSpec :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), (∀ t, ContinuousLinearMap.adjoint (F.U t) = F.U (-t)) ∧ Integrable wR ∧ (∫ t, ‖wR t‖ = 1) ∧ ∀ ψ : ℝ → ℂ, Integrable ψ →
      (∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h) ∧ ‖F.av ψ‖ ≤ ∫ t, ‖ψ t‖ ∧
      ContinuousLinearMap.adjoint (F.av ψ) = F.av (fun t => conj (ψ (-t))) ∧ F.rev.av ψ = F.av (fun t => ψ (-t)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → Y ∘L F.av ψ = F'.av ψ ∘L Y := by
  intro H _ _ _ F
  have hin : ∀ t x y, ⟪F.U t x, F.U t y⟫_ℂ = ⟪x, y⟫_ℂ := fun t x y =>
    (⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hadj : ∀ t x y, ⟪F.U t x, y⟫_ℂ = ⟪x, F.U (-t) y⟫_ℂ := fun t x y => by
    rw [← hin t x, ← F.add, add_neg_cancel, F.zero]
  have hw : Integrable wR := by
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    exact (integrableOn_exp_Iic 0).ofReal
  have spec : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F : Flow G) (ψ : ℝ → ℂ), Integrable ψ →
      ∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h := by
    intro G _ _ _ F ψ hψ
    have hi : ∀ h, Integrable (fun t => ψ t • F.U t h) := fun h =>
      hψ.smul_bdd ‖h‖ (F.cont h).aestronglyMeasurable (Eventually.of_forall fun t => (F.norm t h).le)
    let A : G →ₗ[ℂ] G :=
      { toFun := fun h => ∫ t, ψ t • F.U t h
        map_add' := fun x y => by simp only [map_add (f := _), smul_add]; exact integral_add (hi x) (hi y)
        map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm _ c]; exact integral_smul c _ }
    have hb : ∀ h, ‖A h‖ ≤ (∫ t, ‖ψ t‖) * ‖h‖ := fun h => by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul, F.norm]
      exact integral_mul_const _ _
    exact fun h => ⟨hi h, Classical.epsilon_spec (p := fun A : G →L[ℂ] G => ∀ h, A h = ∫ t, ψ t • F.U t h)
      ⟨A.mkContinuous _ hb, fun _ => rfl⟩ h⟩
  refine ⟨fun t => ?_, hw, ?_, fun ψ hψ => ⟨spec F ψ hψ, ?_, ?_, ?_, ?_⟩⟩
  · exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => by rw [hadj, neg_neg]).symm
  · have : (fun t => ‖wR t‖) = (Iic (0 : ℝ)).indicator Real.exp := by
      funext t
      by_cases h : t ∈ Iic (0 : ℝ) <;> simp [wR, h]
    rw [this, integral_indicator measurableSet_Iic, integral_exp_Iic_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun h => ?_
    rw [(spec F ψ hψ h).2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_smul, F.norm]
    exact integral_mul_const _ _
  · have hψ' : Integrable fun t => conj (ψ (-t)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hψ.comp_neg
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
    rw [(spec F ψ hψ y).2, (spec F _ hψ' x).2, ← integral_inner (spec F ψ hψ y).1, ← inner_conj_symm,
      ← integral_inner (spec F _ hψ' x).1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg, inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hadj]
  · ext h
    rw [(spec F.rev ψ hψ h).2, (spec F _ hψ.comp_neg h).2, ← integral_neg_eq_self]
    simp [Flow.rev]
  · intro G _ _ _ F' Y hY
    ext h
    simp only [ContinuousLinearMap.comp_apply]
    rw [(spec F ψ hψ h).2, (spec F' ψ hψ _).2, ← Y.integral_comp_comm (spec F ψ hψ h).1]
    simp only [map_smul, hY]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ContAdj
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private theorem cnt [TopologicalSpace.SeparableSpace H] {ι : Type} {v : ι → H} (hv : Orthonormal ℂ v) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (v i) (1 / 2)) (fun i j hij => ?_)
    (fun _ => Metric.isOpen_ball) fun i => Metric.nonempty_ball.2 (by norm_num)
  refine Metric.ball_disjoint_ball ?_
  have h := @norm_sub_sq ℂ H _ _ _ (v i) (v j)
  rw [hv.1, hv.1, hv.2 hij] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (v i - v j)]

private theorem contAdj {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => ContinuousLinearMap.adjoint (k y) c :=
  (ContinuousLinearMap.adjoint.continuous.comp hk).clm_apply continuous_const

private theorem cSq {k : ℝ → V →L[ℂ] H} (hk : Continuous k) (c : H) : Continuous fun y => ‖ContinuousLinearMap.adjoint (k y) c‖ ^ 2 :=
  (contAdj hk c).norm.pow 2

private theorem memL (a b : ℝ) {g : ℝ → V} (hg : Continuous g) : MemLp ((Ioc a b).indicator g) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc.nullMeasurableSet]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Icc a b))
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => hC x (Ioc_subset_Icc_self hx)))

private theorem adjEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : ContinuousLinearMap.adjoint Y c = J ((memL a b (contAdj hk c)).toLp _) := by
  refine ext_inner_right ℂ fun h => ?_
  obtain ⟨u, rfl⟩ := J.surjective h
  have hu : IntegrableOn (u : ℝ → V) (Ioc a b) := ((Lp.memLp u).restrict _).integrable one_le_two
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.continuousOn (s := Icc a b))
  have hi : IntegrableOn (fun y => k y (u y)) (Ioc a b) := by
    refine (hu.norm.const_mul C).mono' ?_ ?_
    · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hk.aestronglyMeasurable.prodMk hu.1)
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx =>
        (k x).le_of_opNorm_le (hC x (Ioc_subset_Icc_self hx)) _)
  rw [ContinuousLinearMap.adjoint_inner_left, hY, ← integral_inner hi, J.inner_map_map, L2.inner_def,
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp] with x hx
  rw [hx]
  by_cases h : x ∈ Ioc a b <;> simp [h, ContinuousLinearMap.adjoint_inner_left]

private theorem innEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) (c : H) :
    ⟪ContinuousLinearMap.adjoint Y c, ContinuousLinearMap.adjoint Y' c⟫_ℂ = ∫ y in Ioc a b, ⟪ContinuousLinearMap.adjoint (k y) c, ContinuousLinearMap.adjoint (k' y) c⟫_ℂ := by
  rw [adjEq J a b hk hY, adjEq J a b hk' hY', J.inner_map_map, L2.inner_def, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae ?_
  filter_upwards [(memL a b (contAdj hk c)).coeFn_toLp, (memL a b (contAdj hk' c)).coeFn_toLp] with x hx hx'
  rw [hx, hx']
  by_cases h : x ∈ Ioc a b <;> simp [h]

private theorem normEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (c : H) : ‖ContinuousLinearMap.adjoint Y c‖ ^ 2 = ∫ y in Ioc a b, ‖ContinuousLinearMap.adjoint (k y) c‖ ^ 2 := by
  have h := innEq J a b hk hk hY hY c
  simp only [inner_self_eq_norm_sq_to_K] at h
  have e : ∀ x : ℝ, ((x : ℂ) ^ 2) = ((x ^ 2 : ℝ) : ℂ) := fun x => by push_cast; rfl
  change ((‖ContinuousLinearMap.adjoint Y c‖ : ℝ) : ℂ) ^ 2 = ∫ y in Ioc a b, ((‖ContinuousLinearMap.adjoint (k y) c‖ : ℝ) : ℂ) ^ 2 at h
  simp only [e] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

private theorem ptSum {ι : Type} (c : HilbertBasis ι ℂ H) (A A' : V →L[ℂ] H) :
    HasSum (fun m => ⟪ContinuousLinearMap.adjoint A (c m), ContinuousLinearMap.adjoint A' (c m)⟫_ℂ) (∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), A (stdOrthonormalBasis ℂ V i)⟫_ℂ) := by
  have h := hasSum_sum (s := Finset.univ) fun i _ => c.hasSum_inner_mul_inner (A' (stdOrthonormalBasis ℂ V i)) (A (stdOrthonormalBasis ℂ V i))
  suffices e : ∀ m, ⟪ContinuousLinearMap.adjoint A (c m), ContinuousLinearMap.adjoint A' (c m)⟫_ℂ = ∑ i, ⟪A' (stdOrthonormalBasis ℂ V i), c m⟫_ℂ * ⟪c m, A (stdOrthonormalBasis ℂ V i)⟫_ℂ by
    simpa only [e] using h
  intro m
  rw [← (stdOrthonormalBasis ℂ V).sum_inner_mul_inner]
  exact Finset.sum_congr rfl fun i _ => by
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right, mul_comm]

private theorem ptSumR {ι : Type} (c : HilbertBasis ι ℂ H) (A : V →L[ℂ] H) :
    HasSum (fun m => ‖ContinuousLinearMap.adjoint A (c m)‖ ^ 2) (∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2) := by
  have h := (ptSum c A A).mapL Complex.reCLM
  simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using h

private theorem summ (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) {ι : Type} (c : HilbertBasis ι ℂ H) :
    Summable fun m => ‖ContinuousLinearMap.adjoint Y (c m)‖ ^ 2 := by
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine summable_of_sum_le (c := ∫ y in Ioc a b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2) (fun _ => sq_nonneg _) fun s => ?_
  simp only [normEq J a b hk hY]
  rw [← integral_finsetSum _ fun m _ => ci (cSq hk _)]
  refine integral_mono (integrable_finsetSum _ fun m _ => ci (cSq hk _))
    (ci (continuous_finsetSum _ fun i _ => (hk.clm_apply continuous_const).norm.pow 2)) fun y => ?_
  exact sum_le_hasSum s (fun _ _ => sq_nonneg _) (ptSumR c (k y))

private theorem isHS (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k : ℝ → V →L[ℂ] H} {Y : H →L[ℂ] H} (hk : Continuous k)
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) : IsHilbertSchmidt Y := by
  rw [← isHilbertSchmidt_adjoint_iff, isHilbertSchmidt_iff (stdHilbertBasis ℂ H)]
  have h := summ J a b hk hY (stdHilbertBasis ℂ H)
  have := h.tsum_ofReal_lt_top
  simpa [ENNReal.ofReal_pow] using this

private theorem trEq (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) {k k' : ℝ → V →L[ℂ] H} {Y Y' : H →L[ℂ] H} (hk : Continuous k) (hk' : Continuous k')
    (hY : ∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) (hY' : ∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) :
    trace (ContinuousLinearMap.adjoint Y' ∘L Y) = ∫ y in Ioc a b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  have h1 := isHS J a b hk hY
  have h2 := (isHS J a b hk' hY').adjoint
  let c := stdHilbertBasis ℂ H
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : TopologicalSpace.SeparableSpace H := J.surjective.denseRange.separableSpace J.continuous
  haveI := cnt c.orthonormal
  have s1 := (isTraceClass_comp h1 h2).hasSum_trace c
  have ci : ∀ {f : ℝ → ℝ}, Continuous f → IntegrableOn f (Ioc a b) := fun hf => hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have cg : ∀ m, Continuous fun y => ⟪ContinuousLinearMap.adjoint (k y) (c m), ContinuousLinearMap.adjoint (k' y) (c m)⟫_ℂ := fun m => (contAdj hk _).inner (contAdj hk' _)
  have s2 := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioc a b))
    (F := fun m y => ⟪ContinuousLinearMap.adjoint (k y) (c m), ContinuousLinearMap.adjoint (k' y) (c m)⟫_ℂ)
    (fun m => (cg m).integrableOn_Icc.mono_set Ioc_subset_Icc_self) (by
      refine Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun m => ?_)
        ((summ J a b hk hY c).add (summ J a b hk' hY' c))
      rw [normEq J a b hk hY, normEq J a b hk' hY', ← integral_add (ci (cSq hk _)) (ci (cSq hk' _))]
      refine integral_mono (ci (cg m).norm) ((ci (cSq hk _)).add (ci (cSq hk' _))) fun y => ?_
      refine (norm_inner_le_norm _ _).trans ?_
      show _ ≤ ‖ContinuousLinearMap.adjoint (k y) (c m)‖ ^ 2 + ‖ContinuousLinearMap.adjoint (k' y) (c m)‖ ^ 2
      nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint (k y) (c m)‖ - ‖ContinuousLinearMap.adjoint (k' y) (c m)‖), norm_nonneg (ContinuousLinearMap.adjoint (k y) (c m)), norm_nonneg (ContinuousLinearMap.adjoint (k' y) (c m))])
  simp only [← innEq J a b hk hk' hY hY', (ptSum c _ _).tsum_eq] at s2
  rw [trace_comp_comm_of_isHilbertSchmidt h2 h1]
  refine s1.unique ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] using s2
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.kp :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V ≃ₗᵢ[ℂ] H) (a b : ℝ) (k k' : ℝ → V →L[ℂ] H) (Y Y' : H →L[ℂ] H), a ≤ b → Continuous k → Continuous k' →
      (∀ u : L V, Y (J u) = ∫ y in Ioc a b, k y (u y)) → (∀ u : L V, Y' (J u) = ∫ y in Ioc a b, k' y (u y)) →
      IsHilbertSchmidt Y ∧ hsNorm Y ^ 2 = ∫ y in a..b, ∑ i, ‖k y (stdOrthonormalBasis ℂ V i)‖ ^ 2 ∧
        trace (ContinuousLinearMap.adjoint Y' ∘L Y) = ∫ y in a..b, ∑ i, ⟪k' y (stdOrthonormalBasis ℂ V i), k y (stdOrthonormalBasis ℂ V i)⟫_ℂ := by
  intro H _ _ _ V _ _ _ _ J a b k k' Y Y' hab hk hk' hY hY'
  have h1 := isHS J a b hk hY
  refine ⟨h1, ?_, by rw [intervalIntegral.integral_of_le hab]; exact trEq J a b hk hk' hY hY'⟩
  have s1 := (isTraceClass_comp h1.adjoint h1).hasSum_trace (stdHilbertBasis ℂ H)
  rw [trEq J a b hk hk hY hY] at s1
  have s2 := Complex.hasSum_ofReal.2 (h1.hasSum_norm_sq (stdHilbertBasis ℂ H))
  have e : ∀ x : H, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, e, ← Complex.ofReal_sum] at s1
  rw [integral_complex_ofReal] at s1
  rw [intervalIntegral.integral_of_le hab]
  exact_mod_cast s2.unique s1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CptNull
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cptNull :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (K : H →L[ℂ] H) (x : ι → H) (C : ℝ), IsCompactOperator K → (∀ i, ‖x i‖ ≤ C) →
      (∀ y, Tendsto (fun i => ⟪y, x i⟫_ℂ) l (𝓝 0)) → Tendsto (fun i => K (x i)) l (𝓝 0) := by
  intro H _ _ _ ι l K x C hK hb hw
  obtain ⟨S, hS, hsub⟩ := hK.image_closedBall_subset_compact C
  refine hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun i => hsub ⟨x i, by simpa using hb i, rfl⟩) ?_
  intro y _ hy
  have h1 : Tendsto (fun i => ⟪y, K (x i)⟫_ℂ) l (𝓝 0) := by
    simpa [ContinuousLinearMap.adjoint_inner_left] using hw (ContinuousLinearMap.adjoint K y)
  have h2 : MapClusterPt ⟪y, y⟫_ℂ l (fun i => ⟪y, K (x i)⟫_ℂ) :=
    hy.continuousAt_comp (f := fun z => ⟪y, z⟫_ℂ) (by fun_prop)
  have h3 : ⟪y, y⟫_ℂ = 0 := eq_of_nhds_neBot (h2.clusterPt.mono h1).neBot
  exact inner_self_eq_zero.1 h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutSpec
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s : Set ℝ), MeasurableSet s → ∀ u : L V, ∀ᵐ x : ℝ, cut V s u x = s.indicator u x := by
  intro V _ _ _ _ s hs
  have hm : ∀ u : L V, MemLp (s.indicator (u : ℝ → V)) 2 volume := fun u => (Lp.memLp u).indicator hs.nullMeasurableSet
  let A : L V →ₗ[ℂ] L V :=
    { toFun := fun u => (hm u).toLp _
      map_add' := fun u v => Lp.ext (by
        filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx]; exact h4
        · simp [hx])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((hm u).toLp _)] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h4]) }
  have hb : ∀ u, ‖A u‖ ≤ 1 * ‖u‖ := fun u => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [(hm u).coeFn_toLp] with x h
    show ‖((hm u).toLp _ : ℝ → V) x‖ ≤ _
    rw [h]
    exact norm_indicator_le_norm_self _ _
  exact Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x)
    ⟨A.mkContinuous 1 hb, fun u => (hm u).coeFn_toLp⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourAe
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourAe :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), Integrable (u : ℝ → V) → ∀ᵐ ξ : ℝ, Lp.fourierTransformₗᵢ ℝ V u ξ = 𝓕 (u : ℝ → V) ξ := by
  intro V _ _ _ _ u hu
  have hc : Continuous (𝓕 (u : ℝ → V)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hu
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hc.locallyIntegrable ?_
  intro g hg hgc
  have hs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let φ : SchwartzMap ℝ ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun T : TemperedDistribution ℝ V => T φ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h2 := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume) (f := (φ : ℝ → ℂ)) (g := (u : ℝ → V))
    Real.continuous_fourierChar (by fun_prop) φ.integrable hu
  have h3 : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
  rw [h3] at h2
  have e : ∀ (x : ℝ) (v : V), g x • v = φ x • v := fun x v => by rw [hφ, Complex.coe_smul]
  simp only [e]
  exact h1.symm.trans h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TrWeak
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.trWeak :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (A : ι → H →L[ℂ] H) (A₀ Z : H →L[ℂ] H), IsTraceClass Z → (∀ i, ‖A i‖ ≤ 1) →
      (∀ x y, Tendsto (fun i => ⟪x, A i y⟫_ℂ) l (𝓝 ⟪x, A₀ y⟫_ℂ)) → Tendsto (fun i => trace (A i ∘L Z)) l (𝓝 (trace (A₀ ∘L Z))) := by
  intro H _ _ _ ι l A A₀ Z hZ hA hw
  obtain ⟨S, T, hS, hT, rfl⟩ := hZ.exists_comp
  let b := stdHilbertBasis ℂ H
  have e : ∀ B : H →L[ℂ] H, trace (B ∘L S ∘L T) = ∑' m, ⟪ContinuousLinearMap.adjoint T (b m), B (S (b m))⟫_ℂ := fun B => by
    have h1 : trace ((B ∘L S) ∘L T) = trace (T ∘L (B ∘L S)) := trace_comp_comm_of_isHilbertSchmidt (hS.comp_left B) hT
    have h2 := ((isTraceClass_comp hT (hS.comp_left B)).hasSum_trace b).tsum_eq
    simp only [ContinuousLinearMap.adjoint_inner_left]
    exact h1.trans h2.symm
  simp only [e]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖ContinuousLinearMap.adjoint T (b m)‖ ^ 2 + ‖S (b m)‖ ^ 2)
    ((hT.adjoint.hasSum_norm_sq b).summable.add (hS.hasSum_norm_sq b).summable) (fun m => hw _ _) (Eventually.of_forall fun i m => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  have h3 : ‖A i (S (b m))‖ ≤ ‖S (b m)‖ := by simpa using (A i).le_of_opNorm_le (hA i) (S (b m))
  nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint T (b m)‖ - ‖S (b m)‖), norm_nonneg (ContinuousLinearMap.adjoint T (b m)),
    norm_nonneg (S (b m)), mul_le_mul_of_nonneg_left h3 (norm_nonneg (ContinuousLinearMap.adjoint T (b m)))]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TwoProj
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.twoProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Λ E Λ' E' Y : H →L[ℂ] H), Λ + E = Λ' + E' → Λ ∘L Λ = Λ → E ∘L E = E → Λ' ∘L Λ' = Λ' → E' ∘L E' = E' →
      Λ ∘L E = 0 → E ∘L Λ = 0 → Λ' ∘L E' = 0 → E' ∘L Λ' = 0 → IsTraceClass (Λ ∘L Y ∘L Λ) → IsTraceClass (E ∘L Y) →
      IsTraceClass (Y ∘L E) → IsTraceClass (Y ∘L E') →
      IsTraceClass (Λ' ∘L Y ∘L Λ') ∧ trace (Λ ∘L Y ∘L Λ) + trace (E ∘L Y) = trace (Λ' ∘L Y ∘L Λ') + trace (Y ∘L E') := by
  intro H _ _ _ Λ E Λ' E' Y hs h1 h2 h3 h4 h5 h6 h7 h8 t1 t2 t3 t4
  have key : ∀ A B Z : H →L[ℂ] H, A * A = A → B * B = B → A * B = 0 → B * A = 0 → IsTraceClass ((A + B) * Z * (A + B)) →
      IsTraceClass (A * Z * A) ∧ trace ((A + B) * Z * (A + B)) = trace (A * Z * A) + trace (B * Z * B) := by
    intro A B Z a b ab ba h
    have e1 : A * ((A + B) * Z * (A + B)) * A = A * Z * A := by
      rw [← mul_assoc, ← mul_assoc, mul_add A A, a, ab, add_zero, mul_assoc, add_mul, a, ba, add_zero]
    have e2 : B * ((A + B) * Z * (A + B)) * B = B * Z * B := by
      rw [← mul_assoc, ← mul_assoc, mul_add B A, b, ba, zero_add, mul_assoc, add_mul, b, ab, zero_add]
    set Q := (A + B) * Z * (A + B) with hQ
    have e3 : Q = A * Q + B * Q := by
      rw [← add_mul, hQ, ← mul_assoc, ← mul_assoc, add_mul A B (A + B), mul_add A, mul_add B, a, b, ab, ba, add_zero, zero_add]
    have c : ∀ P : H →L[ℂ] H, P * P = P → trace (P * Q) = trace (P * Q * P) := fun P hP => by
      have := trace_comp_comm (h.comp_left P) P
      change trace (P * (P * Q)) = trace (P * Q * P) at this
      rwa [← mul_assoc, hP] at this
    refine ⟨e1 ▸ (h.comp_left A).comp_right A, ?_⟩
    rw [← e1, ← e2, ← c A a, ← c B b]
    conv_lhs => rw [e3]
    exact trace_add (h.comp_left A) (h.comp_left B)
  have hT : IsTraceClass ((Λ + E) * Y * (Λ + E)) := by
    have : (Λ + E) * Y * (Λ + E) = Λ * (Y * Λ) + (Λ * (Y * E) + E * Y * (Λ + E)) := by noncomm_ring
    rw [this]
    exact t1.add ((t3.comp_left Λ).add (t2.comp_right (Λ + E)))
  obtain ⟨-, k1⟩ := key Λ E Y h1 h2 h5 h6 hT
  rw [hs] at hT k1
  obtain ⟨k2, k3⟩ := key Λ' E' Y h3 h4 h7 h8 hT
  have c1 : trace (E * Y * E) = trace (E * Y) := by
    have := trace_comp_comm t2 E
    change trace (E * (E * Y)) = trace (E * Y * E) at this
    rw [← this, ← mul_assoc]; exact congrArg (fun Z => trace (Z * Y)) h2
  have c2 : trace (E' * Y * E') = trace (Y * E') := by
    have := trace_comp_comm t4 E'
    change trace (E' * (Y * E')) = trace (Y * E' * E') at this
    rw [mul_assoc, this, mul_assoc]; exact congrArg (fun Z => trace (Y * Z)) h4
  refine ⟨k2, ?_⟩
  change trace (Λ * (Y * Λ)) + trace (E * Y) = trace (Λ' * (Y * Λ')) + trace (Y * E')
  rw [← mul_assoc, ← mul_assoc, ← c1, ← c2, ← k1, k3]
end

