module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ShNull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvDense
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem symb_diff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) : Differentiable ℂ (symb κ) := fun z => by
  have c1 : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (w * t) • κ t := fun w =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have c2 : Continuous fun t : ℝ => (Complex.exp (z * t) * t) • κ t :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul Complex.continuous_ofReal).smul hk.1
  have c3 : Continuous fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := by
    have := hk.1
    fun_prop
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  have s3 : HasCompactSupport fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := hk.2.mono fun t ht h => ht (by simp [h])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun (w : ℂ) (t : ℝ) => Complex.exp (w * t) • κ t)
    (F' := fun (w : ℂ) (t : ℝ) => (Complex.exp (w * t) * t) • κ t) (bound := fun t => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖)
    (Metric.ball_mem_nhds z one_pos) (Eventually.of_forall fun w => (c1 w).aestronglyMeasurable)
    ((c1 z).integrable_of_hasCompactSupport s1) c2.aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) (c3.integrable_of_hasCompactSupport s3)
    (Eventually.of_forall fun t w _ => ?_)).2.differentiableAt
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have := norm_sub_norm_le w z
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  · simpa using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).smul_const (κ t)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convDense :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → IsUnit (symb β 0) → DenseRange (conv β) := by
  intro V _ _ _ _ β hk hu
  obtain ⟨k1, k2, k3⟩ := convAdj β hk
  let D : ℂ → ℂ := fun z => LinearMap.det (symb (sharp β) z : V →ₗ[ℂ] V)
  have hD : Differentiable ℂ D := by
    let b := Module.finBasis ℂ V
    have e : D = fun z => ∑ s : Equiv.Perm (Fin (Module.finrank ℂ V)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∏ i, (b.coord (s i)).toContinuousLinearMap (symb (sharp β) z (b i)) := by
      funext z
      simp only [D]
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
      simp [LinearMap.toMatrix_apply]
    rw [e]
    refine Differentiable.fun_sum fun s _ => (differentiable_const _).mul ?_
    intro z
    apply (Finset.analyticAt_fun_prod Finset.univ ?_).differentiableAt
    intro i _
    exact ((ContinuousLinearMap.differentiable _).comp ((symb_diff _ k1).clm_apply (differentiable_const _))).analyticAt z
  have h0 : D 0 ≠ 0 := by
    have : IsUnit (symb (sharp β) 0) := by
      rw [k3, map_zero, neg_zero]; exact hu.star
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 (ContinuousLinearMap.isUnit_iff_bijective.1 this))).ne_zero
  let g : ℝ → ℂ := fun ξ => D (2 * Real.pi * Complex.I * ξ)
  have ga : AnalyticOnNhd ℝ g univ := fun ξ _ => by
    have h1 : AnalyticAt ℝ (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)) ξ :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt ξ)
    exact (hD.analyticAt _).restrictScalars.comp h1
  have gz : ∀ᵐ ξ : ℝ, g ξ ≠ 0 := by
    have h1 := ga.preimage_zero_mem_codiscreteWithin (x := 0) (by simpa [g] using h0) trivial isConnected_univ
    have h2 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h1
    rw [Measure.restrict_univ] at h2
    exact h2
  have inj : ∀ y : L V, conv (sharp β) y = 0 → y = 0 := fun y hy => by
    rw [← (Lp.fourierTransformₗᵢ ℝ V).map_eq_zero_iff]
    refine Lp.ext ?_
    have h1 := fourConv (sharp β) k1 y
    rw [hy, map_zero] at h1
    filter_upwards [h1, gz, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with ξ a b c
    rw [c] at a ⊢
    have := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit b))).1
    exact this (a₁ := _) (a₂ := 0) (a.symm.trans (map_zero _).symm)
  have bot : (LinearMap.range (conv β : L V →ₗ[ℂ] L V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine inj y (ext_inner_left ℂ fun x => ?_)
    rw [← k2, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact hy _ ⟨x, rfl⟩
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 bot)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NAll
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nAll :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (N : W →ₗ[ℂ] V), M.IsN N → ∀ p : L W, Bdd p → M.F.Cob (M.J' p - M.J (one V (N (∫ x, p x)))) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M N hN p hp
  obtain ⟨h1, h2⟩ := cobTail p
  have h3 := (h2 (h1 hp)).2
  have h4 := (cobLaws (shF W)).2.2.2.2.2.2.2 M.F.rev (M.J'.toContinuousLinearEquiv : L W →L[ℂ] H) (fun t h => by
    show M.J' (sh W t h) = M.F.U (-t) (M.J' h)
    rw [M.hJ', neg_neg]) _ h3
  have h5 := ((cobLaws M.F).2.2.2.1 _).1 h4
  have h6 := ((cobLaws M.F).2.1 _ _ h5 (hN (∫ x, p x))).1
  convert h6 using 1
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.NIso
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.nIso :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), (∀ e, M.F.Cob (M.J (one V e)) → e = 0) ∧ ∀ N, M.IsN N → ∀ w, ‖N w‖ = ‖w‖ := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  obtain ⟨g, hg, g1, g2⟩ := grow (V := V) (W := W)
  have hb := (cobLaws M.F).2.2.2.2.2.1
  have e1 : ∀ (e : V) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J (one V e))‖ = g t * ‖e‖ := fun e t => by
    simp only [M.hJ]
    rw [← g1, ← M.J.norm_map]
    exact congrArg _ ((M.J.toContinuousLinearEquiv : L V →L[ℂ] H).intervalIntegral_comp_comm
      (((shF V).cont _).intervalIntegrable _ _))
  have e2 : ∀ (f : W) t, ‖∫ s in (0 : ℝ)..t, M.F.U s (M.J' (one W f))‖ = g t * ‖f‖ := fun f t => by
    simp only [M.hJ']
    rw [← g2, ← M.J'.norm_map]
    exact congrArg _ ((M.J'.toContinuousLinearEquiv : L W →L[ℂ] H).intervalIntegral_comp_comm
      (((shF W).rev.cont _).intervalIntegrable _ _))
  have key : ∀ d C : ℝ, (∀ t, |g t * d| ≤ C) → d = 0 := fun d C h => by
    by_contra hd
    have h1 : Tendsto (fun t => |g t| * |d|) atTop atTop := (tendsto_abs_atTop_atTop.comp hg).atTop_mul_const (abs_pos.2 hd)
    obtain ⟨t, ht⟩ := (h1.eventually_gt_atTop C).exists
    exact absurd (abs_mul (g t) d ▸ h t) (not_le.2 ht)
  refine ⟨fun e he => ?_, fun N hN w => ?_⟩
  · obtain ⟨C, hC⟩ := hb _ he
    exact norm_eq_zero.1 (key _ C fun t => by rw [← e1, abs_norm]; exact hC t)
  · obtain ⟨C, hC⟩ := hb _ (hN w)
    refine (sub_eq_zero.1 (key (‖w‖ - ‖N w‖) C fun t => ?_)).symm
    rw [mul_sub, ← e1, ← e2]
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← intervalIntegral.integral_sub ((M.F.cont _).intervalIntegrable _ _) ((M.F.cont _).intervalIntegrable _ _)]
    simpa only [map_sub] using hC t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ProjLaws
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (M : Sc H V W)

private theorem P_app (s : Set ℝ) (h : H) : M.P s h = M.J (cut V s (M.J.symm h)) := rfl

private theorem one' (s t : Set ℝ) (hs : MeasurableSet s) (ht : MeasurableSet t) : M.P s ∘L M.P t = M.P (s ∩ t) ∧ IsSelfAdjoint (M.P s) ∧ ‖M.P s‖ ≤ 1 ∧
    (Disjoint s t → M.P (s ∪ t) = M.P s + M.P t) ∧ ∀ a : ℝ, M.F.U a ∘L M.P s = M.P ((fun x => x + a) ⁻¹' s) ∘L M.F.U a := by
  obtain ⟨c1, c2, c3, -, -, c4, c5, -⟩ := cutLaws (V := V) s t hs ht
  refine ⟨?_, ?_, ?_, fun hd => ?_, fun a => ?_⟩
  · ext h
    simp only [ContinuousLinearMap.comp_apply, P_app, M.J.symm_apply_apply, ← c1]
  · refine LinearMap.IsSymmetric.isSelfAdjoint fun x y => ?_
    obtain ⟨u, rfl⟩ := M.J.surjective x
    obtain ⟨v, rfl⟩ := M.J.surjective y
    simp only [ContinuousLinearMap.coe_coe, P_app, M.J.symm_apply_apply, M.J.inner_map_map]
    exact c2.isSymmetric u v
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => ?_
    rw [P_app, M.J.norm_map, one_mul]
    exact (c4 _).trans_eq (M.J.symm.norm_map h)
  · ext h
    simp only [P_app, c3 hd, ContinuousLinearMap.add_apply, map_add (f := _)]
  · ext h
    obtain ⟨u, rfl⟩ := M.J.surjective h
    simp only [ContinuousLinearMap.comp_apply, P_app, M.J.symm_apply_apply, M.hJ]
    exact congrArg M.J (DFunLike.congr_fun (c5 a) u)
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.projLaws :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W), M.F.Null ∧ M.swap.swap.F.U = M.F.U ∧ (∀ s, M.swap.P' s = M.P s) ∧ (∀ T T', M.swap.abelian₂ T' T = M.abelian₂ T T') ∧
      (∀ s t : Set ℝ, MeasurableSet s → MeasurableSet t → M.P s ∘L M.P t = M.P (s ∩ t) ∧ IsSelfAdjoint (M.P s) ∧ ‖M.P s‖ ≤ 1 ∧
        (Disjoint s t → M.P (s ∪ t) = M.P s + M.P t) ∧ ∀ a : ℝ, M.F.U a ∘L M.P s = M.P ((fun x => x + a) ⁻¹' s) ∘L M.F.U a ∧
          M.F.U a ∘L M.P' s = M.P' ((fun x => x - a) ⁻¹' s) ∘L M.F.U a) ∧ M.P ∅ = 0 ∧ M.P univ = 1 ∧
      ∀ T T', 2 * M.T₀ ≤ T + T' → M.P (Ioi T) ∘L M.P' (Ioi T') = 0 ∧ M.P' (Ioi T') ∘L M.P (Ioi T) = 0 ∧
        M.abelian₂ T T' ∘L M.abelian₂ T T' = M.abelian₂ T T' ∧ IsSelfAdjoint (M.abelian₂ T T') ∧ ‖M.abelian₂ T T'‖ ≤ 1 ∧
        M.abelian₂ T T' ∘L M.P (Ioi T) = 0 ∧ M.P (Ioi T) ∘L M.abelian₂ T T' = 0 ∧ M.abelian₂ T T' ∘L M.P' (Ioi T') = 0 ∧ M.P' (Ioi T') ∘L M.abelian₂ T T' = 0 := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M
  have hn : M.F.Null := fun h h' => by
    obtain ⟨u, rfl⟩ := M.J.surjective h
    obtain ⟨u', rfl⟩ := M.J.surjective h'
    simp only [M.hJ, M.J.inner_map_map]
    exact shNull u u'
  refine ⟨hn, funext fun t => by simp [Sc.swap, Flow.rev], fun _ => rfl, fun T T' => sub_right_comm _ _ _,
    fun s t hs ht => ⟨(one' M s t hs ht).1, (one' M s t hs ht).2.1, (one' M s t hs ht).2.2.1, (one' M s t hs ht).2.2.2.1,
      fun a => ⟨(one' M s t hs ht).2.2.2.2 a, ?_⟩⟩, ?_, ?_, fun T T' hT => ?_⟩
  · have := (one' M.swap s t hs ht).2.2.2.2 (-a)
    simpa [Sc.swap, Flow.rev, Sc.P', sub_eq_add_neg] using this
  · ext h
    rw [P_app, (cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.2.1]; simp
  · ext h
    rw [P_app, (cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.1]; simp
  · obtain ⟨a1, a2, -⟩ := one' M (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
    obtain ⟨b1, b2, -⟩ := one' M.swap (Ioi T') (Ioi T') measurableSet_Ioi measurableSet_Ioi
    rw [inter_self] at a1 b1
    change M.P' (Ioi T') ∘L M.P' (Ioi T') = M.P' (Ioi T') at b1
    change IsSelfAdjoint (M.P' (Ioi T')) at b2
    have o1 : M.P (Ioi T) * M.P' (Ioi T') = 0 := by
      ext h
      refine ext_inner_left ℂ fun y => ?_
      have hc := (cutLaws (V := W) (Ioi (2 * M.T₀ - T)) (Ioi T') measurableSet_Ioi measurableSet_Ioi).1
      rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at hc
      have e : M.P' (Ioi T') h = M.J' (cut W (Ioi (2 * M.T₀ - T)) (cut W (Ioi T') (M.J'.symm h))) :=
        congrArg M.J' (DFunLike.congr_fun hc _).symm
      rw [ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, e, P_app, M.causal]; simp
    have o2 : M.P' (Ioi T') * M.P (Ioi T) = 0 := by
      have := congrArg star o1
      rwa [star_mul, a2.star_eq, b2.star_eq, star_zero] at this
    change M.P (Ioi T) * M.P (Ioi T) = _ at a1
    change M.P' (Ioi T') * M.P' (Ioi T') = _ at b1
    have l1 : M.abelian₂ T T' * M.P (Ioi T) = 0 := by rw [Sc.abelian₂, sub_mul, sub_mul, a1, o2]; simp
    have l2 : M.P (Ioi T) * M.abelian₂ T T' = 0 := by rw [Sc.abelian₂, mul_sub, mul_sub, a1, o1]; simp
    have l3 : M.abelian₂ T T' * M.P' (Ioi T') = 0 := by rw [Sc.abelian₂, sub_mul, sub_mul, b1, o1]; simp
    have l4 : M.P' (Ioi T') * M.abelian₂ T T' = 0 := by rw [Sc.abelian₂, mul_sub, mul_sub, b1, o2]; simp
    have l0 : M.abelian₂ T T' * M.abelian₂ T T' = M.abelian₂ T T' := by
      conv_lhs => rw [show M.abelian₂ T T' * M.abelian₂ T T' = M.abelian₂ T T' * (1 - M.P (Ioi T) - M.P' (Ioi T')) from rfl]
      rw [mul_sub, mul_sub, l1, l3]; simp
    have sa : IsSelfAdjoint (M.abelian₂ T T') := ((IsSelfAdjoint.one _).sub a2).sub b2
    exact ⟨o1, o2, l0, sa, (IsStarProjection.mk l0 sa).norm_le _, l1, l2, l3, l4⟩
end

