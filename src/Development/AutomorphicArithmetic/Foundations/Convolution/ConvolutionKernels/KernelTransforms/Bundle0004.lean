module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.IsNormAlong
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensMeas
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0001
public import GroundTheory.AutomorphicForms.CuspidalProjection.Global
public import GroundTheory.AutomorphicForms.GKModules.Garding

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AvgTens
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.avgTens :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n) (Φ : AdelicGLn.AdelicGL K n → ℂ),
      (∀ g, Φ g = β (infPart K n g) * e (finPart K n g)) →
      (∀ x, PositivityTheory.Rg.Tf.Geo.avg Φ x = tens β e x) ∧
      ∀ g : AdelicGLn.AdelicGL K n, archEquiv K n (PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.fst _ _) g) = infPart K n g := by
  intro K _ _ n hn β e Φ hΦ
  refine ⟨fun x => ?_, fun g => ?_⟩
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    have ht : tens β e x = tensFun β e x := by
      have h1 : Continuous (tensFun β e) := by
        unfold tensFun
        exact ((continuous_kbar hn β.continuous β.hasCompactSupport).comp
          (continuous_infPart.comp continuous_subtype_val)).mul
          (e.continuous.comp (continuous_finPart.comp continuous_subtype_val))
      have hfin : Continuous (MultiplicityOne.finProj (K := K) (n := n)) :=
        continuous_retractOne.comp continuous_finEmb
      have hfinC : IsCompact (MultiplicityOne.finProj (K := K) (n := n) '' tsupport e) :=
        e.hasCompactSupport.isCompact.image hfin
      have harchC : IsCompact (archP K n '' tsupport β) :=
        β.hasCompactSupport.isCompact.image continuous_archP
      have hC : IsCompact (archP K n '' tsupport β * MultiplicityOne.finProj (K := K) (n := n) '' tsupport e) :=
        harchC.mul hfinC
      have hS : Function.support (tensFun β e) ⊆
          archP K n '' tsupport β * MultiplicityOne.finProj (K := K) (n := n) '' tsupport e := by
        intro y hy
        let a := infPart K n (y : AdelicGLn.AdelicGL K n)
        let h := finPart K n (y : AdelicGLn.AdelicGL K n)
        change kbar β a * e h ≠ 0 at hy
        have he := right_ne_zero_of_mul hy
        obtain ⟨s, hs⟩ : ∃ s, β (a * zInf K n s) ≠ 0 := by
          by_contra h0
          simp only [not_exists, ne_eq, not_not] at h0
          exact left_ne_zero_of_mul hy (by simp [kbar, h0])
        have hproj : archP K n (a * zInf K n s) * MultiplicityOne.finProj (K := K) (n := n) h = y := by
          have hf : MultiplicityOne.finProj (K := K) (n := n) h = retractOne (finEmb K n h) := rfl
          rw [archimedeanProjection_mul_positiveScalar hn, hf, ← retract_infEmb, ← retractOne_mul]
          change retractOne (infEmb K n (infPart K n (y : AdelicGLn.AdelicGL K n)) *
            finEmb K n (finPart K n (y : AdelicGLn.AdelicGL K n))) = y
          rw [infEmb_infPart_mul_finEmb_finPart, retractOne_coe]
        rw [← hproj]
        exact Set.mul_mem_mul ⟨_, subset_tsupport _ hs, rfl⟩ ⟨_, subset_tsupport _ he, rfl⟩
      have h2 : HasCompactSupport (tensFun β e) :=
        hC.of_isClosed_subset isClosed_closure (closure_minimal hS hC.isClosed)
      have h : Continuous (tensFun β e) ∧ HasCompactSupport (tensFun β e) := ⟨h1, h2⟩
      rw [tens, dite_eq_left h]
      rfl
    rw [ht, tensFun, kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos,
      hemb.integral_map, ← integral_mul_const]
    unfold PositivityTheory.Rg.Tf.Geo.avg
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have h1 : infPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        infPart K n (x : AdelicGLn.AdelicGL K n) * zInf K n (GroundTheory.Global.expPos t) := by
      rw [map_mul (infPart K n), ← zInf_mul_comm]
      rfl
    have h2 : CuspidalSpectrum.finPart K n (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) =
        CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n) := by
      rw [map_mul (CuspidalSpectrum.finPart K n), finPart_centralSection, one_mul]
    change Φ (centralSection K n (GroundTheory.Global.expPos t) * (x : AdelicGLn.AdelicGL K n)) = _
    rw [hΦ, h1, h2]
  · rw [infPart_apply]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.compatEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
      (∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (ν : Measure (archGroup K n)) (_ : ν.IsHaarMeasure), Compat μ ν m) ∧
      (∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure], ∃ (m : Measure (AdelicGLn.FiniteAdelicGL K n)) (_ : m.IsHaarMeasure), Compat μ ν m) ∧
      ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ (μ : Measure (normOneGL (K := K) (n := n))) (_ : μ.IsHaarMeasure), Compat μ ν m := by
  intro K _ _ n hn
  have main : ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
      (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧
      Compat μ (c • ν) m ∧ Compat μ ν (c • m) ∧ Compat (c⁻¹ • μ) ν m := by
    intro μ _ ν _ m _
    obtain ⟨c, hc, h⟩ := UpperTheory.ConvolutionTheory.Tf.tensMeas K n hn μ ν m
    lift c to NNReal using hc.le
    have h' : ∀ (β : TI K n) (e : TF K n) (Θ : normOneGL (K := K) (n := n) → ℂ), Continuous Θ → ∫ x, tens β e x * Θ x ∂μ =
        ((c : ℝ) : ℂ) * ∫ a, ∫ y, β a * e y * Θ (archP K n a * MultiplicityOne.finProj K n y) ∂m ∂ν := fun β e Θ hΘ => by
      rw [← h β e Θ hΘ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1 x]
      rfl
    have hc0 : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    refine ⟨c, by exact_mod_cast hc.ne', fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_, fun β e Θ hΘ => ?_⟩
    · rw [h' β e Θ hΘ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [h' β e Θ hΘ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      dsimp only
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    · rw [integral_smul_nnreal_measure, h' β e Θ hΘ, NNReal.smul_def, Complex.real_smul, ← mul_assoc, NNReal.coe_inv,
        Complex.ofReal_inv, inv_mul_cancel₀ hc0, one_mul]
  refine ⟨fun μ _ m _ => ?_, fun μ _ ν _ => ?_, fun ν _ m _ => ?_⟩
  · obtain ⟨c, hc, h, -, -⟩ := main μ Measure.haar m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, h, -⟩ := main μ ν Measure.haar
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ hc, h⟩
  · obtain ⟨c, hc, -, -, h⟩ := main Measure.haar ν m
    exact ⟨_, Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hc), h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem orbit_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) (x : G) (ho : IsOpen (J : Set G)) (hc : IsCompact (J : Set G)) :
    {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite := by
  have hd : DiscreteTopology (G ⧸ J) := by
    refine discreteTopology_iff_isOpen_singleton.2 fun c => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    have himg : ({(QuotientGroup.mk g : G ⧸ J)} : Set (G ⧸ J)) =
        QuotientGroup.mk '' ((fun h => g⁻¹ * h) ⁻¹' (J : Set G)) := by
      ext c
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
      simp only [Set.mem_singleton_iff, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
      constructor
      · intro e
        exact ⟨g * (g⁻¹ * h), by simpa using QuotientGroup.eq.1 e.symm, by simp⟩
      · rintro ⟨a, ha, e⟩
        rw [← e]
        exact (QuotientGroup.eq.2 ha).symm
    rw [himg]
    exact QuotientGroup.isOpenMap_coe _ (ho.preimage (by fun_prop))
  have hS : {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} =
      (fun k => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
    exact ⟨fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩, fun ⟨k, hk, e⟩ => ⟨k, hk, e.symm⟩⟩
  rw [hS]
  exact (hc.image ((QuotientGroup.continuous_mk).comp (continuous_id.mul continuous_const))).finite_of_discrete

private theorem norm_le_one_of_adj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →L[ℂ] H) (h : ContinuousLinearMap.adjoint A = B) (hBA : B ∘L A = 1) :
    ‖A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have h1 : ⟪A v, A v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, h]
    have : B (A v) = v := by
      have := congrArg (fun S : H →L[ℂ] H => S v) hBA
      simpa using this
    rw [this]
  have h2 : ‖A v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h1]
  have h3 : ‖A v‖ = ‖v‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
  rw [h3, one_mul]

private theorem hop_abs {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : G → H →L[ℂ] H) (hmul : ∀ g h, ρ (g * h) = ρ g ∘L ρ h)
    (hnorm : ∀ g, ‖ρ g‖ ≤ 1) (J : Subgroup G) (x : G) (V : Submodule ℂ H)
    (hfix : ∀ v, v ∈ V ↔ ∀ k ∈ J, ρ k v = v) (a1 : ∀ v, prj V v ∈ V) (a2 : ∀ v ∈ V, prj V v = v)
    (hP : ‖prj V‖ ≤ 1)
    (hTP : ∀ T : H →L[ℂ] H, (∀ g, Commute T (ρ g)) → Commute T (prj V))
    (S : Set (G ⧸ J)) (hSd : S = {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)})
    (hS : S.Finite) (A : H →L[ℂ] H) (hA : A = (∑ᶠ c ∈ S, ρ c.out) ∘L prj V) :
    (∀ v, A v ∈ V) ∧ A ∘L prj V = A ∧
      (∀ (ι : Type) [Fintype ι] (y : ι → G),
        Function.Injective (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) →
        Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) = S →
        ∀ v ∈ V, A v = ∑ i, ρ (y i) v) ∧
      (∀ T : H →L[ℂ] H, (∀ g, Commute T (ρ g)) → Commute T A) ∧
      ‖A‖ ≤ S.ncard := by
  classical
  have hB : (∑ᶠ c ∈ S, ρ c.out) = ∑ c ∈ hS.toFinset, ρ c.out :=
    finsum_mem_eq_finite_toFinset_sum _ hS
  rw [hB] at hA
  have hkey : ∀ (y : G) (c : G ⧸ J), (QuotientGroup.mk y : G ⧸ J) = c → ∀ v ∈ V,
      ρ c.out v = ρ y v := by
    rintro y _ rfl v hv
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J y
    rw [hj, hmul, ContinuousLinearMap.comp_apply, (hfix v).1 hv j j.2]
  have hsm : ∀ k ∈ J, ∀ c ∈ S, k • c ∈ S := by
    subst hSd
    rintro k hk _ ⟨k', hk', rfl⟩
    exact ⟨k * k', J.mul_mem hk hk', by rw [mul_assoc]; rfl⟩
  have hApply : ∀ v, A v = ∑ c ∈ hS.toFinset, ρ c.out (prj V v) := fun v => by
    rw [hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
  have hinv : ∀ v, A v ∈ V := by
    intro v
    rw [hfix]
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hApply, map_sum]
    refine Finset.sum_equiv (MulAction.toPerm k) (fun c => ?_) (fun c _ => ?_)
    · simp only [Set.Finite.mem_toFinset, MulAction.toPerm_apply]
      refine ⟨hsm k hk c, fun h => ?_⟩
      simpa using hsm k⁻¹ (J.inv_mem hk) _ h
    · have := hkey (k * c.out) (k • c) (by
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl) _ (a1 v)
      simp only [MulAction.toPerm_apply]
      rw [this, hmul, ContinuousLinearMap.comp_apply]
  have hAP : A ∘L prj V = A := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, hApply, hApply, a2 _ (a1 v)]
  refine ⟨hinv, hAP, ?_, ?_, ?_⟩
  · intro ι _ y hy hr v hv
    have hF : hS.toFinset = Finset.univ.image (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) := by
      ext c
      have hc : c ∈ S ↔ c ∈ Set.range (fun i => (QuotientGroup.mk (y i) : G ⧸ J)) := by rw [hr]
      simpa using hc
    rw [hApply, a2 v hv, hF, Finset.sum_image (fun a _ b _ h => hy h)]
    exact Finset.sum_congr rfl fun i _ => hkey (y i) _ rfl v hv
  · intro T hT
    rw [hA]
    exact (Commute.sum_right _ _ _ fun c _ => hT _).mul_right (hTP T hT)
  · rw [hA]
    calc ‖(∑ c ∈ hS.toFinset, ρ c.out) ∘L prj V‖
        ≤ ‖∑ c ∈ hS.toFinset, ρ c.out‖ * ‖prj V‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖∑ c ∈ hS.toFinset, ρ c.out‖ * 1 := by gcongr
      _ = ‖∑ c ∈ hS.toFinset, ρ c.out‖ := mul_one _
      _ ≤ ∑ c ∈ hS.toFinset, (1 : ℝ) := norm_sum_le_of_le _ fun c _ => hnorm _
      _ = S.ncard := by
        rw [Set.ncard_eq_toFinset_card S hS]
        simp

theorem UpperTheory.ConvolutionTheory.Tf.hopBasic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)),
      IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) →
      {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.Finite ∧
      (∀ v, Hop μ w J x v ∈ fixL μ w J) ∧ Hop μ w J x ∘L prj (fixL μ w J) = Hop μ w J x ∧
      (∀ (ι : Type) [Fintype ι] (y : ι → GL (Fin n) (w.adicCompletion K)), Function.Injective (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) →
        Set.range (fun i => (QuotientGroup.mk (y i) : GL (Fin n) (w.adicCompletion K) ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} →
        ∀ v ∈ fixL μ w J, Hop μ w J x v = ∑ i, rhoL μ w (y i) v) ∧
      (∀ T : LL μ →L[ℂ] LL μ, (∀ g, Commute T (rhoL μ w g)) → Commute T (Hop μ w J x)) ∧
      ‖Hop μ w J x‖ ≤ {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}.ncard := by
  intro K _ _ n μ _ w J x ho hc
  obtain ⟨-, hmem, a1, a2, -, hmul, hone, hadj, hT⟩ :=
    UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))
  have hfin := orbit_finite J x ho hc
  have hfix : ∀ v, v ∈ fixL μ w J ↔ ∀ k ∈ J, rhoL μ w k v = v := fun v => by
    unfold fixL
    rw [hmem]
    constructor
    · exact fun h k hk => h _ (Subgroup.mem_map_of_mem _ hk)
    · rintro h _ ⟨k, hk, rfl⟩
      exact h k hk
  have hρ : ∀ g h, rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := fun g h => by
    simp only [rhoL, map_mul, hmul]
  have hnorm : ∀ g, ‖rhoL μ w g‖ ≤ 1 := fun g => by
    refine norm_le_one_of_adj _ (rhoF μ (AdelicGLn.localEmbedding w g)⁻¹) (hadj _) ?_
    unfold rhoL
    rw [← hmul, inv_mul_cancel, hone]
  have hP : ‖prj (fixL μ w J)‖ ≤ 1 := by
    unfold prj
    exact Submodule.starProjection_norm_le _
  have hTP : ∀ T : LL μ →L[ℂ] LL μ, (∀ g, Commute T (rhoL μ w g)) → Commute T (prj (fixL μ w J)) := by
    intro T h
    refine hT T ?_
    rintro _ ⟨k, -, rfl⟩
    exact h k
  obtain ⟨b1, b2, b3, b4, b5⟩ := hop_abs (rhoL μ w) hρ hnorm J x (fixL μ w J) hfix a1 a2 hP hTP _ rfl hfin
    (Hop μ w J x) rfl
  exact ⟨hfin, b1, b2, b3, b4, b5⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LeftSm
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open GroundTheory.Global
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise ContDiff Manifold

section
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_avg {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasureOnCompacts ρ]
    {z : S → G} (hz : Continuous z) {β : G → ℂ} (hβ : h.IsSmoothFun β) (y : G)
    (hs : ∀ C : Set G, IsCompact C → ∃ D : Set S, IsCompact D ∧ ∀ a ∈ C, ∀ s ∉ D, β (a * y * z s) = 0) :
    h.IsSmoothFun (fun A => ∫ s, β (A * y * z s) ∂ρ) := by
  rw [h.isSmoothFun_iff]
  intro g
  set ψ : 𝔤 → G → ℂ := fun Y w => β (g * h.expG Y * w) with hψdef
  have hψ : ∀ w₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (w₀ * h.expG q.2)) := by
    intro w₀
    let := h.chartedSpace
    have := h.lieGroup ∞
    have hm : ContMDiff 𝓘(ℝ, 𝔤 × 𝔤) 𝓘(ℝ, 𝔤) ∞
        (fun q : 𝔤 × 𝔤 => g * h.expG q.1 * (w₀ * h.expG q.2)) :=
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst)).mul
        (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_snd))
    exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hβ hm).contDiff
  set F : 𝔤 → S → ℂ := fun Y s => ψ Y (y * z s) with hFdef
  have e : (fun Y : 𝔤 => ∫ s, β (g * h.expG Y * y * z s) ∂ρ) = fun Y => ∫ s, F Y s ∂ρ := by
    funext Y
    congr 1
    simp only [hFdef, hψdef, mul_assoc]
  show ContDiff ℝ ∞ (fun Y : 𝔤 => ∫ s, β (g * h.expG Y * y * z s) ∂ρ)
  rw [e]
  refine contDiff_integral_of_iteratedFDeriv F (fun s => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · have e2 : (fun Y => F Y s) =
        (fun q : 𝔤 × 𝔤 => ψ q.1 ((y * z s) * h.expG q.2)) ∘ fun Y => (Y, (0 : 𝔤)) := by
      funext Y
      simp only [Function.comp_apply, h.expG_zero, mul_one, hFdef]
    rw [e2]
    exact (hψ _).comp (contDiff_id.prodMk contDiff_const)
  · exact (h.continuous_iteratedFDeriv_param ψ hψ k).comp
      (continuous_fst.prodMk (continuous_const.mul (hz.comp continuous_snd)))
  · obtain ⟨D, hD, hDz⟩ := hs ((fun Y => g * h.expG Y) '' Metric.closedBall Y₀ 1)
      ((isCompact_closedBall Y₀ 1).image (continuous_const.mul h.continuous_expG))
    refine ⟨Metric.closedBall Y₀ 1, Metric.closedBall_mem_nhds Y₀ one_pos, D, hD, fun Y hY s hsD => ?_⟩
    have h0 := hDz _ ⟨Y, hY, rfl⟩ s hsD
    simpa only [hFdef, hψdef, mul_assoc] using h0

end

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_inv (f : {r : ℝ // 0 < r} → ℂ) :
    ∫ s, f s⁻¹ ∂posRealMeasure = ∫ s, f s ∂posRealMeasure := by
  have hm : MeasurableEmbedding expPos := expPosHomeomorph.measurableEmbedding
  have hi : ∀ x, (expPos x)⁻¹ = expPos (-x) := fun x => by
    apply Subtype.ext
    simp [Real.exp_neg]
  rw [posRealMeasure_eq_map_expPos, hm.integral_map, hm.integral_map]
  simp_rw [hi]
  exact integral_neg_eq_self (fun x => f (expPos x)) volume

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_kbar {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (hβ : SmoothT β) (y : archGroup K n) :
    (isExpLieAlgebra K n).IsSmoothFun fun A : archGroup K n => kbar β (A * y) := by
  refine UpperTheory.ConvolutionTheory.Tf.leftSm_avg (isExpLieAlgebra K n) posRealMeasure continuous_zInf hβ y ?_
  intro C hC
  have hD : IsCompact (detA K n '' tsupport β) := β.hasCompactSupport.isCompact.image continuous_detA
  have hR : IsCompact (detA K n '' ((fun a => a * y) '' C)) :=
    (hC.image (continuous_id.mul continuous_const)).image continuous_detA
  refine ⟨(fun p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r} => p.1 * p.2⁻¹) ''
    ((detA K n '' tsupport β) ×ˢ (detA K n '' ((fun a => a * y) '' C))),
    (hD.prod hR).image (continuous_fst.mul continuous_snd.inv), fun a ha s hs => ?_⟩
  by_contra hne
  apply hs
  refine ⟨(s * detA K n (a * y), detA K n (a * y)),
    ⟨mem_of_kernel_ne_zero hn hne, _, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  simp only [mul_inv_cancel_right]

theorem UpperTheory.ConvolutionTheory.Tf.leftSm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n),
      (SmoothT β → (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ u ∈ U, ∀ h, e (u * h) = e h) → IsLeftSmooth (tens β e)) ∧
      ∀ (β' : TI K n) (e' : TF K n), (∀ a, β' a = conj (β a⁻¹)) → (∀ h, e' h = conj (e h⁻¹)) →
        CuspidalProjection.ccStar (tens β e) = tens β' e' := by
  intro K _ _ n hn β e
  have hT : ∀ (β : TI K n) (e : TF K n) x, tens β e x = tensFun β e x :=
    fun β e => (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1
  refine ⟨fun hβ ⟨U, hUo, hU⟩ => ⟨fun x => ?_, ?_⟩, fun β' e' hβ' he' => ?_⟩
  · have e1 : (fun A : archGroup K n => tens β e (archP K n A * x)) = fun A =>
        e (finPart K n (x : AdelicGLn.AdelicGL K n)) • kbar β (A * infPart K n (x : AdelicGLn.AdelicGL K n)) := by
      funext A
      have hk : kbar β (A * (zInf K n (detA K n A))⁻¹ * infPart K n (x : AdelicGLn.AdelicGL K n)) =
          kbar β (A * infPart K n (x : AdelicGLn.AdelicGL K n)) := by
        rw [← map_inv, mul_assoc, zInf_mul_comm, ← mul_assoc, kbar_mul_zInf]
      rw [hT, tensFun, Subgroup.coe_mul, map_mul, map_mul, infPart_archP, finPart_archP, one_mul, hk,
        smul_eq_mul, mul_comm]
    rw [e1]
    exact ((isExpLieAlgebra K n).smoothFuns (F := ℂ)).smul_mem _ (UpperTheory.ConvolutionTheory.Tf.leftSm_kbar hn β hβ _)
  · refine ⟨U.comap (AdelicGLn.integralFiniteGL K n).subtype, hUo.preimage continuous_subtype_val,
      fun u hu x => ?_⟩
    rw [hT, hT, tensFun, tensFun, Subgroup.coe_mul, coe_finOne, map_mul, map_mul, infPart_finEmb,
      finPart_finEmb, one_mul, hU (u : AdelicGLn.FiniteAdelicGL K n) hu]
  · have zInf_inv_comm : ∀ (s : {r : ℝ // 0 < r}) (a : archGroup K n), (zInf K n s)⁻¹ * a = a * (zInf K n s)⁻¹ := by
      intro s a
      rw [← map_inv, zInf_mul_comm]
    have hk : ∀ a, kbar β' a = conj (kbar β a⁻¹) := by
      intro a
      unfold kbar
      rw [← integral_conj, ← UpperTheory.ConvolutionTheory.Tf.leftSm_inv (fun s => conj (β (a⁻¹ * zInf K n s)))]
      congr 1
      funext s
      rw [hβ', map_inv (zInf K n) s, mul_inv_rev, zInf_inv_comm]
    ext g
    rw [CuspidalProjection.ccStar_apply, hT, hT, tensFun, tensFun, map_mul, he', hk, Subgroup.coe_inv,
      map_inv, map_inv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

attribute [-instance] GlobalTheory.SplitFlip.t2Space_general_linear_group GlobalTheory.SplitFlip.secondCountable_GL in
theorem UpperTheory.ConvolutionTheory.Tf.prjFix :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
      IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)) →
      ∃ e : TF K n, (∀ h, e h = (U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹) h) ∧ Ofin μ m e = prj (fixF μ U) := by
  intro K _ _ n μ _ m _ U hUo hUc
  have hcl : IsClopen (U : Set (AdelicGLn.FiniteAdelicGL K n)) := ⟨U.isClosed_of_isOpen hUo, hUo⟩
  have hpos : (m.real U : ℝ) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hUo.measure_pos m ⟨1, U.one_mem⟩).ne', hUc.measure_lt_top.ne⟩
  obtain ⟨-, hmem, a1, a2, a3, hmul, -, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  let e : TF K n := ⟨⟨(U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹),
    hcl.continuous_indicator continuous_const⟩,
    HasCompactSupport.intro hUc fun x hx => Set.indicator_of_notMem hx (fun _ => ((m.real U : ℝ) : ℂ)⁻¹)⟩
  have he : ∀ h, e h = (U : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (fun _ => ((m.real U : ℝ) : ℂ)⁻¹) h :=
    fun _ => rfl
  refine ⟨e, he, ContinuousLinearMap.ext fun v => ?_⟩
  have hO : Ofin μ m e v = ∫ h, e h • rhoF μ h v ∂m := by
    unfold Ofin
    rw [UnitaryRep.integrated_ccToL1_apply]
    rfl
  have hint : Integrable (fun h => e h • rhoF μ h v) m :=
    (e.continuous.smul (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).continuous_orbit v).comp
      MultiplicityOne.continuous_finProj)).integrable_of_hasCompactSupport e.hasCompactSupport.smul_right
  have h1 : Ofin μ m e v ∈ fixF μ U := by
    rw [hmem]
    intro u hu
    rw [hO, ← ContinuousLinearMap.integral_comp_comm _ hint,
      ← integral_mul_left_eq_self (fun h => e h • rhoF μ h v) u]
    congr 1
    funext h
    have : e (u * h) = e h := by
      rw [he, he]
      by_cases hh : h ∈ U
      · rw [Set.indicator_of_mem (show u * h ∈ (U : Set _) from U.mul_mem hu hh), Set.indicator_of_mem (show h ∈ (U : Set _) from hh)]
      · rw [Set.indicator_of_notMem (show u * h ∉ (U : Set _) from fun h' => hh ((U.mul_mem_cancel_left hu).1 h')),
          Set.indicator_of_notMem (show h ∉ (U : Set _) from hh)]
    rw [this, hmul, map_smul, ContinuousLinearMap.comp_apply]
  rw [← a2 _ h1, hO, ← ContinuousLinearMap.integral_comp_comm _ hint]
  have h2 : (fun h => prj (fixF μ U) (e h • rhoF μ h v)) = fun h => e h • prj (fixF μ U) v := by
    funext h
    rw [map_smul, he]
    by_cases hh : h ∈ U
    · rw [← ContinuousLinearMap.comp_apply, (a3 h hh).2]
    · rw [Set.indicator_of_notMem (show h ∉ (U : Set _) from hh), zero_smul, zero_smul]
  rw [h2, integral_smul_const]
  simp only [he]
  rw [integral_indicator_const _ hUo.measurableSet, Complex.real_smul, mul_inv_cancel₀ (by exact_mod_cast hpos), one_smul]
end

