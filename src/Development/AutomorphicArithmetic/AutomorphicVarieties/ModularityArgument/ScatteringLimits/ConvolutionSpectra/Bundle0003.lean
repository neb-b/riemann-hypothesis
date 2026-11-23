module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.convAdj :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → Ker (sharp κ) ∧ ContinuousLinearMap.adjoint (conv κ) = conv (sharp κ) ∧
      ∀ z : ℂ, symb (sharp κ) z = ContinuousLinearMap.adjoint (symb κ (-conj z)) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have hs : Ker (sharp κ) := by
    refine ⟨(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).continuous.comp (hk.1.comp continuous_neg), ?_⟩
    exact (hk.2.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun A : V →L[ℂ] W => ContinuousLinearMap.adjoint A) (map_zero _)
  refine ⟨hs, ?_, fun z => ?_⟩
  · refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v u => ?_).symm
    rw [(convSpec _ hk u).2.2, (convSpec _ hs v).2.2, ← integral_inner (convSpec _ hk u).2.1, ← inner_conj_symm,
      ← integral_inner (convSpec _ hs v).2.1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [inner_conj_symm]
    rw [L2.inner_def, L2.inner_def, ← integral_add_right_eq_self _ t]
    refine integral_congr_ae ?_
    have q := (measurePreserving_add_right volume t).quasiMeasurePreserving
    filter_upwards [q.ae ((sharp κ (-t)).coeFn_compLpL (sh W (-t) v)), q.ae (sh_ae W (-t) v), (κ t).coeFn_compLpL (sh V t u),
      sh_ae V t u] with x a b c d
    rw [a, b, c, d, add_neg_cancel_right, sharp, neg_neg, ContinuousLinearMap.adjoint_inner_left]
  · have hi : ∀ {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
        [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
        (k : ℝ → A →L[ℂ] B), Ker k → ∀ z : ℂ, Integrable fun t : ℝ => Complex.exp (z * t) • k t := fun k hk z =>
      (Continuous.smul (f := fun t : ℝ => Complex.exp (z * t)) (by fun_prop) hk.1).integrable_of_hasCompactSupport hk.2.smul_left
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun v u => ?_
    rw [symb, symb, ContinuousLinearMap.integral_apply (hi _ hs _), ContinuousLinearMap.integral_apply (hi _ hk _),
      ← integral_inner ((hi _ hk _).apply_continuousLinearMap u), ← inner_conj_symm,
      ← integral_inner ((hi _ hs _).apply_continuousLinearMap v), ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right, map_mul, inner_conj_symm, sharp, neg_neg,
      ContinuousLinearMap.adjoint_inner_left, ← Complex.exp_conj, Complex.conj_ofReal]
    congr 2
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem ker_bd {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {κ : ℝ → V →L[ℂ] W} (h : HasCompactSupport κ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.exists_norm_le
  refine ⟨|R|, abs_nonneg _, fun t ht => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  exact absurd ((hR t hm).trans (le_abs_self R)) (not_le.2 ht)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convLaws :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → (∀ a : ℝ, conv κ ∘L sh V a = sh W a ∘L conv κ) ∧
      (∀ ρ T : ℝ, (∀ t, ρ < |t| → κ t = 0) → cut W (Ioi (T + ρ)) ∘L conv κ ∘L cut V (Iic T) = 0) ∧
      ∀ p : L V, Bdd p → Bdd (conv κ p) ∧ ∫ x, conv κ p x = symb κ 0 (∫ x, p x) := by
  intro V _ _ _ _ W _ _ _ _ κ hk
  have q : ∀ x : ℝ, Measure.QuasiMeasurePreserving (fun t : ℝ => x + t) volume volume :=
    fun x => (measurePreserving_add_left volume x).quasiMeasurePreserving
  refine ⟨fun a => ?_, fun ρ T hρ => ?_, fun p ⟨ρ, hp⟩ => ?_⟩
  · ext1 u
    refine Lp.ext ?_
    filter_upwards [(convSpec κ hk (sh V a u)).1, sh_ae W a (conv κ u),
      (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (convSpec κ hk u).1] with x h1 h2 h3
    simp only [ContinuousLinearMap.comp_apply]
    rw [h1, h2, h3]
    refine integral_congr_ae ?_
    filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) (sh_ae V a u)] with t ht
    rw [ht, add_right_comm]
  · ext1 u
    have c1 := (cutLaws (V := W) (Iic (T + ρ)) (Ioi (T + ρ)) measurableSet_Iic measurableSet_Ioi).2.2.2.2.2.2.2.1
    have c2 := cutLaws (V := W) (Ioi (T + ρ)) (Iic (T + ρ)) measurableSet_Ioi measurableSet_Iic
    have c3 := cutLaws (V := V) (Iic T) (Iic T) measurableSet_Iic measurableSet_Iic
    have h0 := (c3.2.2.2.2.2.2.2.1 (cut V (Iic T) u)).1 (by
      have := DFunLike.congr_fun c3.1 u
      rwa [inter_self] at this)
    have h1 : cut W (Iic (T + ρ)) (conv κ (cut V (Iic T) u)) = conv κ (cut V (Iic T) u) := by
      refine (c1 _).2 ?_
      filter_upwards [(convSpec κ hk (cut V (Iic T) u)).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) h0] with t ht
      by_cases h : ρ < |t|
      · simp [hρ t h]
      · have h2 := (abs_le.1 (not_lt.1 h)).1
        rw [ht (by simp only [mem_Iic, not_le] at hx' ⊢; linarith), map_zero]; rfl
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
    rw [← h1]
    have := DFunLike.congr_fun c2.1 (conv κ (cut V (Iic T) u))
    rw [Ioi_inter_Iic, Ioc_self, c2.2.2.2.2.1] at this
    exact this
  · obtain ⟨R, -, hR⟩ := ker_bd hk.2
    have h0 := ((cutLaws (V := V) (Icc (-ρ) ρ) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 p).1 hp
    have hpi : Integrable (p : ℝ → V) := by
      have h1 : IntegrableOn (p : ℝ → V) (Icc (-ρ) ρ) := integrableOn_Lp_of_measure_ne_top p (by norm_num) measure_Icc_lt_top.ne
      refine ((integrable_indicator_iff measurableSet_Icc).2 h1).congr ?_
      filter_upwards [h0] with x hx
      by_cases h : x ∈ Icc (-ρ) ρ
      · rw [indicator_of_mem h]
      · rw [indicator_of_notMem h, hx h]
    refine ⟨⟨ρ + R, ((cutLaws (V := W) (Icc (-(ρ + R)) (ρ + R)) univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩
    · filter_upwards [(convSpec κ hk p).1] with x hx hx'
      rw [hx]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [Measure.QuasiMeasurePreserving.ae (q x) h0] with t ht
      by_cases h : R < |t|
      · simp [hR t h]
      · obtain ⟨h2, h3⟩ := abs_le.1 (not_lt.1 h)
        rw [ht fun hm => hx' ⟨by linarith [hm.1], by linarith [hm.2]⟩, map_zero]; rfl
    · have hk1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
      have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) :=
        (ContinuousLinearMap.apply ℂ W).flip.aestronglyMeasurable_comp₂ (hk.1.comp continuous_fst).aestronglyMeasurable
          ((Lp.stronglyMeasurable p).comp_measurable (measurable_snd.add measurable_fst)).aestronglyMeasurable
      have hI : Integrable (fun z : ℝ × ℝ => κ z.1 ((p : ℝ → V) (z.2 + z.1))) (volume.prod volume) := by
        refine (integrable_prod_iff hm).2 ⟨Eventually.of_forall fun t => (κ t).integrable_comp (hpi.comp_add_right t), ?_⟩
        refine (hk1.norm.mul_const (∫ x, ‖p x‖)).mono' hm.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_add_right_eq_self (fun x => ‖p x‖) t,
          ← integral_const_mul]
        exact integral_mono ((κ t).integrable_comp (hpi.comp_add_right t)).norm ((hpi.comp_add_right t).norm.const_mul _)
          fun x => (κ t).le_opNorm _
      rw [integral_congr_ae (convSpec κ hk p).1, ← integral_integral_swap (f := fun t x => κ t ((p : ℝ → V) (x + t))) hI, symb]
      simp only [zero_mul, Complex.exp_zero, one_smul]
      rw [ContinuousLinearMap.integral_apply hk1]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only
      rw [(κ t).integral_comp_comm (hpi.comp_add_right t), integral_add_right_eq_self]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLim
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutLim :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), (∀ T : ℝ, Tendsto (fun t => cut V (Ioi T) (sh V t u)) atTop (𝓝 0)) ∧
      ∀ a d : ℝ, 0 < d → HasSum (fun n : ℤ => cut V (Ioc (a + n * d) (a + (n + 1) * d)) u) u := by
  intro V _ _ _ _ u
  have hi : Integrable fun x => ‖u x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have key : ∀ {ι : Type} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] (s : ι → Set ℝ), (∀ i, MeasurableSet (s i)) →
      Antitone s → ⋂ i, s i = ∅ → [Nonempty ι] → Tendsto (fun i => ‖cut V (s i) u‖) atTop (𝓝 0) := by
    intro ι _ _ s hm ha he _
    have h1 := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖u x‖ ^ 2) hm ha ⟨Classical.arbitrary ι, hi.integrableOn⟩
    rw [he, setIntegral_empty] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun i => ?_
    rw [Function.comp_apply, ← (cutLaws (V := V) (s i) (s i) (hm i) (hm i)).2.2.2.2.2.2.2.2 u, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨fun T => ?_, fun a d hd => ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (key (fun t : ℝ => Ioi (T + t)) (fun _ => measurableSet_Ioi) (fun x y h => Ioi_subset_Ioi (by linarith)) ?_).congr fun t => ?_
    · refine eq_empty_of_forall_notMem fun x hx => ?_
      have := mem_iInter.1 hx (x - T)
      simp at this
    · have h := DFunLike.congr_fun ((cutLaws (V := V) (Ioi (T + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) u
      simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h
      rw [← h]; exact ((shF V).norm t _).symm
  · set I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d) with hI
    have hm : ∀ F : Finset ℤ, MeasurableSet (⋃ n ∈ F, I n) := fun F => F.measurableSet_biUnion fun _ _ => measurableSet_Ioc
    have hdis : Pairwise (Function.onFun Disjoint I) := by
      simpa [hI] using pairwise_disjoint_Ioc_add_zsmul a d
    have hun : ⋃ n, I n = univ := by simpa [hI] using iUnion_Ioc_add_zsmul hd a
    have hs : ∀ F : Finset ℤ, ∑ n ∈ F, cut V (I n) u = cut V (⋃ n ∈ F, I n) u := by
      intro F
      induction F using Finset.induction_on with
      | empty => simp [(cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.2.1]
      | insert n F hn ih =>
        rw [Finset.sum_insert hn, ih, Finset.set_biUnion_insert,
          (cutLaws (V := V) (I n) _ measurableSet_Ioc (hm F)).2.2.1, ContinuousLinearMap.add_apply]
        exact disjoint_iUnion₂_right.2 fun k hk => hdis fun e => hn (e ▸ hk)
    have h1 := key (fun F : Finset ℤ => (⋃ n ∈ F, I n)ᶜ) (fun F => (hm F).compl)
      (fun F G h => compl_subset_compl.2 (biUnion_subset_biUnion_left h)) (by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hun ▸ mem_univ x : x ∈ ⋃ n, I n)
        exact mem_iInter.1 hx {n} (by simpa using hn))
    rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
    refine h1.congr fun F => ?_
    obtain ⟨-, -, c3, c4, -⟩ := cutLaws (V := V) (⋃ n ∈ F, I n) (⋃ n ∈ F, I n)ᶜ (hm F) (hm F).compl
    have h2 := c3 disjoint_compl_right
    rw [union_compl_self, c4] at h2
    have h3 : u = cut V (⋃ n ∈ F, I n) u + cut V (⋃ n ∈ F, I n)ᶜ u := DFunLike.congr_fun h2 u
    rw [hs, norm_sub_rev, sub_eq_of_eq_add' h3]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResTail
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resTail :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (k : L V) (T : ℝ), cut V (Iic T) k = k → Tail (cut V (Ioi T) ((shF V).av wR k)) := by
  intro V _ _ _ _ k T hk
  obtain ⟨-, w1, w2, w3⟩ := avSpec (shF V)
  obtain ⟨a1, a2, -⟩ := w3 wR w1
  have cl := fun s t hs ht => cutLaws (V := V) s t hs ht
  refine ⟨Real.exp |T| * ‖k‖, fun ρ hρ => ?_⟩
  have e := DFunLike.congr_fun (cl (Icc (-ρ) ρ)ᶜ (Ioi T) measurableSet_Icc.compl measurableSet_Ioi).1 ((shF V).av wR k)
  rw [ContinuousLinearMap.comp_apply] at e
  rw [e]
  by_cases h : |T| ≤ ρ
  · have e2 : (Icc (-ρ) ρ)ᶜ ∩ Ioi T = Ioi ρ := by
      ext x
      have := abs_le.1 h
      simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioi, not_and_or, not_le]
      constructor
      · rintro ⟨h1 | h1, h2⟩ <;> linarith
      · exact fun h1 => ⟨Or.inr h1, by linarith⟩
    rw [e2, (a1 k).2]
    erw [← (cut V (Ioi ρ)).integral_comp_comm (a1 k).1]
    have ib : Integrable fun t => (Iic (T - ρ)).indicator Real.exp t * ‖k‖ :=
      ((integrable_indicator_iff measurableSet_Iic).2 (integrableOn_exp_Iic _)).mul_const _
    refine (norm_integral_le_of_norm_le ib (Eventually.of_forall fun t => ?_)).trans ?_
    · rw [map_smul, norm_smul]
      by_cases ht : t ≤ T - ρ
      · rw [indicator_of_mem (mem_Iic.2 ht)]
        refine mul_le_mul ?_ (((cl _ univ measurableSet_Ioi .univ).2.2.2.2.2.1 _).trans_eq ((shF V).norm t k)) (norm_nonneg _)
          (Real.exp_pos _).le
        refine (norm_indicator_le_norm_self _ _).trans_eq ?_
        simp
      · have h1 := DFunLike.congr_fun ((cl (Ioi (ρ + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) k
        simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h1
        have h2 := DFunLike.congr_fun (cl (Ioi (ρ + t)) (Iic T) measurableSet_Ioi measurableSet_Iic).1 k
        rw [ContinuousLinearMap.comp_apply, hk, Ioi_inter_Iic, Ioc_eq_empty (by linarith [not_le.1 ht]),
          (cl univ univ .univ .univ).2.2.2.2.1] at h2
        have h3 : cut V (Ioi ρ) ((shF V).U t k) = 0 := by
          show cut V (Ioi ρ) (sh V t k) = 0
          rw [← h1, h2]; simp
        rw [h3, indicator_of_notMem (by simpa using ht)]; simp
    · rw [integral_mul_const, integral_indicator measurableSet_Iic, integral_exp_Iic, mul_right_comm, ← Real.exp_add]
      gcongr
      linarith [le_abs_self T]
  · refine ((cl _ univ (measurableSet_Icc.compl.inter measurableSet_Ioi) .univ).2.2.2.2.2.1 _).trans ?_
    refine (((shF V).av wR).le_of_opNorm_le (a2.trans_eq w2) k).trans ?_
    rw [mul_right_comm, ← Real.exp_add]
    gcongr
    exact Real.one_le_exp (by linarith [not_le.1 h])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.SvSpec
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.svSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V], (∀ φ : ℝ → ℂ, MemLp φ 2 volume → ∀ e : V, (∀ᵐ x : ℝ, sv V φ e x = φ x • e) ∧ ‖sv V φ e‖ ^ 2 = (∫ x, ‖φ x‖ ^ 2) * ‖e‖ ^ 2) ∧
      ∀ e : V, (∀ᵐ x : ℝ, one V e x = (Ioc (0 : ℝ) 1).indicator (fun _ => e) x) ∧ Bdd (one V e) ∧ ∫ x, one V e x = e := by
  intro V _ _ _ _
  have h0 : ∀ φ : ℝ → ℂ, MemLp φ 2 volume → ∀ e : V, ∀ᵐ x : ℝ, sv V φ e x = φ x • e := by
    intro φ hφ
    have hc : ∀ e : V, ∀ᵐ x : ℝ, (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ) x = φ x • e := fun e => by
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ e).coeFn_compLpL (hφ.toLp φ), hφ.coeFn_toLp] with x h1 h2
      rw [h1, h2]; simp
    let A : V →ₗ[ℂ] L V :=
      { toFun := fun e => (ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ)
        map_add' := fun e f => Lp.ext (by
          filter_upwards [hc (e + f), hc e, hc f, Lp.coeFn_add ((ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ))
            ((ContinuousLinearMap.toSpanSingleton ℂ f).compLpL 2 volume (hφ.toLp φ))] with x h1 h2 h3 h4
          rw [h1, h4, Pi.add_apply, h2, h3, smul_add])
        map_smul' := fun c e => Lp.ext (by
          filter_upwards [hc (c • e), hc e, Lp.coeFn_smul c ((ContinuousLinearMap.toSpanSingleton ℂ e).compLpL 2 volume (hφ.toLp φ))]
            with x h1 h2 h4
          rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2, smul_comm]) }
    exact Classical.epsilon_spec (p := fun C : V →L[ℂ] L V => ∀ e, ∀ᵐ x : ℝ, C e x = φ x • e)
      ⟨LinearMap.toContinuousLinearMap A, hc⟩
  refine ⟨fun φ hφ e => ⟨h0 φ hφ e, ?_⟩, fun e => ?_⟩
  · obtain ⟨-, -, -, c4, -, -, -, -, c9⟩ := cutLaws (V := V) univ univ .univ .univ
    have := c9 (sv V φ e)
    rw [c4, Measure.restrict_univ] at this
    rw [← integral_mul_const]
    refine this.trans (integral_congr_ae ?_)
    filter_upwards [h0 φ hφ e] with x h
    rw [h, norm_smul, mul_pow]
  · have h1 : ∀ᵐ x : ℝ, one V e x = (Ioc (0 : ℝ) 1).indicator (fun _ => e) x := by
      filter_upwards [h0 _ (memLp_indicator_const (μ := volume) (s := Ioc (0 : ℝ) 1) 2 measurableSet_Ioc.nullMeasurableSet (1 : ℂ) (Or.inr (by simp : volume (Ioc (0 : ℝ) 1) ≠ ⊤))) e] with x h
      refine h.trans ?_
      by_cases b : x ∈ Ioc (0 : ℝ) 1 <;> simp [b]
    refine ⟨h1, ⟨1, ((cutLaws (V := V) _ univ measurableSet_Icc .univ).2.2.2.2.2.2.2.1 _).2 ?_⟩, ?_⟩
    · filter_upwards [h1] with x h hx
      rw [h, indicator_of_notMem fun (b : x ∈ Ioc (0 : ℝ) 1) => hx ⟨by linarith [b.1], b.2⟩]
    · rw [integral_congr_ae h1, integral_indicator measurableSet_Ioc]; simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TruncEq
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem prj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H) (T : ℝ) :
    let P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
    P * P = P ∧ IsSelfAdjoint P ∧ (∀ h, ∃ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) ∧ P h = J u) ∧
      ∀ u : L V, (∀ᵐ x : ℝ, x ≤ T → u x = 0) → P (J u) = J u := by
  intro P
  obtain ⟨c1, c2, -, -, -, -, -, c8, -⟩ := cutLaws (V := V) (Ioi T) (Ioi T) measurableSet_Ioi measurableSet_Ioi
  rw [inter_self] at c1
  have cc : ∀ u, cut V (Ioi T) (cut V (Ioi T) u) = cut V (Ioi T) u := fun u => DFunLike.congr_fun c1 u
  have jj : ∀ u, ContinuousLinearMap.adjoint J.toContinuousLinearMap (J u) = u := fun u => ext_inner_left ℂ fun v => by
    rw [ContinuousLinearMap.adjoint_inner_right]; exact J.inner_map_map v u
  have pa : ∀ h, P h = J (cut V (Ioi T) (ContinuousLinearMap.adjoint J.toContinuousLinearMap h)) := fun _ => rfl
  refine ⟨?_, ?_, fun h => ⟨_, ?_, pa h⟩, fun u hu => ?_⟩
  · ext h
    rw [ContinuousLinearMap.mul_apply, pa h, pa, jj, cc]
  · show ContinuousLinearMap.adjoint P = P
    simp only [P, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, c2.adjoint_eq, ContinuousLinearMap.comp_assoc]
  · exact ((c8 _).1 (cc _)).mono fun x hx h => hx (by simpa using h)
  · rw [pa, jj, (c8 u).2 (hu.mono fun x hx h => hx (by simpa using h))]

theorem UpperTheory.V.Z.IntegralApplyAeEq.truncEq :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (T : ℝ) (Λ : H →L[ℂ] H),
      (∀ u v, ⟪J (cut V (Ioi T) u), J' (cut W (Ioi T) v)⟫_ℂ = 0) → (IsTrunc J J' T Λ ↔
        Λ = 1 - J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap -
          J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ J J' T Λ ho
  obtain ⟨a1, a2, a3, a4⟩ := prj J T
  obtain ⟨b1, b2, b3, b4⟩ := prj J' T
  set P := J.toContinuousLinearMap ∘L cut V (Ioi T) ∘L ContinuousLinearMap.adjoint J.toContinuousLinearMap
  set P' := J'.toContinuousLinearMap ∘L cut W (Ioi T) ∘L ContinuousLinearMap.adjoint J'.toContinuousLinearMap
  have o1 : P * P' = 0 := by
    ext h
    refine ext_inner_left ℂ fun y => ?_
    rw [ContinuousLinearMap.mul_apply, ← a2.isSymmetric.apply_clm, ContinuousLinearMap.zero_apply, inner_zero_right]
    exact ho _ _
  have o2 : P' * P = 0 := by
    have := congrArg star o1
    rwa [star_mul, a2.star_eq, b2.star_eq, star_zero] at this
  have t0 : IsTrunc J J' T (1 - P - P') := by
    refine ⟨((IsSelfAdjoint.one _).sub a2).sub b2, ?_, fun h => ⟨fun hh => ?_, ?_⟩⟩
    · show (1 - P - P') * (1 - P - P') = _
      simp only [mul_sub, sub_mul, a1, b1, o1, o2, mul_one, one_mul]; abel
    · obtain ⟨u, hu, eu⟩ := a3 h
      obtain ⟨v, hv, ev⟩ := b3 h
      refine ⟨u, v, hu, hv, ?_⟩
      rw [← eu, ← ev]
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hh
      rw [sub_sub, sub_eq_zero] at hh
      exact hh
    · rintro ⟨u, v, hu, hv, rfl⟩
      have e1 : P (J' v) = 0 := by rw [← b4 v hv]; exact DFunLike.congr_fun o1 _
      have e2 : P' (J u) = 0 := by rw [← a4 u hu]; exact DFunLike.congr_fun o2 _
      simp [a4 u hu, b4 v hv, e1, e2]
  refine ⟨fun t1 => ?_, fun h => h ▸ t0⟩
  have key : ∀ A B : H →L[ℂ] H, IsTrunc J J' T A → IsTrunc J J' T B → A * B = A := fun A B hA hB => by
    ext h
    have h1 : B (h - B h) = 0 := by rw [map_sub, sub_eq_zero]; exact (DFunLike.congr_fun hB.2.1 h).symm
    have h2 := (hA.2.2 _).2 ((hB.2.2 _).1 h1)
    rw [map_sub, sub_eq_zero] at h2
    exact h2.symm
  have h1 := congrArg star (key _ _ t1 t0)
  rw [star_mul, t1.1.star_eq, t0.1.star_eq, key _ _ t0 t1] at h1
  exact h1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.WBound
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem layer (f : ℝ → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * f x) =
      ∫⁻ a, ENNReal.ofReal (2 * Real.exp (2 * a)) * ∫⁻ x in Ioi a, ENNReal.ofReal (f x) := by
  have e1 : ∀ x : ℝ, ENNReal.ofReal (Real.exp (2 * x)) = ∫⁻ a in Iio x, ENNReal.ofReal (2 * Real.exp (2 * a)) := fun x => by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_exp_mul_Iic two_pos x).const_mul 2) (Eventually.of_forall fun _ => by positivity), integral_const_mul,
      integral_exp_mul_Iic two_pos]
    congr 1; ring
  have m : Measurable fun z : ℝ × ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) z :=
    Measurable.indicator (by fun_prop) (measurableSet_lt measurable_snd measurable_fst)
  have := lintegral_lintegral_swap (μ := volume) (ν := volume) (f := fun x a : ℝ => {z : ℝ × ℝ | z.2 < z.1}.indicator
      (fun z => ENNReal.ofReal (2 * Real.exp (2 * z.2)) * ENNReal.ofReal (f z.1)) (x, a)) m.aemeasurable
  refine (lintegral_congr fun x => ?_).trans (this.trans (lintegral_congr fun a => ?_))
  · rw [ENNReal.ofReal_mul (Real.exp_pos _).le, e1, ← lintegral_mul_const _ (by fun_prop), ← lintegral_indicator measurableSet_Iio]
    rfl
  · rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ioi]
    rfl

theorem UpperTheory.V.Z.IntegralApplyAeEq.wBound :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (g : L V) (p : L W) (c Q : ℝ), (∀ a : ℝ, ‖cut V (Ioi a) g‖ ≤ ‖cut W (Iic (c - a)) p‖) → WLe (-2) p Q → WLe 2 g (Real.exp c * Q) := by
  intro V _ _ _ _ W _ _ _ _ g p c Q h ⟨hp1, hp2⟩
  have ig : Integrable fun x => ‖g x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have ip : Integrable fun x => ‖p x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable p)).1 (Lp.memLp p)
  have mg : Measurable fun x => ‖g x‖ ^ 2 := (Lp.stronglyMeasurable g).norm.measurable.pow_const 2
  have mp : Measurable fun x => ‖p x‖ ^ 2 := (Lp.stronglyMeasurable p).norm.measurable.pow_const 2
  have ip' : Integrable fun x => ‖p (c - x)‖ ^ 2 := ip.comp_sub_left c
  have h1 : ∀ a, ∫⁻ x in Ioi a, ENNReal.ofReal (‖g x‖ ^ 2) ≤ ∫⁻ x in Ioi a, ENNReal.ofReal (‖p (c - x)‖ ^ 2) := fun a => by
    rw [← ofReal_integral_eq_lintegral_ofReal ig.integrableOn (Eventually.of_forall fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal ip'.integrableOn (Eventually.of_forall fun _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ∫ x in Ioi a, ‖p (c - x)‖ ^ 2 = ∫ x in Iic (c - a), ‖p x‖ ^ 2 := by
      rw [← integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Iic,
        ← integral_sub_left_eq_self _ volume c]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases b : x ≤ c - a
      · simp [indicator, b, show a ≤ c - x by linarith]
      · simp [indicator, b, show ¬ a ≤ c - x from fun k => b (by linarith)]
    rw [e, ← (cutLaws (V := V) _ univ measurableSet_Ioi .univ).2.2.2.2.2.2.2.2,
      ← (cutLaws (V := W) _ univ measurableSet_Iic .univ).2.2.2.2.2.2.2.2]
    exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2
  have i2 : Integrable fun x => Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 := by
    refine ((hp1.comp_sub_left c).const_mul (Real.exp (2 * c))).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, ← Real.exp_add]; ring_nf
  have v2 : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 ≤ (Real.exp c * Q) ^ 2 := by
    have e : ∫ x, Real.exp (2 * x) * ‖p (c - x)‖ ^ 2 = Real.exp (2 * c) * ∫ x, Real.exp (-2 * x) * ‖p x‖ ^ 2 := by
      rw [← integral_sub_left_eq_self (fun x => Real.exp (-2 * x) * ‖p x‖ ^ 2) volume c, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [← mul_assoc, ← Real.exp_add]; ring_nf
    rw [e, mul_pow, ← Real.exp_nat_mul]
    exact mul_le_mul_of_nonneg_left hp2 (Real.exp_pos _).le
  have mp' : Measurable fun x => ‖p (c - x)‖ ^ 2 := mp.comp (measurable_const.sub measurable_id)
  have h2 : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * x) * ‖g x‖ ^ 2) ≤ ENNReal.ofReal ((Real.exp c * Q) ^ 2) := by
    refine le_trans ?_ (ENNReal.ofReal_le_ofReal v2)
    rw [ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun _ => by positivity), layer _ mg, layer _ mp']
    exact lintegral_mono fun a => mul_le_mul' le_rfl (h1 a)
  have m2 : Measurable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 := (by fun_prop : Measurable fun x : ℝ => Real.exp (2 * x)).mul mg
  have i3 : Integrable fun x => Real.exp (2 * x) * ‖g x‖ ^ 2 :=
    ⟨m2.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => by positivity)).2
      (h2.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨i3, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal i3 (Eventually.of_forall fun _ => by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
end

