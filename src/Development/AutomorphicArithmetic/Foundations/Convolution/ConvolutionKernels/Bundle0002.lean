module

public import GroundTheory.AutomorphicForms.TraceClass
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.HsOfKer
section
open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_countable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [TopologicalSpace.SeparableSpace H] {ι : Type*} {b : ι → H}
    (hb : Orthonormal ℂ b) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2)) ?_
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.2 (by norm_num))
  intro i j hij
  refine Metric.ball_disjoint_ball ?_
  have h0 : ⟪b i, b j⟫_ℂ = 0 := hb.2 hij
  have h := norm_sub_sq (𝕜 := ℂ) (b i) (b j)
  rw [h0, hb.1 i, hb.1 j] at h
  simp only [map_zero] at h
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (b i - b j)]

private theorem UpperTheory.ConvolutionTheory.K.hsOfKer_sq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {E : Type*} [NormedAddCommGroup E] (f : X → E) (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem UpperTheory.ConvolutionTheory.K.hsOfKer :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
      (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k : X → Lp ℂ 2 ν), MemLp k 2 ν →
      (∀ φ, (A φ : X → ℂ) =ᵐ[ν] fun x => ⟪k x, φ⟫_ℂ) → IsHilbertSchmidt A := by
  intro X _ ν _ _ A k hk hA
  let b := stdHilbertBasis ℂ (Lp ℂ 2 ν)
  haveI := UpperTheory.ConvolutionTheory.K.hsOfKer_countable b.orthonormal
  rw [isHilbertSchmidt_iff b]
  have h1 : ∀ i, ‖A (b i)‖ₑ ^ 2 = ∫⁻ x, ‖⟪b i, k x⟫_ℂ‖ₑ ^ 2 ∂ν := by
    intro i
    rw [Lp.enorm_def, eLpNorm_congr_ae (hA (b i)),
      UpperTheory.ConvolutionTheory.K.hsOfKer_sq _ _ (hk.aestronglyMeasurable.inner aestronglyMeasurable_const)]
    simp only [enorm_inner_comm (k _)]
  simp only [h1]
  rw [← lintegral_tsum]
  · simp only [← enorm_sq_eq_tsum b]
    rw [← UpperTheory.ConvolutionTheory.K.hsOfKer_sq ν k hk.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hk
  · intro i
    exact ((aestronglyMeasurable_const.inner hk.aestronglyMeasurable).enorm).pow_const 2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QmapPres
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.RightCosetSpace

theorem UpperTheory.ConvolutionTheory.K.qmapPres :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
      (μ : Measure G) [μ.IsHaarMeasure] (e : G ≃ₜ* G), (∀ g, e g ∈ Γ ↔ g ∈ Γ) → MeasurePreserving e μ μ →
      (∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x)) ∧
      MeasurePreserving (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) (quotientMeasure Γ μ) (quotientMeasure Γ μ) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ e hΓ he
  have h1 : ∀ x : G, mk Γ (e (Quotient.out (mk Γ x))) = mk Γ (e x) := by
    intro x
    have h0 : mk Γ (Quotient.out (mk Γ x)) = mk Γ x := Quotient.out_eq _
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 h0
    rw [← hγ]
    change mk Γ (e ((γ : G) * x)) = _
    rw [map_mul]
    exact mk_mul_of_mem ((hΓ _).2 γ.2) _
  have hcomm : (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ = mk Γ ∘ e :=
    funext h1
  have hm : Measurable (fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) := by
    rw [measurable_from_quotient]
    change Measurable ((fun y : RightCosetSpace Γ => mk Γ (e (Quotient.out y))) ∘ mk Γ)
    rw [hcomm]
    exact (measurable_mk Γ).comp he.measurable
  refine ⟨h1, hm, ?_⟩
  let ε : Γ → Γ := fun γ => ⟨e.symm γ, (hΓ _).1 (by simpa using γ.2)⟩
  have hε : Function.Bijective ε := by
    constructor
    · intro a b hab
      exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
    · intro b
      exact ⟨⟨e b, (hΓ _).2 b.2⟩, Subtype.ext (by simp [ε])⟩
  have hF' : IsFundamentalDomain Γ (e ⁻¹' fundamentalDomain Γ) μ :=
    (isFundamentalDomain_fundamentalDomain Γ μ).preimage_of_equiv
      he.quasiMeasurePreserving (e := ε) hε fun γ x => by
        change e (e.symm γ * x) = (γ : G) * e x
        simp
  have key := map_restrict_eq_quotientMeasure μ hF'
  conv_lhs => rw [← key]
  rw [Measure.map_map hm (measurable_mk Γ), hcomm, ← Measure.map_map (measurable_mk Γ) he.measurable,
    ← Measure.restrict_map he.measurable (measurableSet_fundamentalDomain Γ), he.map_eq]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TraceKer
section
open MeasureTheory GroundTheory.Automorphic
open scoped InnerProductSpace

private theorem lintegral_sq_ne_top {X H : Type} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup H] {u : X → H} (hu : MemLp u 2 ν) : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  have h := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num) hu
  simpa using h.ne

private theorem parseval_integral {X H ι : Type} [MeasurableSpace X] {ν : Measure X}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Countable ι]
    (b : HilbertBasis ι ℂ H) {u v : X → H} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    ∑' i, ∫ x, ⟪u x, b i⟫_ℂ * ⟪b i, v x⟫_ℂ ∂ν = ∫ x, ⟪u x, v x⟫_ℂ ∂ν := by
  have hm : ∀ i, AEStronglyMeasurable (fun x => ⟪u x, b i⟫_ℂ * ⟪b i, v x⟫_ℂ) ν := fun i =>
    (hu.aestronglyMeasurable.inner aestronglyMeasurable_const).mul
      (aestronglyMeasurable_const.inner hv.aestronglyMeasurable)
  rw [← integral_tsum hm]
  · simp only [b.tsum_inner_mul_inner]
  · rw [← lintegral_tsum fun i => (hm i).enorm]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, (‖u x‖ₑ ^ 2 + ‖v x‖ₑ ^ 2) ∂ν) ?_ (lintegral_mono fun x => ?_)
    · rw [lintegral_add_left' (hu.aestronglyMeasurable.enorm.pow_const 2)]
      exact ENNReal.add_ne_top.2 ⟨lintegral_sq_ne_top hu, lintegral_sq_ne_top hv⟩
    · rw [enorm_sq_eq_tsum b (u x), enorm_sq_eq_tsum b (v x), ← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun i => ?_
      rw [enorm_mul, enorm_inner_comm (u x)]
      exact ennreal_mul_le_sq_add_sq _ _

theorem UpperTheory.ConvolutionTheory.K.traceKer :
    ∀ {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
      (A M B : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (k₁ k₂ : X → Lp ℂ 2 ν), MemLp k₁ 2 ν → MemLp k₂ 2 ν →
      IsHilbertSchmidt A → IsHilbertSchmidt B →
      (∀ φ, (A φ : X → ℂ) =ᵐ[ν] fun x => ⟪k₁ x, φ⟫_ℂ) →
      (∀ φ, (ContinuousLinearMap.adjoint B φ : X → ℂ) =ᵐ[ν] fun x => ⟪k₂ x, φ⟫_ℂ) →
      trace (A ∘L M ∘L B) = ∫ x, ⟪k₁ x, M (k₂ x)⟫_ℂ ∂ν := by
  intro X _ ν _ _ A M B k₁ k₂ h₁ h₂ hA hB eA eB
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 ν)
  have : Countable w := Formalism.MainNotions.LeviCoordinates.rrd_countable b.orthonormal
  have hMB : IsHilbertSchmidt (M ∘L B) := hB.comp_left M
  have h0 : trace (A ∘L M ∘L B) = ∑' i, ⟪b i, (M ∘L B) (A (b i))⟫_ℂ :=
    (hasSum_inner_comp_comm (stdHilbertBasis ℂ (Lp ℂ 2 ν)) b hA hMB).tsum_eq
  rw [h0, ← parseval_integral b (v := fun x => M (k₂ x)) h₁ (M.comp_memLp' h₂)]
  refine tsum_congr fun i => ?_
  rw [ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint_inner_left M, ← ContinuousLinearMap.adjoint_inner_left B,
    L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [eA (b i), eB (ContinuousLinearMap.adjoint M (b i))] with x hx hy
  rw [hx, hy, RCLike.inner_apply, inner_conj_symm, ContinuousLinearMap.adjoint_inner_left]
end

