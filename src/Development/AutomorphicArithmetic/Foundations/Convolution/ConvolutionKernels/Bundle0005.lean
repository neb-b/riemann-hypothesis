module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RconvEqIntegralKernel
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

section Kernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

private theorem hasCompactSupport_kernel (f : CompactlySupportedContinuousMap G ℂ) (a : G) :
    HasCompactSupport fun q => quotientKernel Γ f (mk Γ a, q) := by
  have hT : T2Space (RightCosetSpace Γ) := RightCosetSpace.t2Space Γ
  have hC : IsCompact (mk Γ '' ((a * ·) '' tsupport (f : G → ℂ))) :=
    (f.hasCompactSupport.isCompact.image (continuous_const_mul a)).image (continuous_mk Γ)
  refine HasCompactSupport.intro hC fun q hq => ?_
  obtain ⟨b, rfl⟩ := mk_surjective Γ q
  rw [quotientKernel_mk]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  by_contra h
  refine hq ⟨(γ : G) * b, ⟨a⁻¹ * γ * b, subset_tsupport _ h, ?_⟩, mk_mul_of_mem γ.2 b⟩
  simp [mul_assoc]

private theorem rconv_eq_integral_kernel (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (a : G) :
    rconv Γ μ f φ a = ∫ q, φ q * quotientKernel Γ f (mk Γ a, q) ∂quotientMeasure Γ μ := by
  have hint : Integrable (fun y => φ (mk Γ y) * f (a⁻¹ * y)) μ := by
    simpa only [mul_comm] using integrable_rconv Γ μ f φ a
  have h1 : rconv Γ μ f φ a = ∫ y, φ (mk Γ y) * f (a⁻¹ * y) ∂μ := by
    unfold rconv
    simp only [mul_comm]
  rw [h1, integral_mul_eq_integral_mul_automorphize μ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨b, rfl⟩ := mk_surjective Γ y
  dsimp only
  rw [quotientKernel_mk]
  congr 1
  change ∑' γ : Γ, f (a⁻¹ * (γ • b)) = _
  simp_rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc]
  exact tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))

end Kernel

theorem UpperTheory.ConvolutionTheory.K.kvAe :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n) (x : G1 K n),
      (kv μ f x : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, y)) := by
  intro K _ _ n μ _ f x
  have hc : Continuous fun q => quotientKernel (Gam K n) f (mk (Gam K n) x, q) :=
    (continuous_quotientKernel (Gam K n) f).comp (continuous_const.prodMk continuous_id)
  have hcs := hasCompactSupport_kernel (Gam K n) f x
  have hm : MemLp (fun q => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, q))) 2
      (quotientMeasure (Gam K n) μ) :=
    (Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hcs.comp_left (g := starRingEnd ℂ) (map_zero _))
  have hkw : kv μ f x = hm.toLp _ := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, rconv_eq_integral_kernel, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with q hq
    rw [hq, RCLike.inner_apply', Complex.conj_conj, mul_comm]
  rw [hkw]
  exact hm.coeFn_toLp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAe
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropAe :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      (∀ φ : L2 μ, (Rop μ f φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => ⟪kv μ f (Quotient.out y), φ⟫_ℂ) ∧ ∀ γ ∈ Gam K n, ∀ x, kv μ f (γ * x) = kv μ f x := by
  intro K _ _ n μ _ f
  have := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  refine ⟨fun φ => ?_, fun γ hγ x => ?_⟩
  · filter_upwards [integrated_ae_eq_rconvQ (Gam K n) μ f φ] with q hq
    rw [inner_kv, ← rconvQ_mk]
    refine hq.trans ?_
    congr 1
    exact (Quotient.out_eq q).symm
  · refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, inner_kv, rconv_mul_left (Gam K n) μ f φ hγ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwAdj
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.twAdj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ) (φ : L2 μ),
      (ContinuousLinearMap.adjoint θ.U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (θ.e (Quotient.out y))) := by
  intro K _ _ n μ _ θ φ
  have hp' : MeasurePreserving θ.e.symm μ μ := θ.pres.symm θ.e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, θ.e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← θ.mem_gam, θ.e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ θ.e θ.mem_gam θ.pres
  obtain ⟨h2, q2⟩ := qmapPres (Gam K n) μ θ.e.symm hg' hp'
  have key : ContinuousLinearMap.adjoint θ.U φ = Lp.compMeasurePreserving _ q1 φ := by
    refine ext_inner_right ℂ fun ψ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    have a1 := q1.quasiMeasurePreserving.ae_eq_comp (θ.U_spec ψ)
    have m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (θ.U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ)
        (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (θ.e (Quotient.out y))) (quotientMeasure (Gam K n) μ)) := by
      rw [q1.map_eq]
      exact (Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)
    have e1 := integral_map q1.measurable.aemeasurable m
    rw [q1.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz
    rw [hz]
    simp only [Function.comp_apply] at hy ⊢
    rw [hy, h2, θ.e.symm_apply_apply]
    congr 2
    exact Quotient.out_eq y
  rw [key]
  exact Lp.coeFn_compMeasurePreserving φ q1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwOpEx
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.twOpEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (e : G1 K n ≃ₜ* G1 K n), (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ →
      ∃ U : L2 μ →L[ℂ] L2 μ,
        (∀ φ : L2 μ, (U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y)))) ∧
        ∀ φ : L2 μ, (ContinuousLinearMap.adjoint U φ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
          fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y))) := by
  intro K _ _ n μ _ e hg hp
  have hp' : MeasurePreserving e.symm μ μ := hp.symm e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← hg, e.apply_symm_apply]
  obtain ⟨h1, q1⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨h2, q2⟩ := qmapPres (Gam K n) μ e.symm hg' hp'
  let U : L2 μ →L[ℂ] L2 μ := (Lp.compMeasurePreservingₗᵢ ℂ _ q2).toContinuousLinearMap
  have hU : ∀ ψ : L2 μ, (U ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
      fun y => (ψ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e.symm (Quotient.out y))) :=
    fun ψ => Lp.coeFn_compMeasurePreserving ψ q2
  refine ⟨U, hU, fun φ => ?_⟩
  have key : ContinuousLinearMap.adjoint U φ = Lp.compMeasurePreserving _ q1 φ := by
    refine ext_inner_right ℂ fun ψ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
    have a1 := q1.quasiMeasurePreserving.ae_eq_comp (hU ψ)
    have m : AEStronglyMeasurable (fun y => ⟪(φ : RightCosetSpace (Gam K n) → ℂ) y, (U ψ : RightCosetSpace (Gam K n) → ℂ) y⟫_ℂ)
        (Measure.map (fun y : RightCosetSpace (Gam K n) => mk (Gam K n) (e (Quotient.out y))) (quotientMeasure (Gam K n) μ)) := by
      rw [q1.map_eq]
      exact (Lp.aestronglyMeasurable φ).inner (Lp.aestronglyMeasurable _)
    have e1 := integral_map q1.measurable.aemeasurable m
    rw [q1.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [a1, Lp.coeFn_compMeasurePreserving φ q1] with y hy hz
    rw [hz]
    simp only [Function.comp_apply] at hy ⊢
    rw [hy, h2, e.symm_apply_apply]
    congr 2
    exact Quotient.out_eq y
  rw [key]
  exact Lp.coeFn_compMeasurePreserving φ q1
end

