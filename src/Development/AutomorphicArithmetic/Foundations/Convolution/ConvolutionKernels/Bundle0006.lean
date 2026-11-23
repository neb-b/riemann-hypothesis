module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdHeight
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.galTwistEx :
    GalTwistEx := by
  intro K _ _ n μ _ σ
  obtain ⟨e, he, he', hg, m, hm, hit⟩ := galEquiv K n σ
  have hp := presOfOrder μ e m hm hit
  have hp' : MeasurePreserving e.symm μ μ := hp.symm e.toHomeomorph.toMeasurableEquiv
  have hg' : ∀ g, e.symm g ∈ Gam K n ↔ g ∈ Gam K n := fun g => by rw [← hg, e.apply_symm_apply]
  obtain ⟨U, hU, hU'⟩ := twOpEx K n μ e hg hp
  refine ⟨⟨e, hg, hp, ⟨1, 1, fun g => ?_⟩, U, hU, ?_⟩, he⟩
  · rw [he, adHeight]; simp
  · exact commProj (cuspidalL2 μ) U (fun v hv => galCusp K n μ σ.symm e.symm he' hg' hp' v _ hv (hU v))
      (fun v hv => galCusp K n μ σ e he hg hp v _ hv (hU' v))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KerId
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.kerId :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f a g : CC K n) (M : L2 μ →L[ℂ] L2 μ),
      Rop μ f = Rop μ a ∘L M ∘L Rop μ g → ∀ x y : G1 K n,
        ∑ᶠ γ : Gam K n, f (x⁻¹ * (γ : G1 K n) * y) = ⟪kv μ a x, M (kv μ (ccStar g) y)⟫_ℂ := by
  intro K _ _ n μ _ f a g M hf x y
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have ext : ∀ u w : RightCosetSpace (Gam K n) → ℂ, Continuous u → Continuous w →
      u =ᵐ[quotientMeasure (Gam K n) μ] w → ∀ z : G1 K n, u (mk _ z) = w (mk _ z) := by
    intro u w hu hw h z
    have h1 := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) h
    exact congrFun ((hu.comp (continuous_mk _)).ae_eq_iff_eq μ (hw.comp (continuous_mk _)) |>.1 h1) z
  have s1 : ∀ φ : L2 μ, rconv (Gam K n) μ f φ x = rconv (Gam K n) μ a (M (Rop μ g φ)) x := by
    intro φ
    have e : Rop μ f φ = Rop μ a (M (Rop μ g φ)) := by rw [hf]; rfl
    refine ext _ _ (continuous_rconvQ _ μ f φ) (continuous_rconvQ _ μ a _) ?_ x
    have a1 := integrated_ae_eq_rconvQ (Gam K n) μ f φ
    have a2 := integrated_ae_eq_rconvQ (Gam K n) μ a (M (Rop μ g φ))
    change (Rop μ f φ : _ → ℂ) =ᵐ[_] _ at a1
    change (Rop μ a (M (Rop μ g φ)) : _ → ℂ) =ᵐ[_] _ at a2
    rw [e] at a1
    exact a1.symm.trans a2
  have s2 : kv μ f x = Rop μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x)) := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, s1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, inner_kv]
  have a3 := integrated_ae_eq_rconvQ (Gam K n) μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))
  change (Rop μ (ccStar g) _ : _ → ℂ) =ᵐ[_] _ at a3
  rw [← s2] at a3
  have s3 := ext _ _ (Complex.continuous_conj.comp ((continuous_quotientKernel (Gam K n) f).comp (Continuous.prodMk_right (mk _ x))))
    (continuous_rconvQ _ μ (ccStar g) _) ((kvAe K n μ f x).symm.trans a3) y
  simp only [Function.comp_apply, quotientKernel_mk, rconvQ_mk] at s3
  rw [← inner_kv, ContinuousLinearMap.adjoint_inner_right] at s3
  rw [← inner_conj_symm, ← s3, starRingEnd_self_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem norm_le_of_sq {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (h : t ^ 2 ≤ B * t) : t ≤ B := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem UpperTheory.ConvolutionTheory.K.kvBd :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n),
      (PolyBd μ a → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x, ‖kv μ a x‖ ≤ C * qht x ^ N) ∧
      (CuspDecay μ a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Pc μ (kv μ a x)‖ ≤ C * (qht x ^ N')⁻¹) := by
  intro K _ _ n μ _ a
  have hq : ∀ x : G1 K n, 0 ≤ qht x := fun x => zero_le_one.trans ((qhtBasic K n).1 x)
  refine ⟨?_, ?_⟩
  · rintro ⟨C, N, h⟩
    refine ⟨max C 0, N, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ qht x ^ N := pow_nonneg (hq x) N
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have h1 := h (kv μ a x) x
    rw [← inner_kv, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖kv μ a x‖ ^ 2 ≤ C * qht x ^ N * ‖kv μ a x‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _
  · intro hc N'
    obtain ⟨C, h⟩ := hc N'
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (hq x) N')
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have hm : Pc μ (kv μ a x) ∈ cuspidalL2 μ := Submodule.starProjection_apply_mem _ _
    have h1 := h (Pc μ (kv μ a x)) hm x
    have h0 : ⟪kv μ a x - Pc μ (kv μ a x), Pc μ (kv μ a x)⟫_ℂ = 0 :=
      Submodule.starProjection_inner_eq_zero _ _ hm
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [← inner_kv, h0, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖Pc μ (kv μ a x)‖ ^ 2 ≤ C * (qht x ^ N')⁻¹ * ‖Pc μ (kv μ a x)‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopPc
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropPc :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Rop μ f ∘L Pc μ = Pc μ ∘L Rop μ f := by
  intro K _ _ n μ _ f
  have h : ∀ g : CC K n, ∀ v ∈ cuspidalL2 μ, Rop μ g v ∈ cuspidalL2 μ := by
    intro g v hv
    rw [← Submodule.orthogonal_orthogonal (cuspidalL2 μ), Submodule.mem_orthogonal]
    intro u hu
    rw [Rop, inner_integrated_ccToL1]
    have : ∀ x, ⟪u, rightRegularRep (Gam K n) μ x v⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal' _ _).1 hu _ (isInvariant_cuspidalL2 μ x v hv)
    simp [this]
  exact commProj (cuspidalL2 μ) (Rop μ f) (h f) (fun v hv => by rw [ropAdj]; exact h _ v hv)
end

