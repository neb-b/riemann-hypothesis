module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TsphComm
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.AmpComm
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem finAt_mem_of_integral {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K)
    {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    finAt w (finEmb K n u) ∈ GLnLocal.integralGL (w.adicCompletion K) n := by
  have e : finAt w (finEmb K n u) = AdelicGLn.finiteRestrictedEquiv K n u w := by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n u)).2) w = _
    rw [prodEquiv_finEmb]
  rw [e]
  exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hu w

theorem UpperTheory.ConvolutionTheory.Tf.ampComm :
    ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (𝔞 : Amp μ),
      (∀ τ i, zc τ i ∈ Subalgebra.center ℂ (UC K n)) →
      0 ≤ 𝔞.A ∧ ‖𝔞.A‖ ≤ 1 ∧ (∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) ∧ IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
      (∀ x, Commute 𝔞.A (𝔞.Z x)) ∧ (∀ x y, Commute (𝔞.Z x) (𝔞.Z y)) ∧
      ∀ w ∉ 𝔞.S, ∀ i, Commute 𝔞.A (Tsph μ w i) ∧ ∀ x, Commute (𝔞.Z x) (Tsph μ w i) := by
  intro K _ _ _ n μ _ 𝔞 hz
  obtain ⟨-, -, a1, a2, -, -, -, -, hT⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U
  obtain ⟨hconv, -, -, -, -, -, -, -, hρ⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n))
  have hA : ∀ β : TI K n, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) = Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U) := fun _ => rfl
  have hOP : ∀ β : TI K n, Commute (Oinf μ 𝔞.ν β) (prj (fixF μ 𝔞.U)) := fun β => hT _ fun u _ => hρ β u
  have hPP : prj (fixF μ 𝔞.U) * prj (fixF μ 𝔞.U) = prj (fixF μ 𝔞.U) :=
    ContinuousLinearMap.ext fun v => a2 _ (a1 v)
  have hcomp : ∀ β γ : TI K n, conv 𝔞.ν β γ = conv 𝔞.ν γ β →
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) := by
    intro β γ h
    have e : ∀ β γ : TI K n, (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) * (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) =
        Oinf μ 𝔞.ν (conv 𝔞.ν β γ) * prj (fixF μ 𝔞.U) := by
      intro β γ
      rw [(hOP γ).symm.mul_mul_mul_comm, hPP, (hconv β γ).1]
      rfl
    show _ * _ = _ * _
    rw [e, e, h]
  have hs := 𝔞.smooth
  have hl := UpperTheory.ConvolutionTheory.Tf.lactSpec K n 𝔞.a₀ hs
  obtain ⟨-, -, hsm, -, hmul, -⟩ := hl
  have hswap : ∀ u ∈ Subalgebra.center ℂ (UC K n), ∀ β : TI K n, SmoothT β →
      conv 𝔞.ν (lact u 𝔞.a₀) β = conv 𝔞.ν 𝔞.a₀ (lact u β) := fun u hu β hβ =>
    (UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν 𝔞.a₀ β hs).2.2 inferInstance hβ u hu
  have hHop : ∀ w ∉ 𝔞.S, ∀ (x : GL (Fin n) (w.adicCompletion K)) (β : TI K n),
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) := by
    intro w hw x β
    have hO := GLnLocal.isOpen_integralGL (w.adicCompletion K) n
    have hC := GLnLocal.isCompact_integralGL (w.adicCompletion K) n
    have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
    have h1 : Commute (Oinf μ 𝔞.ν β) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) :=
      (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w _ x hO hC).2.2.2.2.1 _ fun g => hρ β _
    have h2 := (UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) w _ x 𝔞.U hO hC 𝔞.isOpen hUc
      (𝔞.max w hw) fun u hu => finAt_mem_of_integral w (𝔞.le hu)).1
    exact h1.mul_left h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hpos : (Oinf μ 𝔞.ν 𝔞.a₀).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive).1 𝔞.pos
    have hadj : ContinuousLinearMap.adjoint (prj (fixF μ 𝔞.U)) = prj (fixF μ 𝔞.U) :=
      (isSelfAdjoint_starProjection _).adjoint_eq
    have h := hpos.conj_adjoint (prj (fixF μ 𝔞.U))
    rw [hadj] at h
    have e : prj (fixF μ 𝔞.U) ∘L Oinf μ 𝔞.ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) = 𝔞.A := by
      show prj (fixF μ 𝔞.U) * (Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)) = Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)
      rw [← mul_assoc, ← (hOP _).eq, mul_assoc, hPP]
    rw [e] at h
    exact (ContinuousLinearMap.nonneg_iff_isPositive).2 h
  · calc ‖𝔞.A‖ ≤ ‖Oinf μ 𝔞.ν 𝔞.a₀‖ * ‖prj (fixF μ 𝔞.U)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul 𝔞.norm_le (Submodule.starProjection_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro v
    have e : 𝔞.A v = prj (fixF μ 𝔞.U) (Oinf μ 𝔞.ν 𝔞.a₀ v) :=
      congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOP 𝔞.a₀).eq
    rw [e]
    exact a1 _
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
  · intro x
    exact hcomp _ _ (hswap _ (hz x.1 x.2) _ hs).symm
  · intro x y
    refine hcomp _ _ ?_
    rw [hswap _ (hz x.1 x.2) _ (hsm _).1, hswap _ (hz y.1 y.2) _ (hsm _).1, ← (hmul _ _).1, ← (hmul _ _).1,
      (Subalgebra.mem_center_iff.1 (hz x.1 x.2) (zc y.1 y.2))]
  · intro w hw i
    refine ⟨(hHop w hw _ _).smul_right _, fun x => (hHop w hw _ _).smul_right _⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RconvSlice
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem parts_archP (a : archGroup K n) :
    ∃ s, infPart K n (archP K n a : AdelicGLn.AdelicGL K n) = a * zInf K n s ∧
      CuspidalSpectrum.finPart K n (archP K n a : AdelicGLn.AdelicGL K n) = 1 := by
  refine ⟨(detModule K n (infEmb K n a))⁻¹, ?_, ?_⟩
  · rw [← retract_infEmb, coe_retractOne, map_mul, infPart_infEmb, ← map_inv, map_inv (zInf K n)]
    rw [map_inv (centralSection K n), map_inv (infPart K n)]
    rfl
  · rw [← retract_infEmb, coe_retractOne, map_mul, finPart_infEmb, map_inv, finPart_centralSection]
    simp

private theorem tensFun_shift (β : TI K n) (e : TF K n) (a : archGroup K n) (g : normOneGL (K := K) (n := n)) :
    tensFun β e ((archP K n a)⁻¹ * g) =
      kbar β (a⁻¹ * infPart K n (g : AdelicGLn.AdelicGL K n)) *
        e (CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n)) := by
  obtain ⟨s, h1, h2⟩ := parts_archP a
  rw [tensFun, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, inv_one, one_mul,
    mul_inv_rev, ← map_inv, mul_assoc, zInf_mul_comm, kbar_mul_zInf]

private theorem kbar_conv (hn : 0 < n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n)
    (x : archGroup K n) :
    kbar (conv ν β₁ β₂) x = ∫ a, β₁ a * kbar β₂ (a⁻¹ * x) ∂ν := by
  have hc : Continuous (Function.uncurry fun (s : {r : ℝ // 0 < r}) (a : archGroup K n) =>
      β₁ a * β₂ (a⁻¹ * (x * zInf K n s))) := by
    refine (β₁.continuous.comp continuous_snd).mul (β₂.continuous.comp ?_)
    exact (continuous_snd.inv).mul (continuous_const.mul (continuous_zInf.comp continuous_fst))
  have hs : HasCompactSupport (Function.uncurry fun (s : {r : ℝ // 0 < r}) (a : archGroup K n) =>
      β₁ a * β₂ (a⁻¹ * (x * zInf K n s))) := by
    have hC : IsCompact ((fun p : {r : ℝ // 0 < r} × archGroup K n => (p.1 * detA K n (x⁻¹ * p.2), p.2)) ''
        ((detA K n '' tsupport β₂) ×ˢ tsupport β₁)) :=
      ((β₂.hasCompactSupport.isCompact.image continuous_detA).prod β₁.hasCompactSupport.isCompact).image
        ((continuous_fst.mul (continuous_detA.comp (continuous_const.mul continuous_snd))).prodMk continuous_snd)
    refine HasCompactSupport.intro hC fun p hp => ?_
    by_contra hne
    apply hp
    obtain ⟨s, a⟩ := p
    have h1 : β₁ a ≠ 0 := left_ne_zero_of_mul hne
    have h2 : β₂ (a⁻¹ * (x * zInf K n s)) ≠ 0 := right_ne_zero_of_mul hne
    have h3 := mem_of_kernel_ne_zero hn (κ := β₂) (a := a⁻¹ * x) (s := s) (by rwa [mul_assoc])
    refine ⟨(s * detA K n (a⁻¹ * x), a), ⟨h3, subset_tsupport _ h1⟩, ?_⟩
    have h4 : detA K n (a⁻¹ * x) * detA K n (x⁻¹ * a) = 1 := by
      rw [← map_mul]
      simp [mul_assoc]
    simp only [mul_assoc, h4, mul_one]
  have hsw := integral_integral_swap_of_hasCompactSupport hc hs (μ := GroundTheory.Global.posRealMeasure) (ν := ν)
  simp only [kbar, conv_apply]
  rw [hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_assoc]
  exact integral_const_mul _ _

private theorem tens_conv (hn : 0 < n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n) (e : TF K n)
    (g : normOneGL (K := K) (n := n)) :
    tens (conv ν β₁ β₂) e g = ∫ a, β₁ a * tens β₂ e ((archP K n a)⁻¹ * g) ∂ν := by
  simp only [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn _ e).1, tensFun_shift]
  rw [tensFun, kbar_conv hn, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_assoc]

private theorem rconv_conv (hn : 0 < n) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n) (e : TF K n) (φ : LL μ) (x : normOneGL (K := K) (n := n)) :
    rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν β₁ β₂) e) φ x =
      ∫ a, β₁ a * rconv (rationalGLOne (K := K) (n := n)) μ (tens β₂ e) φ (x * archP K n a) ∂ν := by
  haveI hσ : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ μ hσ
  obtain ⟨T, hT⟩ : ∃ T, T = tens β₂ e := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = tsupport β₁ := ⟨_, rfl⟩
  have hAc : IsCompact A := hA ▸ β₁.hasCompactSupport.isCompact
  obtain ⟨D, hD⟩ : ∃ D, D = (fun q : archGroup K n × normOneGL (K := K) (n := n) => x * archP K n q.1 * q.2) ''
      (A ×ˢ tsupport (T : normOneGL (K := K) (n := n) → ℂ)) := ⟨_, rfl⟩
  have hDc : IsCompact D := by
    rw [hD]
    exact (hAc.prod T.hasCompactSupport.isCompact).image
      ((continuous_const.mul (continuous_archP.comp continuous_fst)).mul continuous_snd)
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = D.indicator fun y => φ (mk (rationalGLOne (K := K) (n := n)) y) := ⟨_, rfl⟩
  have hψi : Integrable ψ μ := by
    rw [hψ]
    exact (integrableOn_lift (rationalGLOne (K := K) (n := n)) μ φ hDc).integrable_indicator hDc.measurableSet
  have hβi : Integrable (β₁ : archGroup K n → ℂ) ν :=
    β₁.continuous.integrable_of_hasCompactSupport β₁.hasCompactSupport
  obtain ⟨M, hM⟩ := T.continuous.bounded_above_of_compact_support T.hasCompactSupport
  have hint : Integrable (Function.uncurry fun (a : archGroup K n) (y : normOneGL (K := K) (n := n)) =>
      β₁ a * (T ((archP K n a)⁻¹ * (x⁻¹ * y)) * φ (mk (rationalGLOne (K := K) (n := n)) y))) (ν.prod μ) := by
    have h1 : Integrable (fun z : archGroup K n × normOneGL (K := K) (n := n) => β₁ z.1 * ψ z.2) (ν.prod μ) := hβi.mul_prod hψi
    have hcT : Continuous fun z : archGroup K n × normOneGL (K := K) (n := n) => T ((archP K n z.1)⁻¹ * (x⁻¹ * z.2)) :=
      T.continuous.comp ((continuous_archP.comp continuous_fst).inv.mul (continuous_const.mul continuous_snd))
    have h2 := h1.bdd_mul hcT.aestronglyMeasurable (Filter.Eventually.of_forall fun z => hM _)
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    obtain ⟨a, y⟩ := z
    simp only [Function.uncurry]
    by_cases hy : y ∈ D
    · rw [hψ, Set.indicator_of_mem hy]
      ring
    · rw [hψ, Set.indicator_of_notMem hy, mul_zero, mul_zero]
      by_cases ha : a ∈ A
      · have h0 : T ((archP K n a)⁻¹ * (x⁻¹ * y)) = 0 := by
          by_contra hne
          refine hy ?_
          rw [hD]
          refine ⟨(a, (archP K n a)⁻¹ * (x⁻¹ * y)), ⟨ha, subset_tsupport _ hne⟩, ?_⟩
          simp [mul_assoc]
        rw [h0, zero_mul, mul_zero]
      · have h0 : β₁ a = 0 := image_eq_zero_of_notMem_tsupport (by rwa [← hA])
        rw [h0, zero_mul]
  have hsw := integral_integral_swap hint
  have hr : ∀ a : archGroup K n, β₁ a * rconv (rationalGLOne (K := K) (n := n)) μ (tens β₂ e) φ (x * archP K n a) =
      ∫ y, β₁ a * (T ((archP K n a)⁻¹ * (x⁻¹ * y)) * φ (mk (rationalGLOne (K := K) (n := n)) y)) ∂μ := by
    intro a
    rw [rconv, integral_const_mul, hT]
    simp only [mul_inv_rev, mul_assoc]
  simp only [hr]
  rw [hsw, rconv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [tens_conv hn, ← integral_mul_const, hT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_assoc]

private theorem uAct_tmul (c : ℂ) (a : UEnv K n) (f : archSmooth K n) :
    (uAct (c ⊗ₜ[ℝ] a) f : archSmooth K n) = c • (uAction a f : archSmooth K n) := by
  exact congrArg (fun T : Module.End ℂ (archSmooth K n) => T f)
    (Algebra.TensorProduct.lift_tmul (Algebra.ofId ℂ (Module.End ℂ (archSmooth K n)))
      (uAction : UEnv K n →ₐ[ℝ] Module.End ℂ (archSmooth K n))
      (fun c _ => Algebra.commute_algebraMap_left c _) c a)

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Tf.rconvSlice :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], Compat μ ν m →
      ∀ (β₁ β₂ : TI K n) (e : TF K n) (φ : LL μ), SmoothT β₁ →
      (∀ x, rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν β₁ β₂) e) φ x =
        ∫ a, β₁ a * rconv (rationalGLOne (K := K) (n := n)) μ (tens β₂ e) φ (x * archP K n a) ∂ν) ∧
      ∃ h : liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν β₁ β₂) e) φ) ∈ archSmooth K n, ∀ u : UC K n,
        (uAct u ⟨_, h⟩ : AdelicGLn.AdelicGL K n → ℂ) =
          liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν (lact u β₁) β₂) e) φ) := by
  intro K _ _ n hn μ _ ν _ m _ _ β₁ β₂ e φ hβ₁
  refine ⟨rconv_conv hn μ ν β₁ β₂ e φ, ?_⟩
  obtain ⟨h, -, h2, -, h4, h5, -, h7⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β₁ hβ₁
  obtain ⟨Φ, hΦe⟩ : ∃ Φ, Φ = rconv (rationalGLOne (K := K) (n := n)) μ (tens β₂ e) φ := ⟨_, rfl⟩
  have hΦ : Continuous Φ := hΦe ▸ continuous_rconv (rationalGLOne (K := K) (n := n)) μ (tens β₂ e) φ
  have key : ∀ (γ : TI K n) x, rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν γ β₂) e) φ x =
      ∫ a, γ a * Φ (x * archP K n a) ∂ν := fun γ x => by
    rw [hΦe]
    exact rconv_conv hn μ ν γ β₂ e φ x
  obtain ⟨hF, hU⟩ := UpperTheory.ConvolutionTheory.Tf.sliceAct K n ν β₁ h Φ hΦ
  have e0 : rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν β₁ β₂) e) φ =
      fun x => ∫ a, β₁ a * Φ (x * archP K n a) ∂ν := funext (key β₁)
  have hF' : liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (conv ν β₁ β₂) e) φ) ∈ archSmooth K n := by
    rw [e0]
    exact hF
  have hi : ∀ (γ : TI K n) (g : AdelicGLn.AdelicGL K n),
      Integrable (fun a => γ a * Φ (retractOne g * archP K n a)) ν := fun γ g =>
    (γ.continuous.mul (hΦ.comp (continuous_const.mul continuous_archP))).integrable_of_hasCompactSupport
      γ.hasCompactSupport.mul_right
  have P : ∀ (u : UC K n) (g : AdelicGLn.AdelicGL K n), (uAct u ⟨_, hF⟩ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ a, lact u β₁ a * Φ (retractOne g * archP K n a) ∂ν := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero =>
      intro g
      have l0 : lact (0 : UC K n) β₁ = 0 := by
        have := (h5 0 0).1
        simpa using this
      rw [l0, map_zero]
      simp
    | tmul c a =>
      intro g
      have l1 : lact (c ⊗ₜ[ℝ] a) β₁ = c • lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₁ := by
        rw [← (h5 c _).1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [uAct_tmul, Submodule.coe_smul, Pi.smul_apply, hU a g, l1]
      simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, h7, mul_assoc]
      rw [integral_const_mul]
    | add u v hu hv =>
      intro g
      rw [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hu g, hv g, (h4 u v).2,
        ← integral_add (hi _ g) (hi _ g)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      simp only [CompactlySupportedContinuousMap.add_apply]
      ring
  refine ⟨hF', fun u => ?_⟩
  have hsub : (⟨_, hF'⟩ : archSmooth K n) = ⟨_, hF⟩ := Subtype.ext (congrArg liftOne e0)
  rw [hsub]
  funext g
  rw [P, liftOne, key]
end

