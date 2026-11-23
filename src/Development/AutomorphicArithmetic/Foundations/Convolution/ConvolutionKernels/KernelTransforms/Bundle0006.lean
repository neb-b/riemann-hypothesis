module

public import Mathlib
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
public import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
public import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
public import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ExpGen

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ConvL
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.convL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : CompactlySupportedContinuousMap (archGroup K n) ℂ)
      (h₁ : (fun g => β₁ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), ∃ h₁₂ : (fun g => conv ν β₁ β₂ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ (u : UEnv K n) (x : archGroup K n),
        ((isExpLieAlgebra K n).rightUAction u ⟨fun g => conv ν β₁ β₂ g⁻¹, h₁₂⟩ : archGroup K n → ℂ) x⁻¹ =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x) ∂ν := by
  intro K _ _ n ν _ β₁ β₂ h₁
  have hc : HasCompactSupport (fun g : archGroup K n => β₁ g⁻¹) :=
    β₁.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hΘ : Continuous (fun c : archGroup K n => β₂ c⁻¹) := (map_continuous β₂).comp continuous_inv
  obtain ⟨hF, hD⟩ := UpperTheory.ConvolutionTheory.Tf.derivInt K n ν (fun g => β₁ g⁻¹) h₁ hc (fun c => β₂ c⁻¹) hΘ
  have e : (fun x : archGroup K n => ∫ a, (fun g : archGroup K n => β₁ g⁻¹) (a⁻¹ * x) * (fun c : archGroup K n => β₂ c⁻¹) a ∂ν) =
      fun g => conv ν β₁ β₂ g⁻¹ := by
    funext g
    rw [GroundTheory.Automorphic.conv_apply,
      ← integral_mul_left_eq_self (μ := ν) (fun a => β₁ a * β₂ (a⁻¹ * g⁻¹)) g⁻¹]
    congr 1
    funext c
    simp [mul_assoc]
  refine ⟨e ▸ hF, fun u x => ?_⟩
  refine Eq.trans (congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f :
    (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x⁻¹) (Subtype.ext e.symm : _ = (⟨_, hF⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)))) ?_
  rw [hD u x⁻¹, ← integral_mul_left_eq_self (μ := ν) (fun a =>
    ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x)) x]
  congr 1
  funext c
  simp [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.SliceAct
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.sliceAct :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : CompactlySupportedContinuousMap (archGroup K n) ℂ)
      (hβ : (fun g => β g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (Φ : normOneGL (K := K) (n := n) → ℂ), Continuous Φ →
      ∃ hF : liftOne (fun x => ∫ a, β a * Φ (x * archP K n a) ∂ν) ∈ archSmooth K n, ∀ (u : UEnv K n) (g : AdelicGLn.AdelicGL K n),
        (uAction u ⟨_, hF⟩ : AdelicGLn.AdelicGL K n → ℂ) g =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β g⁻¹, hβ⟩ : archGroup K n → ℂ) a⁻¹ * Φ (retractOne g * archP K n a) ∂ν := by
  intro K _ _ n ν _ β hβ Φ hΦ
  have hc : HasCompactSupport (fun g : archGroup K n => β g⁻¹) :=
    β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hΘ : ∀ g : AdelicGLn.AdelicGL K n,
      Continuous (fun a : archGroup K n => Φ (retractOne g * archP K n a)) := fun g =>
    hΦ.comp (continuous_const.mul continuous_archP)
  have hs : ∀ g : AdelicGLn.AdelicGL K n,
      archSlice (liftOne (fun x => ∫ a, β a * Φ (x * archP K n a) ∂ν)) g =
        fun x => ∫ a, (fun g : archGroup K n => β g⁻¹) (a⁻¹ * x) * Φ (retractOne g * archP K n a) ∂ν := by
    intro g
    funext x
    rw [archSlice_apply, liftOne, retractOne_mul_infEmb,
      ← integral_mul_left_eq_self (μ := ν) (fun a => (fun g : archGroup K n => β g⁻¹) (a⁻¹ * x) *
        Φ (retractOne g * archP K n a)) x]
    congr 1
    funext a
    simp [map_mul, mul_assoc]
  have hD := fun g => UpperTheory.ConvolutionTheory.Tf.derivInt K n ν _ hβ hc _ (hΘ g)
  refine ⟨fun g => by rw [hs g]; exact (hD g).1, fun u g => ?_⟩
  obtain ⟨hF, h⟩ := hD g
  have h1 := h u 1
  simp only [mul_one] at h1
  rw [coe_uAction, uActFun, ← h1]
  exact congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f :
    (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) 1) (Subtype.ext (hs g))
end

