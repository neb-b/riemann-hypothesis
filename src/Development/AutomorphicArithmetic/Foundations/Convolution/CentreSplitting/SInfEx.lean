module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GlobalTheory.CuspRep in
theorem UpperTheory.ConvolutionTheory.Dp.sInfEx :
    UpperTheory.ConvolutionTheory.Dp.SInfEx := by
  intro E _ _ _ n μ _ V hV τ
  have hex : ∃! π : CuspSub E n, Carries μ π V :=
    UpperTheory.ConvolutionTheory.Dp.exCusp E n μ V hV
  obtain ⟨π, hπ⟩ := hex.exists
  refine ExistsUnique.intro ((CG.mk π).infChar τ) ?_ ?_
  · exact (sInfIff E n μ π V hπ τ _).2 (ParLaws.hasInfChar_infChar (CG.mk π) τ)
  · intro m hm
    exact (CG.HasInfChar.infChar_eq (π := CG.mk π) ((sInfIff E n μ π V hπ τ m).1 hm)).symm
