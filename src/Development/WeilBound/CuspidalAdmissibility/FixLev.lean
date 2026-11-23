module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0003

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.RightCosetSpace
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped RestrictedProduct Classical

namespace PositivityTheory.TfC.FixLev

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finAt_finEmb (u : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n u) =
      (AdelicGLn.finiteRestrictedEquiv K n u v : GL (Fin n) (v.adicCompletion K)) := by
  ext a b
  rw [finAt_apply, AdelicGLn.finiteRestrictedEquiv_apply, ← AdelicGLn.prodEquiv_apply_snd,
    prodEquiv_finEmb]

section Rep

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

end Rep

end PositivityTheory.TfC.FixLev
