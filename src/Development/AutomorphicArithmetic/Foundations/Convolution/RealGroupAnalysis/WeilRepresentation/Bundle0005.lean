module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.GoodLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LiftCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.TrISmul

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsBis
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.cusp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Cusp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Φ hΦ
  have hG : Good D Φ.1 := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, hφ, e⟩ := hx
      rw [e]
      exact G.goodLift F E D W M π h0 f hf φ hφ
    | zero => exact (G.goodSpan F E D).1
    | add x y _ _ hx hy => exact (G.goodSpan F E D).2.1 _ _ hx hy
    | smul c x _ hx => exact (G.goodSpan F E D).2.2 c _ hx
  refine ⟨G.cuspE F E D _ hG.left hG.zero, fun hW => Subtype.ext (funext fun h => ?_)⟩
  have hs := hG.sum h
  simp only [hW] at hs
  exact hs.unique hasSum_zero
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.smooth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Smooth W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  have key := smCrit E (Submodule.span ℂ {Φ : GL (Fin 2) (A E) → ℂ | ∃ f ∈ π.V, ∃ φ ∈ Fock D.δ, Φ = lift W M f.1 φ})
    (fun Φ hΦ => by
      induction hΦ using Submodule.span_induction with
      | mem Φ h => obtain ⟨f, hf, φ, hφ, rfl⟩ := h; exact liftCont F E D W M π f hf φ hφ
      | zero => exact fun _ => continuous_const
      | add _ _ _ _ h1 h2 => exact fun g => (h1 g).add (h2 g)
      | smul c _ _ h1 => exact fun g => (h1 g).const_smul c)
    (fun Φ hΦ => by
      induction hΦ using Submodule.span_induction with
      | mem Φ h => obtain ⟨f, hf, φ, hφ, rfl⟩ := h; exact derT F E D W M π f hf φ hφ
      | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => hasDerivAt_const _ _⟩
      | add _ _ _ _ h1 h2 =>
        obtain ⟨T1, a1, b1⟩ := h1
        obtain ⟨T2, a2, b2⟩ := h2
        exact ⟨T1 + T2, fun X => add_mem (a1 X) (a2 X), fun X g => (b1 X g).add (b2 X g)⟩
      | smul c _ _ h1 =>
        obtain ⟨T1, a1, b1⟩ := h1
        exact ⟨c • T1, fun X => Submodule.smul_mem _ c (a1 X), fun X g => (b1 X g).const_smul c⟩)
  exact ⟨⟨_, key (Submodule.subset_span ⟨f, hf, φ, hφ, rfl⟩)⟩, rfl⟩
end

