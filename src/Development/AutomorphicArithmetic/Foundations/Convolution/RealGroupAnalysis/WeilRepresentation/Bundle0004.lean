module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0018
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Exp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.exp :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Exp W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  have hδ : D.δ ≠ 0 := by
    intro h0
    have h := D.sq
    rw [h0, map_zero] at h
    exact D.b.ne_zero 1 (by rw [D.b1, (pow_eq_zero_iff two_ne_zero).1 h])
  have hO := G.orth F D.δ hδ (T0 W M f.1 φ h) (Wx W M f.1 φ h) (fun u => lift W M f.1 φ (nE D u * h))
    (G.expand1 F E D W M π f hf φ hφ h).1 fun u => by
      rw [(G.expand1 F E D W M π f hf φ hφ _).2, (G.transN F E D W M f.1 φ h u).1]
      simp only [(G.transN F E D W M f.1 φ h u).2]
  exact hO.2.2.2.trans (G.thetaFourierCoeff_zero_and_eq_shifted_whittaker F E D W M π f hf φ hφ h).2.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsExtra
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.ne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Ne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π
  obtain ⟨f, hf, a, k, hk, hW⟩ := G.exIw F M π
  obtain ⟨φ, hφ, hp⟩ := G.exPhi F E D W a k hk
  by_contra hn
  have h0 : ∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0 := fun φ hφ => by
    by_contra h1
    exact hn ⟨f, hf, φ, hφ, 1, h1⟩
  have h := G.zeroW F E D W M π f hf h0 φ hφ a k hk
  have e : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  simp only [w1, e, dM_one, mul_one, map_one, Module.End.one_apply] at h
  exact mul_ne_zero hW hp h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.stable :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Stable W M π := by
  intro F E _ _ _ _ _ _ _ D W M π o Φ hΦ
  refine (Submodule.span_le.2 ?_ : span W M π ≤ (span W M π).comap (act o)) hΦ
  rintro Ψ ⟨f, hf, φ, hφ, e⟩
  cases o with
  | fin k =>
    obtain ⟨f', hf', φ', hφ', h⟩ := finLift F E D W M π f hf φ hφ k
    exact Submodule.subset_span ⟨f', hf', φ', hφ', funext fun g => (congrFun e _).trans (h g)⟩
  | cpt k => exact (kFin F E D W M π f hf φ hφ Ψ e).1 k
  | lie X =>
    obtain ⟨O⟩ := UpperTheory.ConvolutionTheory.R2.Fo.opsEx F
    obtain ⟨Y, s, hY, rfl, -⟩ := lieSplit X
    change lie E 2 (Y + zE s) Ψ ∈ span W M π
    rw [map_add (f := _), LinearMap.add_apply]
    exact add_mem (Submodule.subset_span ⟨f, hf, _, dLFock F E D O Y φ hφ, lieL F E D O W M π f hf φ hφ Y hY Ψ e⟩)
      (Submodule.subset_span ⟨_, π.stable (.lie _) f hf, φ, hφ, lieZ F E D W M π f hf φ hφ s Ψ e⟩)
end

