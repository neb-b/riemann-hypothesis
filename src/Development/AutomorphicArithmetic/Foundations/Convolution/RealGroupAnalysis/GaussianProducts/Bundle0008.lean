module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.BdInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.bdInv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ C : Set (GL (Fin 2) (A F)), IsCompact C → ∃ B : ℝ, 0 ≤ B ∧ ∀ b a, ∀ k ∈ C,
    ‖f.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ ∧ ‖Wf f.1 (gl (nU b * mD a) * k)‖ ≤ B * (ab a)⁻¹ := by
  intro F _ _ _ π f hf C hC
  obtain ⟨B₁, h₁⟩ := UpperTheory.ConvolutionTheory.R2.Pp.bdd F π f hf C hC
  obtain ⟨-, hd⟩ := UpperTheory.ConvolutionTheory.R2.decay F π f hf
  obtain ⟨B₂, h₂⟩ := hd C hC 1 one_pos 1
  have key : ∀ (b : A F) (a : (A F)ˣ), ∀ k ∈ C,
      ‖f.1 (gl (nU b * mD a) * k)‖ ≤ max (max B₁ B₂) 0 * (ab a)⁻¹ := by
    intro b a k hk
    have hp : 0 < ab a := (IdeleGroup.ideleModule F a).2
    have hi : 0 < (ab a)⁻¹ := inv_pos.2 hp
    rcases le_total 1 (ab a) with h | h
    · have h3 := h₂ b a k hk h
      rw [pow_one] at h3
      exact h3.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) hi.le)
    · have h1 : 1 ≤ (ab a)⁻¹ := (one_le_inv₀ hp).2 h
      calc ‖f.1 (gl (nU b * mD a) * k)‖ ≤ B₁ := (h₁ _ k hk).1
        _ ≤ max (max B₁ B₂) 0 := (le_max_left _ _).trans (le_max_left _ _)
        _ = max (max B₁ B₂) 0 * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  refine ⟨_, le_max_right _ _, fun b a k hk => ⟨key b a k hk, UpperTheory.ConvolutionTheory.R2.Pp.norm_Wf_le fun x => ?_⟩⟩
  have e : gl (nU (x + b) * mD a) = gl (nU x) * gl (nU b * mD a) := by
    have g : ∀ y z : G1 F, gl (y * z) = gl y * gl z := fun y z => map_mul _ _ _
    rw [g, g, UpperTheory.ConvolutionTheory.R2.Pp.n_add, mul_assoc]
  have h4 := key (x + b) a k hk
  rwa [e, mul_assoc] at h4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExIw
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exIw :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (π : TR.CuspSub F 2), ∃ f ∈ π.V, ∃ a, ∃ k ∈ KK F, Wf f.1 (gl (mD a * k)) ≠ 0 := by
  intro F _ _ _ _ π
  obtain ⟨f, hf, g, -, hg⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfNe F π
  obtain ⟨b, a, k, hk, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa F g
  refine ⟨f, hf, a, k, hk, fun h => hg ?_⟩
  have e : gl (nU b * mD a * k) = gl (nU b) * gl (mD a * k) := by
    rw [mul_assoc]
    exact map_mul _ _ _
  rw [e, ((UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1).2.1 b _), h, mul_zero]
end

