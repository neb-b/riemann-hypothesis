module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.HomCommTrivial

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.red :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Red F := by
  intro F _ _ _
  obtain ⟨t₀, ht₀, h⟩ := Reduction.exists_reduced (K := F)
  refine ⟨Real.sqrt t₀, Real.sqrt_pos.2 ht₀, fun g => ?_⟩
  obtain ⟨γ, b, hb, k, hk, he, hr⟩ := h 2 (gl g)
  obtain ⟨γ', b', hb', he', h0, h1⟩ := M.redDet F g γ b hb k he
  obtain ⟨x, a, k', hk', hg, ha, ha'⟩ := M.fromGL F (ratS F γ' * g) b' hb' k hk he'
  refine ⟨γ', x, a, k', hk', hg, ?_⟩
  have := hr 0 1 rfl
  rw [← h1, ← h0, ha', ← ha, Reduction.adeleAbs_units] at this
  change t₀ * (ab a)⁻¹ ≤ ab a at this
  have hp := M.ab_pos a
  rw [mul_inv_le_iff₀ hp] at this
  exact Real.sqrt_le_iff.2 ⟨hp.le, by rwa [pow_two]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTer
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.gen :
    ∀ (F : Type) [Field F] [NumberField F], St.Gen F := by
  intro F _ _
  refine ⟨eq_top_of_nU_wW _ (fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl)),
    le_antisymm ((Subgroup.closure_le _).2 ?_)
      (Gam_le _ (fun b => Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl)))⟩
  rintro _ (⟨b, rfl⟩ | rfl)
  exacts [nU_rt_mem b, wW_mem]
end

