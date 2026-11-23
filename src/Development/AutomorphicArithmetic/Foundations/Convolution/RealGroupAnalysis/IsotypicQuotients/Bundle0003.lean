module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Imports
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.R2.Pp.bdd :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Bdd F := by
  intro F _ _ _ π f hf C hC
  obtain ⟨ω, hω, hc⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
  obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
  let u : GL (Fin 2) (A F) → (A F)ˣ := fun k =>
    posIdeleHom F (rpowHom ((((2 : ℕ) : ℝ) * Module.finrank ℚ F))⁻¹ (detModule F 2 k))
  have hu : Continuous u := continuous_posIdeleHom.comp ((continuous_rpowHom _).comp continuous_detModule)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (Units.continuous_val.comp (hω.comp hu)).continuousOn
  have key : ∀ g : G1 F, ∀ k ∈ C, ‖φ.1 (gl g * k)‖ ≤ M * B₀ := fun g k hk => by
    have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (u k) = centralSection F 2 (detModule F 2 k) := Units.ext rfl
    have h1 : detModule F 2 (gl g) = 1 := by
      have : AdelicGLn.det F 2 (gl g) = 1 := Units.ext g.2
      rw [detModule, MonoidHom.comp_apply, this, map_one]
    have h2 : (centralSection F 2 (detModule F 2 k))⁻¹ * (gl g * k) ∈ normOneGL (K := F) (n := 2) := by
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, h1, detModule_centralSection two_pos, one_mul,
        inv_mul_cancel]
    have h3 := hc _ hf (u k) ((centralSection F 2 (detModule F 2 k))⁻¹ * (gl g * k))
    rw [e, mul_inv_cancel_left] at h3
    rw [show φ.1 (gl g * k) = _ from h3, norm_mul]
    exact mul_le_mul (hM k hk) (hB₀ _ h2) (norm_nonneg _) ((norm_nonneg _).trans (hM k hk))
  refine ⟨M * B₀, fun g k hk => ⟨key g k hk, norm_Wf_le fun b => ?_⟩⟩
  have := key (nU b * g) k hk
  rwa [show gl (nU b * g) = gl (nU b) * gl g from map_mul _ _ _, mul_assoc] at this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfNe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfNe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.WfNe F := by
  intro F _ _ _ π
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨x, hx⟩ : ∃ x, Wf f.1 x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
    exact h0 (Subtype.ext (eq_zero_of_Wf φ.2 (cuspZero F π _ hf).1 hn))
  obtain ⟨g, s, k, y, hg, rfl⟩ := infDec F x
  refine ⟨TR.act (.cpt k) (TR.act (.fin y) f), π.stable _ _ (π.stable _ _ hf), g, hg, fun h => hx ?_⟩
  unfold Wf at h ⊢
  rw [← mul_zero ((ω s : ℂˣ) : ℂ), ← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e : ∀ z : GL (Fin 2) (A F), gl (nU b) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (nU b) * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext ((Matrix.scalar_commute (s : A F) (fun _ => mul_comm _ _) _).eq.symm)
  simp only
  rw [e, hω f hf, mul_assoc, ← mul_assoc (gl (nU b)), ← mul_assoc (gl (nU b))]
  rfl
end

