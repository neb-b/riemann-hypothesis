module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftUnr
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTwistRamifiedCharNeSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

@[expose] public section

open NumberField IsDedekindDomain

theorem UpperTheory.ConvolutionTheory.Sph.quadLiftUnr :
    UpperTheory.ConvolutionTheory.Sph.QuadLiftUnr := by
  intro K M _ _ _ _ _ _ _ h2 a ha π ⟨w, hram, B, hB⟩
  haveI : Algebra.IsQuadraticExtension K M := ⟨h2⟩
  haveI : IsGalois K M := inferInstance
  have hp : (Module.finrank K M).Prime := h2 ▸ Nat.prime_two
  exact UpperTheory.ConvolutionTheory.Sph.liftUnr K M hp a ha π fun η hη =>
    _root_.GlobalTheory.TwistRamified.twist_ne K a ha _ η (w.under (𝓞 K)) B hB ((UpperTheory.ConvolutionTheory.Sph.normRam K M hp w hram).2.2 η hη)
