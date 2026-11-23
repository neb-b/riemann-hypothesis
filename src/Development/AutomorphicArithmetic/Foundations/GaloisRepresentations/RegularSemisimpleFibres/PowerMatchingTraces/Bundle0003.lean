module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormOpen
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.normOpen :
    UpperTheory.Gal.InertialTypesAlt.G.NormOpen := by
  intro F E _ _ _ _ _ _ _ _ σ _ hp n _ v
  obtain ⟨η, hη⟩ := UpperTheory.ConvolutionTheory.R.classChar2 F E hp
  have hpow := (UpperTheory.ConvolutionTheory.R.normCharPow_holds F E hp η hη).1
  have key : ∀ g : Gw n v, g ∈ normSet E n v ↔ chiAt n η v g = 1 := by
    intro g
    constructor
    · intro h
      have h1 := h η hη.1
      simp only [chiAt, h1, Units.val_one]
    · intro h χ hχ
      obtain ⟨j, -, -, rfl⟩ := hpow χ hχ
      have h1 : η.loc v (Matrix.GeneralLinearGroup.det g) = 1 := Units.ext h
      show (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = 1
      have h2 : (η ^ j).loc v (Matrix.GeneralLinearGroup.det g) = (η.loc v (Matrix.GeneralLinearGroup.det g)) ^ j := rfl
      rw [h2, h1, one_pow]
  refine ⟨?_, fun γ x => ?_⟩
  · have hs : normSet E n v = chiAt n η v ⁻¹' {1} := Set.ext fun g => key g
    rw [hs]
    exact ((UpperTheory.Gal.InertialTypesAlt.G.chiBasic F n η v).1).isClopen_fiber 1
  · have hd : Matrix.GeneralLinearGroup.det (x⁻¹ * γ * x) = Matrix.GeneralLinearGroup.det γ := by
      rw [map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det γ), mul_assoc, inv_mul_cancel, mul_one]
    rw [key, key]
    simp only [chiAt, hd]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrEx
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.trEx :
    UpperTheory.Gal.InertialTypesAlt.G.TrEx := by
  intro K _ _ _ n hn π v _ _ m hm τ hτ f hf
  haveI := hm
  let μ : Measure (normOneGL (K := K) (n := n)) := Measure.haar
  obtain ⟨χ, hχ, V, hV⟩ := Dp.exTwist K n μ π hn
  obtain ⟨⟨τ₁, h₁⟩, htw⟩ := locTw K n hn π χ v τ hτ
  obtain ⟨e, he⟩ := htw τ₁ h₁
  have hocc : Occurs μ V v τ₁ :=
    (occursIff K n μ V hV.summand v τ₁).2 ((Dp.locIff K n μ (π.twist χ) V hV v τ₁).1 h₁)
  obtain ⟨h₁, h₂, h₃⟩ := occursBasics K n μ V v m hV.summand
  obtain ⟨z, hz⟩ := h₃ τ₁ hocc (fun g => f g * chiAt n χ⁻¹ v g) ((chiBasic K n χ⁻¹ v).2.2 f hf)
  have ht := (trTw _ m (chiAt n χ v) τ τ₁ e he (fun g => f g * chiAt n χ⁻¹ v g) z).1.2 hz
  have hfun : (fun g => f g * chiAt n χ⁻¹ v g * chiAt n χ v g) = f := by
    funext g
    have h := (chiBasic K n χ v).2.1 g
    rw [mul_assoc, mul_comm (chiAt n χ⁻¹ v g), h, mul_one]
  rw [hfun] at ht
  exact ⟨z, ht⟩
end

