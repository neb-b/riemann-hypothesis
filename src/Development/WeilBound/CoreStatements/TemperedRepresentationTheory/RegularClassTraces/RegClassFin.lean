module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.RegularCuspidalTrace

def IsCuspFn {D : D7} {V : HSp D} (f : GA D V → ℂ) : Prop :=
  ∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f

def RegClassInt : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] (f : GA D V → ℂ), f ∈ CcGA V → IsCuspFn f →
    ∀ γ : GF V, IsRegSS γ.1.1 →
      Integrable (descend (GQ V) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (GQ V) (rat V γ) f)) (autMeasure V μ)

def RegClassFin : Prop :=
  ∀ (D : D7) (V : HSp D) (f : GA D V → ℂ), f ∈ CcGA V →
    {𝔬 : Set (GF V) | (∃ γ : GF V, IsRegSS γ.1.1 ∧ 𝔬 = {δ | IsConj γ δ}) ∧
      ∃ (x : GA D V) (δ : GF V), δ ∈ 𝔬 ∧ f (x⁻¹ * rat V δ * x) ≠ 0}.Finite

end MainStatements.RegularCuspidalTrace

end
