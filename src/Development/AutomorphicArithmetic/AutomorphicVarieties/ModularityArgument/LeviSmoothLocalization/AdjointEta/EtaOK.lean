module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lin3 (ν c : kˣ →* ℂˣ) : ℂ[X] := lin (ν * c) * lin c * lin (ν⁻¹ * c)

def Ram3 (ν c : kˣ →* ℂˣ) : Prop := ¬ IsUnram (ν * c) ∧ ¬ IsUnram c ∧ ¬ IsUnram (ν⁻¹ * c)

end Loc

def tri (a x : ℂˣ) : Multiset ℂ := (({a * x, x, a⁻¹ * x} : Multiset ℂˣ)).map fun b : ℂˣ => (b : ℂ)

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
