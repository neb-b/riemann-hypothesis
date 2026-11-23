module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.PropEG2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V
open GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace Ad3P

def SEig : Prop :=
  ∀ (k N : ℕ) [NeZero N], 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ),
    Ad3.IsForm k N χ g.f g.a ∧ Ad3.IsEig k N χ g.a

end Ad3P
