module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Base

namespace UpperTheory.V.Z.Bc

structure HypothesesZ : Prop where
  af : Af.Hypotheses₂
  eg : PropEG
  up : UpSol

end UpperTheory.V.Z.Bc
