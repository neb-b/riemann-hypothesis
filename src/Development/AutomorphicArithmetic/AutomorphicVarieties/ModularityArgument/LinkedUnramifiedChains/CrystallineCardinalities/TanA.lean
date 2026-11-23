module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanAOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.OrbitCount

@[expose] public section

open UpperTheory.V

theorem UpperTheory.V.J.tanA (hP : GC.Hypotheses₂) (hL : Loc.LocalPublishedTheorems) : UpperTheory.V.J.TanA :=
  UpperTheory.V.J.tanA_of hP UpperTheory.V.Pr.degEq (UpperTheory.V.Z.J.unitOf hL)
