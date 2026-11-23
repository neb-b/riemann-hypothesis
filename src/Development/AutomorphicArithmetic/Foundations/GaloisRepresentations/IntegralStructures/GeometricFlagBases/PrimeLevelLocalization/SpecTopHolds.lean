module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.ExistsUnitaryGroupDatumOfVectorExponentSpectral
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConjHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecTopG

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.Pl

theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds

theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds

end UpperTheory.Gal.Int.Geo.Pl
