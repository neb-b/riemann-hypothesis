module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.Development
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.WeightOneGeometricRealization

@[expose] public section

namespace UpperTheory.Gal.Int

theorem galoisRepresentations_of_thetaLift (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT := galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up

end UpperTheory.Gal.Int
