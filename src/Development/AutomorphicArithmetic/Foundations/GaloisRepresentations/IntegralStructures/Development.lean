module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ToCoreK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.CongFinOddOfLvLac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.GaloisLocalGlobalOfLocalGlobalCompatibility
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.LimFinOddOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.MainFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightEmbeddingOverPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.GaloisCompatUnlinkedSupportOfSpherical
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedOfUnlinked

@[expose] public section

namespace UpperTheory.Gal.Int

open GlobalTheory.CongL

def recT : UpperTheory.GalStar.RecNotion := fun h rc => UpperTheory.Zero.LLC.IsRecT h rc

theorem coreAll_of (seed : SeedFinOdd) (cong : CongFinOdd) (up : UpperTheory.TP.TLiftK) : GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core
    (UpperTheory.Gal.Int.Core.toCoreK up UpperTheory.Gal.ClosedPhiFromClosedTrace.congPhi_holds UpperTheory.Gal.Desc.descOffT (UpperTheory.Gal.Lim.limFinOdd_of seed cong))

theorem rest (h : GlobalTheory.RoadU.CoreAll) : UpperTheory.GalStar.Row0 recT := by
  have hspherical := UpperTheory.Gal.ToralGalois.galoisCompat_unlinkedSupport_of_spherical h
  exact UpperTheory.Gal.Int.Row.galoisLocalGlobal_of_localGlobalCompatibility h hspherical
    (UpperTheory.Gal.ToralGalois.R2.localGlobalCompatAtIwahoriFixed_of_unlinked hspherical)

theorem galoisLocalGlobal_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0 recT :=
  rest (coreAll_of (UpperTheory.Gal.Int.Div.seedFinOdd_of_geoOne geo) (UpperTheory.Gal.Int.Cong.congFinOdd_of_ex UpperTheory.Gal.Wt.wtLacEx_holds) up)

theorem galoisLocalGlobalStrong_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT :=
  UpperTheory.GalStar.Row0.row0b recT (galoisLocalGlobal_of_geometry_lift geo up)

end UpperTheory.Gal.Int
