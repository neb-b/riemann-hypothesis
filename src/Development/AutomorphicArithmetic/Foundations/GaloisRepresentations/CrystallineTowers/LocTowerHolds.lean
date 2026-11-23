module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0013

@[expose] public section

namespace UpperTheory.Gal.Seam

theorem hopEx_holds : HopEx := hopExS trivial

theorem locTower_holds : LocTower := G3.locTower_of G3.vBcS_holds hopEx_holds niceBc

theorem pieceIn_holds : PieceIn := pieceInS G3.vInv_holds hopEx_holds

theorem matIn_holds : MatIn := matInS G3.vFin_holds pieceIn_holds negVan

theorem crysStep_of (h : CrystallineSemistableComparison.SmoothModelCrystalline) : UpperTheory.Gal.Int.Geo.CrysStep :=
  crysStep h niceBc locTower_holds bcCover intMap goodOf matIn_holds subAdm grCrys

end UpperTheory.Gal.Seam
