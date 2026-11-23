module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.CechHEquivCohOnCechCubeMapOver
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOfPf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.Bundle0001

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem seamHopEx_holds : UpperTheory.Gal.Seam.HopEx := by
  intro l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap k Ω) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  exact (hopSpec_holds l hl H Ω g d hd).1

theorem locTower_holds : UpperTheory.Gal.Seam.LocTower := locTower_of vBcS_holds seamHopEx_holds UpperTheory.Gal.Seam.niceBc

theorem traceSplit_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.TraceSplit := by
  intro k _ Z Y W q s _ _ c _ _ I _ σ hσ hS a b y
  exact hodgeTr_holds k a b q (s ≫ q) s rfl W (c ≫ q) c rfl I σ hσ hS y

theorem hodgeBC_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC :=
  jHBC jHBasis jHEquiv jHCube jHAffine jHCover (jHOmega jHEquiv jHForms jHSections jHAffine) PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.cech_holds
    (jHTrace jHFun jHAffine)

theorem coverOp_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := jCoverOp etnGood_holds @bcSplits_holds @bcGal_holds corrUniq_holds

theorem lowHodge_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge :=
  jLowHodge hodgeGood_holds @bcGood_holds.{0} fEtBasic_holds
    (jHodgeOpBc @bcSplits_holds hodgeTr_holds (jTrBc.{0} @bcSplits_holds)) @coverInv_holds.{0} @liesOp_holds.{0}

theorem hopLies_holds : HopLies := jHopLies etGood_holds @bcGood_holds.{1} fEtBasic_holds hopSpec_holds @liesOp_holds.{1}

theorem lowPiece_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := jLowPiece hopLies_holds pieceLe_holds

theorem lowCov_holds : LowCov :=
  jLowCov @galClosD_holds @bcSplits_holds @bcGal_holds @jGenIso (jModBc UpperTheory.Gal.Seam.goodOf)

theorem jumpStep_of (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (hC : CrysStep) (hR : RepEx) : JumpStep :=
  PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpStep_of
    (PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpCore_of hS (jLowNice fEtBasic_holds) lowHodge_holds lowPiece_holds (matEx_of hR)
      (jLocalMat UpperTheory.Gal.Seam.niceBc seamHopEx_holds locTower_holds) (coverLow_of_cov PositivityTheory.AutomorphicGaloisHodgeTate.G8.coverOf lowCov_holds)
      (jBridgeInt UpperTheory.Gal.Seam.intMap) (jBCTower UpperTheory.Gal.Seam.niceBc)
      (PositivityTheory.AutomorphicGaloisHodgeTate.G8.locE_of hodgeBC_holds traceSplit_holds coverOp_holds) PositivityTheory.AutomorphicGaloisHodgeTate.G8.OccMove_holds
      PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpsEx_holds jConjBridge jJumpOfHT2) hC

end UpperTheory.Gal.G3
