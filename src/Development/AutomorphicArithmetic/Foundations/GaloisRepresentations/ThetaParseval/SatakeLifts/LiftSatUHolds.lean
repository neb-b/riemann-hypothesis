module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatContra
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatInvT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairSatPf

@[expose] public section

namespace UpperTheory.Gal.TP.Loc

theorem liftIso_holds : LiftIso :=
  liftIso_of (pairOfLift leftSmooth keepsSB modelDict separates) srcGood contraIrr (contraUnit contraIrr)

theorem liftSat_holds : LiftSat :=
  liftSat_of liftIso_holds srcGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr)) satTwist satInvT satDet
    satProd segInv

theorem pairSat_holds : PairSat :=
  pairSat liftSat_holds pullGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr))

theorem liftSatU_holds : LiftSatU := liftSatU pairSat_holds compUnit

end UpperTheory.Gal.TP.Loc
