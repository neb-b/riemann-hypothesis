module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PPhiSeed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDetEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDenseUs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSmall
public import Development.EtaleCohomology.DivisorCycles.GoalHolds

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

theorem subLoc_holds : SubLoc := subLoc_of subSplit_of inFacts_of locConj_of locSum_of jumpCard_of
theorem phiSeed_holds : PhiSeed := phiSeed_of subLoc_holds locConj_of rootPin_of algGen_of
theorem centU_holds : CentU := centU_of zetaEx_of zetaLoc_of schurU_of charOfZeta_of algOfFix_of satCent_of
theorem detEx_holds : DetEx := detEx_of centU_holds
theorem divDet_holds : DivDet := divDet_of denseUs_of detFrob_of
theorem senWLac_holds : PositivityTheory.AutomorphicGaloisHodgeTate.Div.SenWLac := senWLac_of jumpCard_of
theorem divSet_holds : DivSet := divSet_of LateralTheory.DivDb.goal_holds senWLac_holds lacBridge_of inFacts_of
theorem divOne_holds : DivOne := divOne_of divSet_holds denseUs_of detFrob_of inFacts_of sepPin_of
theorem divAll_holds : DivAll :=
  divAll_of detEx_holds divDet_holds phiSeed_holds divOne_holds (divUniq_of denseUs_of) isoMove_of
    (frobSeed_of inFacts_of genPin_of algGen_of detFrob_of) (jumpSeed_of coverIn_of sSBlock_of subLoc_holds locConj_of jumpCard_of)
    subLoc_holds

end UpperTheory.Gal.Int.Div
