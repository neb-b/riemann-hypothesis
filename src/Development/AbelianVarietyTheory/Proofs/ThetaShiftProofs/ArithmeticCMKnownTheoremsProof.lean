module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem known_holds : Known :=
  have hL := GlobalTheory.firstFiveLaws
  have hh : GlobalTheory.CM.HomExtDvr := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr
  { laws := hL.1
    laws2 := hL.2.1
    ubc := hL.2.2.2.1.unifBaseChange
    laws5 := hL.2.2.2.2
    theta := GlobalTheory.thetaUnifAV_all
    n1ab := GlobalTheory.Moduli.jointExistence_and_moduliScheme.2
    n1c := GlobalTheory.closing_of_abelianSchemeLaws
    n5 := GlobalTheory.arcClause_closed
    models := GlobalTheory.Moduli.jointExistence_and_moduliScheme.1
    hom := hh
    key := GlobalTheory.KeyFam.keyFormula_holds
    cm := GlobalTheory.cmExists_closed
    deg := GlobalTheory.CM.PureDeg.degSt GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all hL.1 hh
    ev := fun E _ _ _ H Dw l Xo c => (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1 }

end GlobalTheory.ArcCM
