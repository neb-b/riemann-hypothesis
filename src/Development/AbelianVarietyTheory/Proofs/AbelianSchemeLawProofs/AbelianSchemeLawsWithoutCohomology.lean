module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polBaseChange_holds : PolBaseChangeSt :=
  polBaseChange_of_relAmple_local _root_.GlobalTheory.AmpleLocal.relAmple_of_locally

theorem cubical_extends_holds : Semi.cubical_extendsSt.{0} :=
  (cubical_extends_and_extendGen
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _root_.GlobalTheory.GenExtend.existsUnique_gen_extend).1

theorem laws_without_cohomology :
    GlobalFnsSt ∧ RigiditySt ∧ PolBaseChangeSt ∧ Semi.lemmaBSt.{0} ∧ Semi.cubical_extendsSt.{0} :=
  ⟨globalFns_holds, rigidity_holds, polBaseChange_holds, lemmaB_holds, cubical_extends_holds⟩

end GlobalTheory
