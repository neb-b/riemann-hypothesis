module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.HomExtendsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.HomExtExamples

theorem homExtendsOverDVR_holds : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR :=
  fun T _ _ _ K _ _ _ G G' _ _ => GlobalTheory.semiAbelian_hom_extends_uniquely_dvr T K G G'

theorem homExtendsOverDVR_iff : GlobalTheory.IndefiniteRowSideFullHecke.HomExtensionOverDVR.HomExtendsOverDVR ↔ GlobalTheory.LN.HomExtSt :=
  ⟨fun h T K _ _ _ _ _ _ => h T K, fun h T _ _ _ K => h T K⟩

theorem homExtSt_holds : GlobalTheory.LN.HomExtSt := homExtendsOverDVR_iff.1 homExtendsOverDVR_holds

end GlobalTheory.HomExtExamples
