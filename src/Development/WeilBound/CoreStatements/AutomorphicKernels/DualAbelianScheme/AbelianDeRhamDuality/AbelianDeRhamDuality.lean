module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DualAbelianScheme.AbelianDeRhamDuality.SurjAllOfHodge
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianDeRhamPage
public import Development.WeilBound.CoreStatements.AbelianDeRhamStructure.AbelianDeRhamPages.AbelianDeRhamStructureOfPage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126

@[expose] public section

set_option autoImplicit false

namespace PositivityTheory.DualRT

open GlobalTheory.Published
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open CrystallinePoints.Pd

theorem surjAll : CrystallinePoints.Pd.SurjAll := by
  intro R _ A _ g hAb hsm
  haveI := hAb
  haveI : IsProper A.hom := IsAbelianScheme.proper
  have hs : A.hom ≫ 𝟙 (Sp R) = A.hom := Category.comp_id _
  refine toPicard_surjective _ ?_ ?_
  · rw [hs]
    exact (GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne A.hom IsAbelianScheme.smooth inferInstance inferInstance).2
  · rw [hs]
    exact (MainStatements.Hodge.Free.abelianHodgeDeRham R A g hAb hsm).2.2.2.2.1.2.2

theorem duality : AbelianDeRham.Duality :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  CrystallinePoints.Pd.duality_of_surjAll (GlobalTheory.abelianDeRhamStructure_toFree hS) hS.2.1 hS.2.2 surjAll

theorem abelianDeRham : AbelianDeRham :=
  have hS := AbelianDeRhamStructureFromPages.Adrs.abelianDeRhamStructure_of_page MainStatements.Hodge.Free.abelianDeRhamPage
  have hF := GlobalTheory.abelianDeRhamStructure_toFree hS
  ⟨hF, hS.2.1, hS.2.2, AbelianDeRham.rigid_of_free_of_crystallineDeRham hF FubiniStudyChowHeightFormula₂.Adr.crystallineDeRham, duality⟩

end PositivityTheory.DualRT
