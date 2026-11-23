module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.AbelianHodgeDeRham.Bridge

@[expose] public section

namespace AbelianDeRhamStructureFromPages.Adrs

theorem abelianDeRhamStructure_of_page (P : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage) : GlobalTheory.Published.AbelianDeRhamStructure :=
  let hL := GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations
  let hH := FubiniStudyChowHeightFormula₂.Hdr.abelianHodgeDeRham_of_page P
  ⟨GlobalTheory.Proof.abelianDeRhamFree_of_hodge hL hH,
    GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift hL hH,
    GlobalTheory.AbelianBaseChange.abelianDeRham_baseChange_of_smoothLift hL hH⟩

end AbelianDeRhamStructureFromPages.Adrs
