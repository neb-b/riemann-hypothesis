module

public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

theorem rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin

theorem heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter :=
  GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin

end PositivityTheory.Stage1.PM
