module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004

@[expose] public section

open NumberField GlobalTheory.CuspRep

namespace PositivityTheory.S2.Clozel

theorem clozelPurity_of_bounded : GlobalTheory.Published.CuspFormsBoundedGL → GlobalTheory.Published.ClozelPurity :=
  fun hB E _ _ _ a ha π h =>
    GlobalTheory.CompanionTheory.ClozelPurity.purity hB E a ha π (fun τ => ⟨_, GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ⟩) h

end PositivityTheory.S2.Clozel
