module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2LinkedPair
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0002

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GL2_spherical_swap : GL2SphericalSwap k := fun a b hab => by
  by_cases hL : unrChar k a = unrChar k b * absPow k 1
  · exact PositivityTheory.Rg.BcB.N3.GL2LinkedPair.linked a b hL
  · exact unl a b hL hab

theorem sphEmb : SphEmb k :=
  sphEmb_of k (GL2_spherical_swap k) (PositivityTheory.Rg.BcB.N3.PseStage.stageLift k) PositivityTheory.Rg.BcB.N3.PseExp.expSph
    PositivityTheory.Rg.BcB.N3.PseSat.satPerm PositivityTheory.Rg.BcB.N3.PseBub.bubble

end PositivityTheory.Rg.BcB.N3.Pse
