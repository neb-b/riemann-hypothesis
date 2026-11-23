module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2SphericalSwap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.Bundle0004

@[expose] public section

namespace PositivityTheory.Rg.BcB.N3.Final

open PositivityTheory.Rg.BcB.N3

theorem n3 : N3 :=
  Pee.galois_fixed_adelic_matrices_descend (fun k _ _ _ _ => Pee.expEmb k)
    (fun k _ _ _ _ => Pee.extremeSph_of k (Pee.sphConst k) (Pse.sphEmb k) (Pus.uniqSub k)) Psl.satLink

end PositivityTheory.Rg.BcB.N3.Final
