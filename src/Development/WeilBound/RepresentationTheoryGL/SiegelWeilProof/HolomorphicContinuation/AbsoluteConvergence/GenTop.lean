module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreP
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IEqOfSL
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ProjOpOf

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt

theorem genCore : Iwa → CayleyBlocksInvertible → KAK → Mult → SecZero → DerivativeVacuumDilations → CycSec → HolParam → Glue → LC → GenCore :=
  fun hI hD hK hM hS hDF hC hH hG hLC =>
    genCore_of (Proj.projOp hI hM) (tsGenC_of hD hK hM hS hDF hH hLC tsbFacts) (basis hI hD hM hC hH)
      (farRightC hI hD hM hH) hS hLC hH hG

theorem absThm_of' (hV : VacOut) (hI : Iwa) (hD : CayleyBlocksInvertible) (hK : KAK) (hM : Mult) (hS : SecZero) (hDF : DerivativeVacuumDilations)
    (hC : CycSec) (_hSph : Sph) (hH : HolParam) (hG : Glue) (hLC : LC) (_hN : NullIff) : AbsThm :=
  absThm_gen hV (Proj.projOp hI hM) (tsGen hI hD hK hM hS hDF hH hLC) (basis hI hD hM hC hH) (farRight hI hD hM hH)
    hS hLC hH hG

end PositivityTheory.Rg.Sw.AbsSt
