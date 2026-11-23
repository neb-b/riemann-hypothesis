module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PKey
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.TkFcPzTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.Bundle0001

@[expose] public section

namespace PositivityTheory.KB

open AffineStabilizerVanishing

theorem sHecke_of (_hCh : SChain) (_hEv : SEv) (_hSep : SSep) (_hSt : SStab) (_hFin : SFin) (_hAff : SAff) :
    SHecke :=
  assemble _hCh _hEv _hSt _hFin _hAff (pKey (pTransfer pCobSub pEvDC)) pHeckeFormal
    (pHeckeKer (pTransfer pCobSub pEvDC) pEvDC) pIndex pStabK

end PositivityTheory.KB
