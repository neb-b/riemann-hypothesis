module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyInverseConjTransposeMulApply
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0012
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenTop

@[expose] public section

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem absThm_of (hLV : LV) (hC : Cyc) (hLC : LC) (hN : NullIff) : AbsThm := by
  have hZ := secZero hN
  have hS := sph iwa mult
  have hT := thSph_of kAK mult derivative_vacuum_section hS hZ holParam hLC hN
  have hV := vacOut_of' detU1 (locOp hLV iwa mult holParam) holParam hT
  exact absThm_of' hV iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) hS holParam glue hLC hN

theorem genCore_top (hC : Cyc) (hLC : LC) (hN : NullIff) : GenCore := by
  have hZ := secZero hN
  exact genCore iwa detU1 kAK mult hZ derivative_vacuum_section (cycSec_of hC hZ secDer) holParam glue hLC

end PositivityTheory.Rg.Sw.AbsSt
