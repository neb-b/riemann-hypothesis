module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.IntegrableOfBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Integr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0005

@[expose] public section

namespace PositivityTheory.Rg.Sw.WR

theorem wr : WRSt :=
  T.wr_of G.gauss B.clsBound K.GB.clsGainB ibp I.integr (D.densOf3 G.gauss K.GB.clsGainB I.integr)

end PositivityTheory.Rg.Sw.WR
