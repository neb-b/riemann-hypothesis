module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0007
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0002

@[expose] public section

namespace PositivityTheory.ThKClose

theorem domWeil_of (h : PositivityTheory.ThKEst.DomWeilU) : PositivityTheory.ThKEst.DomWeil := PositivityTheory.ThKEst.domWeil_of_U h

theorem soSemi_of (h : PositivityTheory.ThKEst.SoSemiU) : PositivityTheory.ThKEst.SoSemi := PositivityTheory.ThKEst.soSemi_of_U h

end PositivityTheory.ThKClose
