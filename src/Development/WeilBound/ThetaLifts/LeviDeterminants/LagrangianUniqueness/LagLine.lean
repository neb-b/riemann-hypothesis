module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LineCore
public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.HasDerivAtEc

@[expose] public section

theorem PositivityTheory.ThKF0.lagLine : PositivityTheory.ThKF0.LagLine := PositivityTheory.ThKF0.LineCore.lagLine_of PositivityTheory.ThKF0.realTest
