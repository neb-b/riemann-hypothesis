module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.Bundle0002
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdelicEstimatesHolds

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixWClosed
section
theorem PositivityTheory.Mix.mixW_closed : PositivityTheory.ThKG.MixW := PositivityTheory.ThKF0.mixW_of_adel PositivityTheory.Mix.adelic_estimates_holds
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ThetaTowerHermitianSecondHolds
section
theorem PositivityTheory.Mix.theta_tower_hermitian_first_holds : type_of% (PositivityTheory.ThKF0.Chr.theta_tower_hermitian_first PositivityTheory.Mix.adelic_estimates_holds) := PositivityTheory.ThKF0.Chr.theta_tower_hermitian_first PositivityTheory.Mix.adelic_estimates_holds

theorem PositivityTheory.Mix.theta_tower_hermitian_second_holds : type_of% (PositivityTheory.ThKF0.Chr.theta_tower_hermitian_second PositivityTheory.Mix.adelic_estimates_holds) := PositivityTheory.ThKF0.Chr.theta_tower_hermitian_second PositivityTheory.Mix.adelic_estimates_holds
end

