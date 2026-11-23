module

public import Formalism.GaussJetBounds.GaussJetProofs.ThmAGaussOf
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0005
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0006
public import Formalism.GaussJetBounds.GaussJetProofs.Bundle0004

@[expose] public section

namespace Formalism.DworkPowerSeriesWeights

theorem thmAGauss : ThmAGauss :=
  thmAGauss_of admissibleTransfer frame_jet_evaluation labelsExist_statement gauss_sum_powers

end Formalism.DworkPowerSeriesWeights
