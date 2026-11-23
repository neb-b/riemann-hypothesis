module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TopMainZj
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Bundle0001

@[expose] public section

theorem UpperTheory.One.vwin_of_row (h : UpperTheory.V.Z.Win.RowT) : UpperTheory.Top.VWin :=
  UpperTheory.One.Join.automorphic_window_of_inputs
    ⟨h⟩ UpperTheory.BaseChangeIdentities.baseChangeN h
