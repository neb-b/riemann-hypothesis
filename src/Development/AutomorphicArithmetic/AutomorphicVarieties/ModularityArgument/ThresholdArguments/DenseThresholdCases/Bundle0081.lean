module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0080
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0077
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0079

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcIndCs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEndsTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
theorem ends0_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_u_alt hH (_root_.UpperTheory.V.Z.J.linkedUnlE_holds_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH))
end UpperTheory.V.Z.Win.Dn
end
end

