module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryRankTwoFlags
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0078
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdjointLiftFromEisensteinSeedOfHyps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSeedInW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0070
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0069
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0054
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Narrow

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedUnlEHolds
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.J
open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.J
theorem linkedUnlE_holds_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : LinkedUnlE :=
  have hN := hH.litN
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linkedUnlE_alt hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) (_root_.UpperTheory.V.Z.J.D.modularity_n_of_printed_mult_comp hH Z.Mult.mult_free Z.Mult.compOf_free) levEx
    (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2 (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
    (tanA (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hN) (_root_.UpperTheory.V.W.locPrints_of_litN hN)) (_root_.UpperTheory.V.Th.core_alt_bis hH (_root_.UpperTheory.V.W.cohP_alt hN))
end UpperTheory.V.Z.J
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.Sym.Top
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem linkedEnd_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt :=
  have hA := hH.toClassicalTheorems
  have hN := hA.litN
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) levEx (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2
    (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
end UpperTheory.V.Z.Sym.Top
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryThreeInputsOfLiterature
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Sym.W
theorem weight_compatible_descent (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility :=
  ⟨hH.toClassicalTheorems, _root_.UpperTheory.V.Z.Win.Gu.galUnitaryT_of_printsH_of_bcSpeh_of_rT hH (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge hH.litN.aut.bc hH.litN.loc.bern)) hR,
    Z.Win.compatTOf hR Z.Win.plainRec, _root_.UpperTheory.V.Z.Desc.W.same_of_prints_of_rT hH.toClassicalTheorems hR, Z.Win.plainRec, Top.descUse_of_weak hH.descU⟩
theorem adjoint_automorphy_w_of_printed_hida_window (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : AdAutW := _root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_pure_weight_adjoint_lift (_root_.UpperTheory.V.Z.Sym.W.weight_compatible_descent hH hR) (_root_.UpperTheory.V.Z.Sym.W.adjoint_lift_w_of_literal_automorphy_spec_out hH.litN specOutS)
theorem unitary_three_automorphy_dense_of_prints_and_row (hH : _root_.UpperTheory.V.Af.HypothesesH') (hR : Z.Win.RowT) : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.adjoint_lift_from_eisenstein_of_propagation (_root_.UpperTheory.V.Z.Sym.W.prop_eg_w_of_printed_hida hH) (_root_.UpperTheory.V.Z.Sym.W.seedInW_alt hH) (_root_.UpperTheory.V.Z.Sym.W.adjoint_automorphy_w_of_printed_hida_window hH hR)
theorem unitary_three_automorphy_dense_of_prints (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense := _root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints_and_row hH (_root_.UpperTheory.Gal.SV.rowOf' hH.litN.aut.gal)
end UpperTheory.V.Z.Sym.W
end
end

