module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.LocalConditionRankThreeLinkOfInertiaOrdinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.InertiaRankTwo.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.ConjLeftPosAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.NormalValuationBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0079
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0076
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymmetricCubeTheoremOfEndomorphisms
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0072
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0058
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MixSeedOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnEnds
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Win.Dn
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem ends_rank_three_of_local' (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : LocalConditionRankThreeEvenLevel := fun Ω _ _ _ l _ c _ N _ e ψ hev η σ g₁ B M h =>
  Keep.keeps3E (_root_.UpperTheory.V.W.locPrints_of_litN hH.litN) hU Ω l c N e ψ η σ g₁ B M h hev
theorem ends_of_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hE : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt) (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  have h3 := localConditionRankThreeLink_of_inertia_ordinary ineOfKer_of flagAll_of
  ⟨_root_.UpperTheory.V.Z.Win.Dn.gdEnd_of_frame_linkedEnd_downCsdK_descent hH h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) potTwo_of (inertiaConditionRankTwoLink_of_inertia UpperTheory.V.Keep.ineOf) (Fr.gd_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH) (_root_.UpperTheory.V.Af.rankTwoAutomorphyDescends_of_printsH hH)
      (_root_.UpperTheory.V.Br.autNewformA_of_printsH hH) (_root_.UpperTheory.V.Sd.twist_conjugate_selfDual hH.toClassicalTheorems) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hH.toClassicalTheorems),
    _root_.UpperTheory.V.Pr.symmetric_cube_theorem_of_endomorphisms_alt (_root_.UpperTheory.V.Z.Win.Dn.hostEnd_of_loc3_frame_linkedEnd_downCsdK h3 (_root_.UpperTheory.V.Z.Win.Dn.ends_rank_three_of_local' hH hU) (Fr.host_ex (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hH.litN)) hE (_root_.UpperTheory.V.Z.Win.Dn.downCsdK_of_printsH hH))⟩
theorem ends_u_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (hU : J.LinkedUnlE) : _root_.UpperTheory.V.Pr.GdEndAlt ∧ _root_.UpperTheory.V.Aut.ThmS6Core_s :=
  _root_.UpperTheory.V.Z.Win.Dn.ends_of_alt hH (_root_.UpperTheory.V.Z.Sym.Top.linkedEnd_alt hH (_root_.UpperTheory.V.Z.Win.Birth.seed2_alt hH) (_root_.UpperTheory.V.Z.Sym.W.unitary_three_automorphy_dense_of_prints hH)) hU
end UpperTheory.V.Z.Win.Dn
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedIIZ
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
namespace UpperTheory.V.Z.Bc
theorem seedII_Z_alt (h : _root_.UpperTheory.V.Z.Bc.Hypotheses4Z') (hI : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP) : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  _root_.UpperTheory.V.Z.Bc.seedII_of_p_alt (_root_.UpperTheory.V.Z.Win.Birth.mixOfP (_root_.UpperTheory.Esk.mixSeed_of_alt h.h (_root_.UpperTheory.V.Z.Bc.propMHolZ_alt h))) hI
end UpperTheory.V.Z.Bc
end
end

