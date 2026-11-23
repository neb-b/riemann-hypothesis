module

public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0002
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0004
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0003
public import Formalism.EllipticTorsion.Bundle0002
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne
public import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
public import Mathlib
public import Formalism.EllipticTorsion.Bundle0003
public import Formalism.FormalGroupLog.LogDeterminesLaw
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.LogWeight
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CoefficientWeightsLemmaTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0001
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
public import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluUSeries
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree

@[expose] public section

universe u

namespace Formalism.ELL

theorem legendreInv : LegendreInv.{u} := legendre_invariant
theorem deuringInv : DeuringInv.{u} := deuring_invariant
theorem modelLegendre : ModelLegendre.{u} := legendre_model
theorem modelDeuring : ModelDeuring.{u} := deuring_model
theorem modelUnit : ModelUnit.{u} := by
  apply modelUnit_of <;> first | exact modelLegendre | exact modelDeuring | exact legendreInv | exact deuringInv
theorem intValuedZp : IntValuedZp.{u} := integer_valued_padic_integers
theorem nAddSubgroup : NAddSubgroup.{u} := N_additive_subgroup
theorem nZpSmul : NZpSmul.{u} := N_padic_integer_smul
theorem nPderiv : NPderiv.{u} := N_partial_derivative

theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion

theorem isoExpand : IsoExpand.{u} := isogeny_expansion
theorem isoVanish : IsoVanish.{u} := isogeny_vanishing

theorem changeIntegral : ChangeIntegral.{u} := change_of_variables_integral

theorem lwP₂ : LogWeight.{u} := logarithm_coeff_weight
theorem unitCancel : UnitCancel.{u} := unit_cancellation

theorem compExpWeight : CompExpWeight.{u} := comp_exp_coeff_weight

theorem lemma2Weights : EllipticTorsionWeights.{u} := coefficient_weights_lemma_two
theorem frobExpand : FrobExpand.{u} := frobenius_expansion

theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
theorem wSeriesLead : WSeriesLead.{u} := wSeriesLeadingTerm_holds
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint | exact wSubstUnique | exact wSeriesUnique | exact wSeriesLead

theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := by
  apply formal_group_points_param_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
theorem formal_group_points_hom : FormalGroupPointsHomomorphism.{u} := by
  apply formal_group_points_hom_of <;> first | exact wSubstUnique | exact wChordSubst | exact formal_group_points_param | exact wFormalGroup | exact wChordSeries | exact wPoint

theorem veluIntegralModel : VeluIntegralModel.{u} := velu_integral_model
theorem veluUSeries : VeluUSeries.{u} := velu_u_series

theorem cubeTwo : CubeTwo.{u} := cube_two
theorem cubeThree : CubeThree.{u} := chordDeterminantFactor_holds

end Formalism.ELL
