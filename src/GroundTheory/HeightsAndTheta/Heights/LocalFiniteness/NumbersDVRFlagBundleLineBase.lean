module

public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.FieldNumbersDivPushForwardLocal
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0045

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForward.{u} : GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.Statement.{u} :=
  @GroundTheory.Heights₂.Heights.FieldNumbers.DivPushForward.proof.{u} GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelDimLe.proof GroundTheory.Heights₂.Heights.AutoClose.FieldNumbers_DivPushForwardLocal
