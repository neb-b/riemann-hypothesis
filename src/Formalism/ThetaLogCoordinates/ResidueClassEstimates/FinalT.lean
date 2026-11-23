module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogBinomialProperties
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.LogWeylDimensionEstimate
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.N0LeNs
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AtypicalWeightBoundOf
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

@[expose] public section

namespace Formalism.InvariantFactorPaths.BranchingDimensions.Top

theorem lemma_t_one : PathWeightBound :=
  pathWeightBound_of pathEntryBounds pathInterlacingCriterion logBinomialProperties logWeylDimensionEstimate logRankEstimate pathTailBounds logBinomialDeficit
theorem weylGT : ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ) :=
  weyl_dim_eq_gelfand_tsetlin branchingDimensionFormula

end Formalism.InvariantFactorPaths.BranchingDimensions.Top
