module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementP

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def WeylGT : Prop :=
  BranchDim → ∀ (n : ℕ) (μ : Fin n → ℤ), Antitone μ → weylDim n (extW μ) = (Formalism.InvariantFactorPaths.GelfandTsetlinBases.dGT n μ : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
