module

public import Formalism.BranchSandwichDivisors.StatementL
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.RatHerm
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
public import Mathlib
public import Formalism.QuotientMetricDivisors.StatementK
public import Formalism.BranchSandwichDivisors.StatementR
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer

@[expose] public section

namespace Formalism.BranchingDeterminantCap

theorem mapMu : MapMu := map_slope_mu
theorem scaleSandwich : ScaleSandwich := scale_sandwich_bound
theorem orthSum : OrthSum := orthogonal_sum_slope
theorem powMu : PowMu := power_slope_mu
theorem orthSandwich : OrthSandwich := orthogonal_sandwich_bound
theorem transferPart : TransferPart := transferPart_of mapMu powMu
theorem transferMuMax : TransferMuMax := transferMuMax_of scaleSandwich orthSum powMu
theorem transferDeg : TransferDeg := degreeTransferBound
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
theorem capConst : CapConst := capacity_constant_bound
theorem weylDimBound : WeylDimBound := weyl_dimension_bound
theorem branchMap : BranchMap := branch_map_formula
theorem xiNorm : XiNorm := xi_norm_bound

end Formalism.BranchingDeterminantCap
