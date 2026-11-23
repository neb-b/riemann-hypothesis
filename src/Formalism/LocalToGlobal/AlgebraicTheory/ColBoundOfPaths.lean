module

public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementStep
public import Formalism.LocalToGlobal.Divisibility.JetBounds.Bundle0001
public import Formalism.GaussJetBounds.FinalB
public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
public import Mathlib
public import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.TranslateCocycles.StatementHC
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
public import Formalism.SizeWindowBrackets.SBrDiv
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
public import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace

@[expose] public section

namespace Formalism.L2.AlgTh

theorem logDerJets : LogDerJets := log_derivative_jets_integral
theorem powLogDer : PowLogDer := power_log_derivative_jets
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
theorem linScale : LinScale := linear_scaling_jets
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
theorem etPower : EtPower := etPower_of unitKerInt
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
theorem tensZEt : TensZEt := tensor_integral_torsion
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
theorem scalarConst : ScalarConst := scalar_constant_value
theorem xiSwap : XiSwap := xi_swap
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
