module

public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Mathlib
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

section Frob
open scoped Matrix.Norms.Frobenius

end Frob

noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

section FrobG
open scoped Matrix.Norms.Frobenius

end FrobG


end Formalism.HermitianLatticeCounting.P
