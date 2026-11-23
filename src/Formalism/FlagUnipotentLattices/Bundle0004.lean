module

public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.IdealsOfNormEqIndexSet
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SchurAverage
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MeasurePreservingPiCompProd
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SumComplexEmbeddingsEqSumInfinitePlace
public import Mathlib
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.HarderNarasimhan.Statement
public import Formalism.FlagUnipotentLattices.Bundle0002
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ColonCountWeighted
public import Formalism.FlagUnipotentLattices.Bundle0001
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LocalIntegralStructure
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ComplexMultiplicationRoot

@[expose] public section

-- bundled from Formalism.FlagUnipotentLattices.AutBoundOfMinkowskiBound
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem nFJZero : Formalism.HermitianLatticeCounting.S6.NFJZero := by
  first
    | exact Formalism.HermitianLatticeCounting.P.normalFormZero
    | exact Formalism.HermitianLatticeCounting.P.S6e.normalFormZero

theorem normalForm : Formalism.HermitianLatticeCounting.S6.NormalForm := by
  first
    | exact Formalism.HermitianLatticeCounting.P.existsNormalForm
    | exact Formalism.HermitianLatticeCounting.P.S6e.existsNormalForm

theorem normSgBound : Formalism.HermitianLatticeCounting.S6.NormSgBound := by
  first
    | exact Formalism.HermitianLatticeCounting.P.norm_singular_value_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.norm_singular_value_bound

theorem finalSum : Formalism.HermitianLatticeCounting.S6.FinalSum := by
  first
    | exact Formalism.HermitianLatticeCounting.P.final_sum_bound
    | exact Formalism.HermitianLatticeCounting.P.S6e.final_sum_bound

end Formalism.HermitianLatticeCounting.Final.S6
end

-- bundled from Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
section
namespace Formalism.HermitianLatticeCounting.Final.LatticeSumBounds

theorem absA : Formalism.HermitianLatticeCounting.LatticeSumBounds.AbsA := Formalism.HermitianLatticeCounting.P.absolute_value_bound
theorem wedgeHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.WedgeHadamard := Formalism.HermitianLatticeCounting.P.wedge_hadamard_inequality
theorem cramerUpper : Formalism.HermitianLatticeCounting.LatticeSumBounds.CramerUpper := Formalism.HermitianLatticeCounting.P.leadingMinorColumnReplace
theorem gramHadamard : Formalism.HermitianLatticeCounting.LatticeSumBounds.GramHadamard := Formalism.HermitianLatticeCounting.P.gram_hadamard_inequality
theorem lemmaP : Formalism.HermitianLatticeCounting.LatticeSumBounds.LemmaP := Formalism.HermitianLatticeCounting.P.prodMaxInvLeSq
theorem packing : Formalism.HermitianLatticeCounting.LatticeSumBounds.Packing := Formalism.HermitianLatticeCounting.P.packing_bound
theorem traceLower : Formalism.HermitianLatticeCounting.LatticeSumBounds.TraceLower := Formalism.HermitianLatticeCounting.P.traceLowerBound
theorem classNumberBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ClassNumberBound := Formalism.HermitianLatticeCounting.P.class_number_upper_bound
theorem c2a : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesOfIndexLePow := Formalism.HermitianLatticeCounting.P.ideal_count_statement
theorem c2b : Formalism.HermitianLatticeCounting.LatticeSumBounds.CardSubmodulesAndLinearEquivBounds := Formalism.HermitianLatticeCounting.P.submodule_automorphism_count
theorem unipotentReduce : Formalism.HermitianLatticeCounting.LatticeSumBounds.UnipotentReduce := Formalism.HermitianLatticeCounting.P.unitriangularReduction
theorem leadingMinorInvariant : Formalism.HermitianLatticeCounting.LatticeSumBounds.LeadingMinorInvariant := Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant
theorem minorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.MinorBound := Formalism.HermitianLatticeCounting.P.normMinorMulLe
theorem monomialMinor : Formalism.HermitianLatticeCounting.LatticeSumBounds.MonomialMinor := Formalism.HermitianLatticeCounting.P.normMinorMonomialLe
theorem omegaNorm : Formalism.HermitianLatticeCounting.LatticeSumBounds.OmegaNorm := Formalism.HermitianLatticeCounting.P.complementNormIdentity
theorem boxCount : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCount := Formalism.HermitianLatticeCounting.P.box_count_alt
theorem kernelRowSpace : Formalism.HermitianLatticeCounting.LatticeSumBounds.KernelRowSpace := Formalism.HermitianLatticeCounting.P.cofactorVectorKernel
theorem cofVecAdjugate : Formalism.HermitianLatticeCounting.LatticeSumBounds.CofVecAdjugate := Formalism.HermitianLatticeCounting.P.adjugateLastColumnEqCofactor
theorem projQuotCard : Formalism.HermitianLatticeCounting.LatticeSumBounds.ProjQuotCard := Formalism.HermitianLatticeCounting.P.projective_quotient_card
theorem degFactorBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegFactorBound := Formalism.HermitianLatticeCounting.P.prodHyperbolicRatioSqLe
theorem deNonDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeNonDegBound := Formalism.HermitianLatticeCounting.P.nondegenerateFactorBound
theorem deDegBound : Formalism.HermitianLatticeCounting.LatticeSumBounds.DeDegBound := Formalism.HermitianLatticeCounting.P.degenerateFactorBound
theorem nonDegRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegRow := Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
theorem degRow : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegRow := Formalism.HermitianLatticeCounting.P.degenerateRowBound
theorem nonDegSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.NonDegSum := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe
theorem degSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.DegSum := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe
theorem smallTerm : Formalism.HermitianLatticeCounting.LatticeSumBounds.SmallTerm := Formalism.HermitianLatticeCounting.P.prodMinLeOfProdRatio
theorem single_row_lattice_sum_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.SingleRowBound := Formalism.HermitianLatticeCounting.P.singleRowBound
theorem lattice_exp_sum_upper_bound : Formalism.HermitianLatticeCounting.LatticeSumBounds.ExpSumLe' := Formalism.HermitianLatticeCounting.P.expSumLe'
theorem gainSqrt : Formalism.HermitianLatticeCounting.LatticeSumBounds.GainSqrt := Formalism.HermitianLatticeCounting.P.invSqrtPowLeExp
theorem boxCountO : Formalism.HermitianLatticeCounting.LatticeSumBounds.BoxCountO := Formalism.HermitianLatticeCounting.P.box_count_big_O
theorem latticeSum : Formalism.HermitianLatticeCounting.LatticeSumBounds.LatticeSum := Formalism.HermitianLatticeCounting.P.lattice_sum_alt
theorem homRestrictIndex : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := Formalism.HermitianLatticeCounting.P.cardCokernelRestriction

theorem coveringO_of_transference (h : Formalism.HermitianLatticeCounting.LatticeSumBounds.Transference) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := Formalism.HermitianLatticeCounting.P.coveringO_of_transference h

end Formalism.HermitianLatticeCounting.Final.LatticeSumBounds
end

-- bundled from Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
section
open Finset MeasureTheory NumberField
open scoped ComplexOrder

noncomputable section

namespace Formalism.HermitianLatticeCounting.S7

open Formalism.NuclearRankWeightBounds.D (lead hs q0)

def decExp (h : ℝ) (q : ℕ) (t : ℝ) : ℝ := h / 8 * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))

def Ydat (n f : ℕ) (rd g b : ℝ) : ℝ := (n : ℝ) * f * rd * g * b

def epsN (c : ℝ) (n f : ℕ) : ℝ := c / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)


end Formalism.HermitianLatticeCounting.S7
end
end

-- bundled from Formalism.FlagUnipotentLattices.IdealCountLeWAsm
section
namespace Formalism.HermitianLatticeCounting.Final.S6

theorem dualIndex : Formalism.HermitianLatticeCounting.S6.DualIndex := Formalism.HermitianLatticeCounting.P.dual_lattice_index

end Formalism.HermitianLatticeCounting.Final.S6
end

-- bundled from Formalism.FlagUnipotentLattices.SignaturePreservingEntryNorms
section
namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem torsionIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.HermitianLatticeCounting.P.card_range_nsmul_mul_card_le
theorem perpCompl : Formalism.HermitianLatticeCounting.LocalIntegralStructure.PerpCompl := Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
theorem cofactorVec : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CofactorVec := Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
theorem localCongr : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := Formalism.HermitianLatticeCounting.P.local_congruence_condition
theorem thmB : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := Formalism.HermitianLatticeCounting.P.theorem_B_statement

theorem gramDetGen : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDetGen := Formalism.HermitianLatticeCounting.P.gram_determinant_general
theorem gramNondeg : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramNondeg := Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
theorem arithmetic_square_bound_fourth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductInequalitySq := Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
theorem arithmetic_square_bound_fifth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductPlacesInequalitySq := Formalism.HermitianLatticeCounting.P.L5_arithmetic_square

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
end

