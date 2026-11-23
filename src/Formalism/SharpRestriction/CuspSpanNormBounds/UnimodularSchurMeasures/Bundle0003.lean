module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0002
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CovolumeIndependentOfFundamentalDomain
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def LocFinF (X : CData) : Prop := IsLocallyFiniteMeasure X.μf

theorem automorphic_L2_secondCountable (X : CData) [SecondCountableTopology X.I.Gf] : SecondCountableTopology X.L2 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  infer_instance

theorem rr_muA_locFin (X : CData) (h : LocFinF X) : IsLocallyFiniteMeasure (X.I.muA X.μf) := by
  have : IsLocallyFiniteMeasure X.μf := h
  unfold AutInst.muA; infer_instance

theorem rr_muA_openPos (X : CData) [X.μf.IsHaarMeasure] : (X.I.muA X.μf).IsOpenPosMeasure := by
  unfold AutInst.muA; infer_instance

end Formalism.MainNotions.LeviCoordinates

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.KernelDiagonalOfTriangleInequality
section
noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (decExp)

def DistTri : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), cartanDistance ε (g * k) ≤ cartanDistance ε g + cartanDistance ε k

end Formalism.MainNotions.LeviCoordinates

end
end

