module

public import Formalism.HermitianCurvature.Bundle0005
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0070
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFdGramCut
section
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm.Gram

section
variable {k r : ℕ}

end

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

end

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  simp [UWset, UH]

end

end PI.UnitaryGroupMassFormula.DLm.Gram
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundVDefs
section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def hW (k : ℕ) (j : Fin (k + 1)) : ℂ := if j.val = k then -1 else 1

def zW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => z (wI k r j)

def cmOf (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  S - (1 / 2 : ℂ) • (Bm * Matrix.diagonal (hW k) * Bmᴴ)

def unipotentBlockMatrix (k r : ℕ) (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) : B.Mat k r :=
  Matrix.of fun i j =>
    (if i = j then 1 else 0) +
    (if h : i.val < r ∧ r ≤ j.val ∧ j.val ≤ r + k then
      Bm ⟨i.val, h.1⟩ ⟨j.val - r, by omega⟩ else 0) +
    (if h : i.val < r ∧ r + k < j.val then
      cmOf k r Bm S ⟨i.val, h.1⟩ ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ else 0) +
    (if h : r ≤ i.val ∧ i.val ≤ r + k ∧ r + k < j.val then
      -(hW k ⟨i.val - r, by omega⟩) * star (Bm ⟨2 * r + k - j.val, by have := j.isLt; omega⟩ ⟨i.val - r, by omega⟩)
      else 0)

end PI.UnitaryGroupMassFormula.DLm
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PointwiseBoundHolds
section
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

section Frob

attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

end Frob

lemma gN_cont (k r : ℕ) : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

end PI.UnitaryGroupMassFormula.DLm
end
end

