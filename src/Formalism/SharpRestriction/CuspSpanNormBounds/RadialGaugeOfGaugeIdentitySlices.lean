module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
public import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
public import Formalism.HermitianCurvature.StatementWd
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateTheorem
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.SharpRestriction.ParConsts
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.WRWeyl
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleGD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0005
public import Formalism.FormalDegreeBessel.FinalIO
public import Formalism.FormalDegreeBessel.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationScalesHeisenbergMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0028
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0021
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import Formalism.HermitianCurvature.StatementB
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
public import Formalism.HermitianCurvature.StatementTC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionWithDensities

@[expose] public section

section PartSl1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Head

variable (k j r' : ℕ)

variable {k j r'}

variable (z z' : Fin (2 * (j + r') + k + 1) → ℂ) (h : Matrix (Fin j) (Fin j) ℂ)
  (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Head

end Formalism.MainNotions.BridgeLemma₅

end PartSl1

section PartSl2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartSl2

section PartSl3

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Formalism.MainNotions.S.GramWordSpace Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartSl3

section PartT22

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Homog

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Homog

section Classes

end Classes

end Formalism.MainNotions.BridgeLemma₅

end PartT22

section PartT22b

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartT22b

section PartBlk

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section GlobalTheory

variable {k j r' : ℕ}

variable (o o' : Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ)
  (g g' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end GlobalTheory

end Formalism.MainNotions.BridgeLemma₅

end PartBlk

section PartLv

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

section Lv

variable {k j r' : ℕ}

end Lv

end Formalism.MainNotions.BridgeLemma₅

end PartLv

section PartHd

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Hd

variable {k r' : ℕ}

variable (c : ℂ) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)

end Hd

end Formalism.MainNotions.BridgeLemma₅

end PartHd

section PartBc

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

variable {k r' : ℕ}

end Formalism.MainNotions.BridgeLemma₅

end PartBc

section PartSlI

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Cast

variable {k j r' R : ℕ}

end Cast

section Cast1

variable {k r' R : ℕ}

end Cast1

end Formalism.MainNotions.BridgeLemma₅

end PartSlI

section PartSlJ

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartSlJ

section PartRp

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartRp

section PartWdAll

noncomputable section PartWd1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdAbstract

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end WdAbstract

end Formalism.MainNotions.BridgeLemma₅

end PartWd1

noncomputable section PartWd2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section WdZero

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}

end WdZero

end Formalism.MainNotions.BridgeLemma₅

end PartWd2

noncomputable section PartWd3

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

section WdScalars

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end WdScalars

section WdKap

open Formalism.FourierDecayAlt.Wd

variable {S : Type}

end WdKap

end Formalism.MainNotions.BridgeLemma₅

end PartWd3

noncomputable section PartWd4

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators

end Formalism.MainNotions.BridgeLemma₅

end PartWd4

noncomputable section PartWd6

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartWd6

noncomputable section PartWd8

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.REAL Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section WdHom

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}

end WdHom

end Formalism.MainNotions.BridgeLemma₅

end PartWd8

noncomputable section PartWd7

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartWd7

noncomputable section PartWd5

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryLevelOperators

end Formalism.MainNotions.BridgeLemma₅

end PartWd5

end PartWdAll

section PartLc

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.UnitaryLevelOperators Matrix

end Formalism.MainNotions.BridgeLemma₅

end PartLc

section PartFrAll

section PartFr1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)

variable {C}

end Abstract

end Formalism.MainNotions.BridgeLemma₅

end PartFr1

section PartFr2

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.BridgeLemma₅

end PartFr2

section PartFr3

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.I

section Ring

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

end Ring

end Formalism.MainNotions.BridgeLemma₅

end PartFr3

section PartFr5

namespace Formalism.MainNotions.BridgeLemma₅

open Polynomial Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

section Rat

variable {V : Type} [Ring V] [Algebra ℂ V]

end Rat

section Ee

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B : Base E} {r : ℕ} (C : Ctx B r)
  (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)

variable {C SS}

end Ee

end Formalism.MainNotions.BridgeLemma₅

end PartFr5

section PartFr7

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end PartFr7

section PartFr8

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions

end Formalism.MainNotions.BridgeLemma₅

end PartFr8

section PartFr9

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR Formalism.MainNotions.S.UnitaryLevelOperators

end Formalism.MainNotions.BridgeLemma₅

end PartFr9

end PartFrAll

section PartLb1

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb1

section PartLb2

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb2

section PartLb3

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.MainNotions.BridgeLemma₅

end PartLb3

section PartLb4

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lb_haarG : Formalism.FourierDecayAlt.B2.HaarGExists :=
  (Formalism.FourierDecayAlt.P.group_measure_from_diagonal Formalism.REAL.uJEmb Formalism.REAL.unimodular Formalism.REAL.ballFinite Formalism.REAL.volGrowth
    Formalism.QuantumDeterminants.hpkFacts Formalism.QuantumDeterminants.uHConj Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar Formalism.FourierDecayAlt.P.unitary_group_closed).1

def lbHaarUp : Prop :=
  (∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHaarOn (UWset k r z) μ → Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) ∧
  ∀ (k r : ℕ) (μ : Measure (Mt k r)), Formalism.MainNotions.S.IsHaarOn (Nset k r) μ → Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μ

def lbRepOfHC : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), inWb k r z → 0 < Tz k r z →
    Formalism.MainNotions.S.IsHCTypeW k r z u π →
      IsCRepOn (UWset k r z) π ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ ContinuousOn π (UWset k r z)

end Formalism.MainNotions.BridgeLemma₅

end PartLb4

section PartLb5

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb5

section PartLb6

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb6

section PartLb7

open MeasureTheory

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.BridgeLemma₅

end PartLb7

section PartTaAll

section PartTa1

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

section Sets

variable (D : D7)

end Sets

section Axioms

variable {D : D7} {L : LatticeDataWithDual D} {Kd : KernelData D} (Lv : ℕ → AddSubgroup D.host.E)

end Axioms

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa1

section PartTa2

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

section Lattices

variable (D : D7)

variable {D}

end Lattices

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa2

section PartTa3

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa3

section PartTa3b

open NumberField Finset Filter Topology

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa3b

section PartTa4

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.FourierDecayAlt.TA Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

def ThmAHyp (D : D7) (C : ℝ) (Kst : ℕ) (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  4 ≤ Kst ∧ 1 ≤ D.host.v ∧ PsiAx D δ ∧ LatAx D δ L ∧ FrameAx D δ L B ∧ ArithAxF D L Kd ∧
    (∀ v, LocMatch D T T' (x v) (B v) ∧ IsKFinCoefH (B v).σ (f v) ∧
      IsSection D.R.k D.R.rS (B v).z (B v).z' (μsec v)) ∧
    (∀ v, InterlaceS (k_le_nS D) (x v).u (x v).lam ∧ InterlaceS (k_le_nS D) (x v).u' (x v).lam) ∧
    (∀ v, (x v).u ≠ (x v).u') ∧
    (∀ v, GapAtLeast (epsSH D.R) (x v).lam
      (C * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Kst * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3))) ∧
    (∀ v, IsCutS (x v).u (x v).u' (Set.Icc (x v).a (x v).b)) ∧
    (∀ v, (x v).a ≤ (x v).a1 ∧ (x v).a1 ≤ (x v).b1 ∧ (x v).b1 ≤ (x v).b ∧
      Nlet D Kst ^ 3 / 2 ≤ (x v).b1 - (x v).a1) ∧
    (∀ v, C * ((D.R.k : ℝ) * Nlet D Kst * ((D.R.rS : ℝ) + 1) ^ 2 +
        Nlet D Kst ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + Nlet D Kst ^ 3) ≤ (x v).b - (x v).a)

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa4

section PartTa5

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa5

section PartTa6

open NumberField Finset Filter Topology
open scoped nonZeroDivisors ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalFrameAxioms Formalism.MainNotions.InterlacingSignCuts

attribute [local instance] Classical.propDecidable

section Ultra

variable (D : D7)

variable {D}

end Ultra

end Formalism.MainNotions.BridgeLemma₅

end

end PartTa6

end PartTaAll

section PartA0

namespace Formalism.MainNotions.BridgeLemma₅

open Formalism.MainNotions Formalism.MainNotions.S

end Formalism.MainNotions.BridgeLemma₅

end PartA0
