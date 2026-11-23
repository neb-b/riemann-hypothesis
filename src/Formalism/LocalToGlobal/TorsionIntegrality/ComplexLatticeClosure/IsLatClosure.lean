module

public import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (latI UniqInv CMConjSet)

def IsLatClosure : Prop :=
  ∀ a b : ℂ, ((starRingEnd ℂ) a * b).im ≠ 0 → IsLat (AddSubgroup.closure {a, b})

def IsLatSmul : Prop := ∀ (Λ : AddSubgroup ℂ) (c : ℂ), c ≠ 0 → IsLat Λ → IsLat (c • Λ)

def LatILat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ x : K, x ^ 2 = -(d : K) →
    Module.finrank ℚ K = 2 → ∀ (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ), 𝔞 ≠ ⊥ → δ ≠ 0 →
      IsLat (latI φ 𝔞 δ) ∧ HasCM d (latI φ 𝔞 δ)

end Formalism.L2.Th1.F2
