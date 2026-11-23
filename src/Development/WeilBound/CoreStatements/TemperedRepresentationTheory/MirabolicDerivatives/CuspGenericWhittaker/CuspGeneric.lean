module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import GroundTheory.AutomorphicForms.Bundle0007
public import GroundTheory.AutomorphicForms.WhittakerGroups
public import GroundTheory.AutomorphicForms.WhittakerCells
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import GroundTheory.AutomorphicForms.Bundle0010
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Matrix

namespace GlobalTheory.BZMir.Whit

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def WhitLeOne : Prop :=
  ∀ (n : ℕ) (ψ : AddChar k Circle) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → Continuous ψ → ψ ≠ 1 →
      Module.rank ℂ (TwJacquet π (unipB k (Fin n)) (whitChar ψ n)) ≤ 1

end GlobalTheory.BZMir.Whit

end
