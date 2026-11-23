module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.AutFinLit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compact

variable {K : Type} [Group K] [TopologicalSpace K]

end Compact

variable {D : D7}

def IsMaxCompactInf (V : HSp D) (K : Subgroup (GA D V)) : Prop :=
  (∀ k ∈ K, k ∈ GinfC V) ∧ IsCompact (K : Set (GA D V)) ∧
    ∀ K' : Subgroup (GA D V), (∀ k ∈ K', k ∈ GinfC V) → IsCompact (K' : Set (GA D V)) → K ≤ K' → K' = K

abbrev LieC (V : HSp D) : Type := ⨁ τ : D.what₂.Tau, ℂ ⊗[ℝ] LieAt V τ

abbrev Env (V : HSp D) : Type := UniversalEnvelopingAlgebra ℂ (LieC V)

end GlobalTheory.AutFinLit

namespace GlobalTheory.Published

open GlobalTheory.AutFinLit

end GlobalTheory.Published

end
