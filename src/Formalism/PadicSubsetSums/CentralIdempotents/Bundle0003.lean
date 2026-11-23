module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
section
open Polynomial CategoryTheory
noncomputable section
namespace Formalism.IrreducibleCountingLemmas.TYPES

section Reps

variable {Γ : Type} [Group Γ]

def RepIso {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ Γ V) (ρ' : Representation ℂ Γ W) : Prop :=
  ∃ e : V ≃ₗ[ℂ] W, ∀ γ v, e (ρ γ v) = ρ' γ (e v)

end Reps

section Props

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {C : LabelConv K}

end Props

end Formalism.IrreducibleCountingLemmas.TYPES
end
end

-- bundled from Formalism.PadicSubsetSums.CentralIdempotents.SchurOrthogonalityCompact
section
noncomputable section

open Polynomial MeasureTheory
open scoped TensorProduct NumberField ComplexConjugate

namespace Formalism.IrreducibleCountingLemmas.Z

def DegreeOneSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ →
    P.inertiaDeg ℤ = 1 → P.ramificationIdx (𝓞 F) = 1 →
    ((P.under (𝓞 F)).primesOver (𝓞 E)).ncard = 2

def DirectedHomLine : Prop :=
  ∀ (k V W : Type) [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (ι : Type)
    [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (Vs : ι → Submodule k V)
    (H : Submodule k (V →ₗ[k] W)), Monotone Vs → (⨆ i, Vs i) = ⊤ →
    (∀ i, ∀ l ∈ H, ∀ l' ∈ H, l.domRestrict (Vs i) ≠ 0 →
      ∃ c : k, l'.domRestrict (Vs i) = c • l.domRestrict (Vs i)) →
    ∀ l ∈ H, ∀ l' ∈ H, l ≠ 0 → ∃ c : k, l' = c • l

def UnipotentTwistCharpoly : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A U : Module.End K V), Commute A U → IsNilpotent (U - 1) → (A * U).charpoly = A.charpoly

def GeneralizedEigenSplit : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (γ₀ γ : Module.End K V) (c : K) (t : ℕ) (s : K[X]), Commute γ₀ γ →
    γ₀.charpoly = s * (X - C c) ^ t → s.eval c ≠ 0 →
    IsCompl (LinearMap.ker (aeval γ₀ s)) (γ₀.maxGenEigenspace c) ∧
    Module.finrank K (γ₀.maxGenEigenspace c) = t ∧
    (∀ v ∈ LinearMap.ker (aeval γ₀ s),
      γ₀ v ∈ LinearMap.ker (aeval γ₀ s) ∧ γ v ∈ LinearMap.ker (aeval γ₀ s)) ∧
    ∀ v ∈ γ₀.maxGenEigenspace c, γ₀ v ∈ γ₀.maxGenEigenspace c ∧ γ v ∈ γ₀.maxGenEigenspace c

def BCCyclicVector : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (g : Module.End K V), g.charpoly.Separable → ∃ e : V, ∀ v : V, ∃ p : K[X], aeval g p e = v


end Formalism.IrreducibleCountingLemmas.Z
end
end

