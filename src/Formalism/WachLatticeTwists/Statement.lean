module

public import Formalism.CharacterColumnKernels.Statement

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology

def negCount (s : Multiset ℤ) : ℕ := Multiset.card (s.filter (fun u => u < 0))

def StatRowColength : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    (I : Submodule O M) (ℓ e : ℕ),
    (∀ m : M, ((ℓ : O) ^ e) • m ∈ I) →
    Module.length O (M ⧸ I) ≤
      (Module.finrank O M : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) +
        Module.length O (Submodule.torsion O M)

def SubmoduleLengthBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (d : Type*) [Fintype d] (N : Submodule O (d → Formalism.NG.KO O)) (ℓ c : ℕ),
    (∀ x ∈ N, ((ℓ : O) ^ c) • x = 0) →
    Module.length O N ≤
      (Fintype.card d : ℕ∞) * ((c : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}))

end Formalism.RepresentationBoundsCohomology
