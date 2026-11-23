module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SmithDeterminants.StatementDVR
section
open Finset

noncomputable section

namespace Formalism.A

structure SmithData {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (y : M →ₗ[R] M) (d : ℕ) where
  b : Module.Basis (Fin d) R M
  b' : Module.Basis (Fin d) R M
  a : Fin d → R
  hy : ∀ i, y (b i) = a i • b' i



def SmithExists : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (y : M →ₗ[R] M),
    Nonempty (SmithData y (Module.finrank R M))

end Formalism.A
end
end

-- bundled from Formalism.SmithDeterminants.StatementGram
section
open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.A

def mfact {σ : Type*} (g : σ →₀ ℕ) : ℕ := g.prod fun _ n => n.factorial

end Formalism.A
end
end

