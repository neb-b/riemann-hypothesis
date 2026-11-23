module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsBis
section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.ell :
    ∀ (O Λ Γ X : Type) [CommRing O] [CommRing Λ] [Algebra O Λ] [CommGroup Γ] [AddCommGroup X] [Module O X] (th₀ : Λ →ₐ[O] O) (d : Λ →ₗ[O] X) (χ : Γ →* Multiplicative X), (∀ a b, d (a * b) = th₀ a • d b + th₀ b • d a) → ∃ (th : MonoidAlgebra Λ Γ →ₐ[O] O) (ell : MonoidAlgebra Λ Γ →ₗ[O] X), (∀ g a, th (MonoidAlgebra.single g a) = th₀ a) ∧ (∀ a b, ell (a * b) = th a • ell b + th b • ell a) ∧ ∀ g a, ell (MonoidAlgebra.single g a) = d a + th₀ a • Multiplicative.toAdd (χ g) :=
  _root_.UpperTheory.Reformulated.B.Qh12.ell
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Lam0
section
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.lam0 :
    ∀ (O B M : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [AddCommGroup M] [Module B M] [Module.Finite B M] (x : B →ₐ[O] O), Module.annihilator B M ≤ RingHom.ker x → ∃ (lam : M →+ O) (m₀ : M), (∀ (a : B) m, lam (a • m) = x a * lam m) ∧ lam m₀ ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qf1.lam0
end

