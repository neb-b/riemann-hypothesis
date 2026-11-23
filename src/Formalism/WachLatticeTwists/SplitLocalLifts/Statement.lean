module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.StatementTop

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

def LiftO {O : Type*} [CommRing O] (ℓ : ℕ) {H₁ H₂ : Type*} [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ((ℓ : O) ^ e) • κ ∈ Hf₁.map g

section FinalTheorems
variable (ℓ : ℕ) [Fact ℓ.Prime] {H₁ H₂ : Type} [AddCommGroup H₁] [Module ℤ_[ℓ] H₁]
    [AddCommGroup H₂] [Module ℤ_[ℓ] H₂] (Hf₁ : Submodule ℤ_[ℓ] H₁) (Hf₂ : Submodule ℤ_[ℓ] H₂)
    (g : H₁ →ₗ[ℤ_[ℓ]] H₂) (e : ℕ)

end FinalTheorems

end Formalism.RepresentationBoundsCohomology.JL
