module

public import Formalism.CharacterColumnKernels.StatementRho

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

def StatBlockRhoAbs : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type*) [Group G]
    (d : Type) [Fintype d] (ρM : Representation O G (d → KO O)) (H : Type*) [AddCommGroup H]
    [Module O H] (Ψ : H →ₗ[O] coZ1s ρM) (δ : O),
    (∀ h : H, ∀ v : d → KO O, (Ψ h : G → (d → KO O)) = coD0 ρM v → (δ * δ) • v = 0) →
    ∀ (ι : Type*) [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
      (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
      (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞) (ℓ : ℕ) (e' j : ι → ℕ) (h0 : ι → ℕ∞),
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δ
    let N : ℕ∞ := Fintype.card d
    (∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))), F w ≤ A ∧
      Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A) →
    (∀ w ∈ cols, ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ s →
    Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + (cols.card : ℕ∞) * N * vδ →
    Module.length O H ≤
      ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
        4 * N * ((cols.card : ℕ∞) + 1) * vδ

abbrev ColData (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ) (δ : O)
    (e' j : ℕ) (Xw : Type*) [AddCommGroup Xw] [Module O Xw] (d : Type) [Fintype d] : Type _ :=
  (Fin j → LinearMap.ker (DistribSMul.toLinearMap O (KO O) ((ℓ : O) ^ e' * δ))) × Xw ×
    LinearMap.ker (DistribSMul.toLinearMap O (d → KO O) δ)

end Formalism.NG
