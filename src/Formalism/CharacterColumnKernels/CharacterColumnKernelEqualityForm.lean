module

public import Formalism.CharacterColumnKernels.StatementPsi
public import Formalism.CharacterColumnKernels.StatBlockRhoCount
public import Formalism.CharacterColumnKernels.StatementGC
public import Formalism.CharacterColumnKernels.Bundle0002

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.NG

def StatColKerChiC : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A),
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    Module.length O (kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0) ≤
      ∑ l, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D l))) +
      (Fintype.card ι : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO

def StatColKerChiOne : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (ℓ : ℕ) (e' : ι → ℕ),
    (∀ g (m : d → KO O), uElt r χ g • m = m) →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = δO • m) →
    (∀ m : d → KO O, (algebraMap T' A δ) • m = δO • m) →
    (∀ l, ∃ g ∈ D l, ∃ c : O, IsUnit c ∧
      ∀ m : d → KO O, k0 l g • m = ((ℓ : O) ^ e' l * δO * c) • m) →
    Module.length O (kerY (O := O) (M := d → KO O) r χ E e₁ δ D j Kc k0) ≤
      ∑ l, (Fintype.card d : ℕ∞) * (Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (e' l : ℕ∞) +
          2 * IsDiscreteValuationRing.addVal O δO) +
      (Fintype.card ι : ℕ∞) * (Fintype.card d : ℕ∞) * IsDiscreteValuationRing.addVal O δO

def StatBlockChiCFull : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    [Module T' (d → KO O)] [IsScalarTower T' A (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ) (sE : Finset G) (tE : G → T'),
    Fintype.card d = 1 →
    E = ∑ g ∈ sE, tE g • r g → E * E = δ • E →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = 0) →
    (∀ l g, ∃ a : A, k0 l g = a * E) →
    (∀ m : d → KO O, δ • m = δO • m) →
    (∀ m : d → KO O, (∑ g ∈ sE, tE g * ((χ g : T'ˣ) : T')) • m = δO • m) →
    let ρM := uRep O (M := d → KO O) r χ
    let Ψ := colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (Sha H0 : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ cols, Module.length O (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D w))) ≤ H0) →
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ Sha →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (d → KO O)) ≤
      Sha + eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        (cols.card : ℕ∞) * H0 + ∑ w ∈ qs, vζ w

def StatBlockChiOneFull : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G] (d : Type) [Fintype d]
    [Module A (d → KO O)] [SMulCommClass A O (d → KO O)]
    [Module T' (d → KO O)] [IsScalarTower T' A (d → KO O)]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (δO : O) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (ι' : Type*) [DecidableEq ι'] (colIdx : ι → ι'), Function.Injective colIdx →
    ∀ (D : ι' → Subgroup G) (j e' : ι' → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
      (k0 : ι → G → A) (ℓ cB : ℕ),
    Fintype.card d = 1 →
    (∀ g (m : d → KO O), uElt r χ g • m = m) →
    (∀ m : d → KO O, e₁ • m = 0) → (∀ m : d → KO O, E • m = δO • m) →
    (∀ m : d → KO O, δ • m = δO • m) →
    (∀ l, ∃ g ∈ D (colIdx l), ∃ c : O, IsUnit c ∧
      ∀ m : d → KO O, k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * c) • m) →
    let ρM := uRep O (M := d → KO O) r χ
    let Ψ := colPsi (O := O) (M := d → KO O) r χ E e₁ δ (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0
    ∀ (lrows qs : Finset ι') (F : ∀ w, Submodule O (H1z (resRep ρM (D w)))) (deg : ι' → ℕ)
      (vζ : ι' → ℕ∞) (Q : Submodule O (H1z ρM)) (vhE : ℕ∞),
    let cols : Finset ι' := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    (∀ w ∈ lrows, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ vζ w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B) →
    (∀ w ∈ cols, ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w) →
    (∀ h, Submodule.mkQ _ (Ψ h) ∈ Q) →
    Module.length O ↥(Q ⊓ ⨅ w ∈ lrows ∪ qs ∪ cols, (F w).comap (resH1 ρM (D w))) ≤ vhE →
    Module.length O (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
        (d → KO O)) ≤
      vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) +
        eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
        ∑ w ∈ qs, vζ w

abbrev blockRestrictedRepresentationType {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α) : Type _ :=
  LatQ O {a // bl a = k} (ρk k).toRingHom

end Formalism.NG
