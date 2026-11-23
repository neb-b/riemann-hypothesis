module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

def StatPowSubOneO : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ (x : O) (y : Oˣ), x - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ n : ℕ, n ≠ 0 →
      IsDiscreteValuationRing.addVal O (x ^ n - 1) =
        IsDiscreteValuationRing.addVal O (ℓ : O) * ((s₀ + padicValNat ℓ n : ℕ) : ℕ∞)

def WachTwistTheoremDeltaClause : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ x y u₁ : Oˣ, (x : O) - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ t : ℕ,
    let δO : O := ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    IsDiscreteValuationRing.addVal O δO =
      eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    IsDiscreteValuationRing.addVal O δO ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

def WachTwistTheoremDeltaSum : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s₀ t : ℕ,
    ∑ i ∈ Finset.Ioo 0 (t + 1), (s₀ + padicValNat ℓ i) = t * s₀ + padicValNat ℓ t.factorial

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRhoTensor (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  ((∀ (a : A) v, iL (a • v) = a • iL v) ∧ (∀ (a : A) v, qV (a • v) = a • qV v) ∧
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v)) ∧
    Function.Injective iL ∧ Function.Surjective qV ∧ LinearMap.ker qV = LinearMap.range iL ∧
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range iL) ∧
    ∀ l, (∀ a (g : D (colIdx l)), (κz l a : D (colIdx l) → L) g = κ l a g) ∧
      (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
      (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
      (∀ z ∈ Ff l, ∃ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 ∧
        c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l))))) = 0) ∧
      (∀ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 →
        c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))) = 0 → b = 0)) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRho M r χ E (D w) ε ρ₁ inc π γ (Hc w) (F w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

def SelmerInjConditions : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    InRhoTensor M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ iL qV Ff κz HcG Hc F Io ε ρ₁ ρ₂ inc
      π γ lam cls pr Fs Im →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im

end Formalism.RepresentationBoundsCohomology.BR
