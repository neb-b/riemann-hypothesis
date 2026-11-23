module

public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.WachLatticeTwists.RealClassMaps.Bundle0001
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG (KO H1z coZ1s resRep uRep IsEquivMap resH1 uElt)
open Formalism.RepresentationBoundsCohomology.BR (unrH1)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (lcH1)

section Defs
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def InRhoFixReal2 (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
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
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  Module.length O ↥((lcH1 (uRep O (M := M) r χ) ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

def InChiLoc (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (D : ℕ → Subgroup G) (qs : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
  (∀ w ∈ qs, F w = unrH1 (resRep (uRep O (M := M) r χ) (D w)) (I w) ∧ γ w ∈ I w ∧
    (r (γ w : G) - 1) * (r (γ w : G) - algebraMap T' A (ζ w)) = 0 ∧
    ((χ (γ w : G) : T'ˣ) : T') = ζ w ∧
    (∀ g ∈ I w, r (g : G) = r (γ w : G) ^ n w g ∧ χ (g : G) = χ (γ w : G) ^ n w g) ∧
    (∀ g ∈ I w, ∀ m : M, uElt r χ (g : G) • m = m) ∧
    (∀ m : M, r (γ w : G) • m = ζO w • m)) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ v, ∀ g ∈ IS v, ∃ a : A, a * ((r g - algebraMap T' A ((χ g : T'ˣ) : T')) * E) = 0 ∧
    ∀ m : M, a • m = 0 → m = 0)

def InChiFixReal (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ qs : Finset ℕ) (s : ℕ∞)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G)
    (I : ∀ w, Subgroup (D w)) (γ : ∀ w, D w) (ζ : ℕ → T') (ζO : ℕ → O) (n : ∀ w, D w → ℕ) : Prop :=
  InChiLoc M r χ E D qs F Io IS I γ ζ ζO n ∧
  Module.length O ↥((lcH1 (uRep O (M := M) r χ) ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs


end Formalism.RepresentationBoundsCohomology.FIN
