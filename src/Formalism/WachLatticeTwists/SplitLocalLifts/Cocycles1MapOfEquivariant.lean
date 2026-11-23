module

public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Bundle0001
public import Formalism.WachLatticeTwists.Statement
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Map
variable {O D M₁ M₂ : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
  [AddCommGroup M₂] [Module O M₂]

def cocycles1MapOfEquivariant (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (p : M₁ →ₗ[O] M₂)
    (hp : IsEquivMap ρ₁ ρ₂ p) : coZ1s ρ₁ →ₗ[O] coZ1s ρ₂ where
  toFun c := ⟨fun g => p ((c : D → M₁) g), fun g h => by
    show p ((c : D → M₁) (g * h)) = p ((c : D → M₁) g) + ρ₂ g (p ((c : D → M₁) h))
    rw [c.2 g h, map_add (f := _), hp]⟩
  map_add' a b := Subtype.ext (funext fun g => map_add p _ _)
  map_smul' c a := Subtype.ext (funext fun g => map_smul p _ _)

def mapH1 (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (p : M₁ →ₗ[O] M₂)
    (hp : IsEquivMap ρ₁ ρ₂ p) : H1z ρ₁ →ₗ[O] H1z ρ₂ :=
  Submodule.mapQ _ _ (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp) (by
    rintro x ⟨v, hv⟩
    refine ⟨p v, funext fun g => ?_⟩
    have h := congrFun hv g
    show ρ₂ g (p v) - p v = p ((x : D → M₁) g)
    rw [← hp, ← map_sub]
    exact congrArg p h)

end Map

section Ev
variable {O A T' G : Type*} [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
  {P : Type*} [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
  {L : Type*} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]

theorem ev_equiv (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L)
    (ev : P →ₗ[O] L) (hev : ∀ p, ev p = inc p • v₁) :
    IsEquivMap (resRep (uRep O (M := P) r χ) Dl) (resRep (uRep O (M := L) r χ) Dl) ev := by
  intro g p
  show ev (uElt r χ (g : G) • p) = uElt r χ (g : G) • ev p
  rw [hev, hev, map_smul, smul_eq_mul, mul_smul]

theorem ev_equiv_triv {N : Type*} [AddCommGroup N] [Module O N] (r : G →* A) (χ : G →* T'ˣ)
    (Dl : Subgroup G) (ev : P →ₗ[O] N) (hev : ∀ g p, ev (uElt r χ g • p) = ev p) :
    IsEquivMap (resRep (uRep O (M := P) r χ) Dl) (Representation.trivial O Dl N) ev := by
  intro g p
  show ev (uElt r χ (g : G) • p) = ev p
  exact hev g p

end Ev

def StatLiftCoc : Prop :=
  ∀ (O D M₁ M₂ : Type*) [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂]
    [Module O M₂] (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (p : M₁ →ₗ[O] M₂)
    (hp : IsEquivMap ρ₁ ρ₂ p), Function.Surjective p →
    ∀ (Hf₁ : Submodule O (H1z ρ₁)) (Hf₂ : Submodule O (H1z ρ₂)) (ℓ e : ℕ),
    LiftO ℓ Hf₁ Hf₂ (mapH1 ρ₁ ρ₂ p hp) e →
    ∀ κ : coZ1s ρ₂, (Submodule.mkQ _ κ : H1z ρ₂) ∈ Hf₂ →
      ∃ K : coZ1s ρ₁, (Submodule.mkQ _ K : H1z ρ₁) ∈ Hf₁ ∧
        ∀ g, p ((K : D → M₁) g) = ((ℓ : O) ^ e) • (κ : D → M₂) g

def StatColK : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type*) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A) (v₁ : L) (ev : P →ₗ[O] L)
    (hev : ∀ p, ev p = inc p • v₁), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (ℓ e' j : ℕ)
      (κ : Fin j → G → L) (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) → (∀ a, Submodule.mkQ _ (κz a) ∈ Hf₂) →
    LiftO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv r χ Dl inc v₁ ev hev)) e' →
    ∃ (Kc : Fin j → G → A) (Kz : Fin j → coZ1s (resRep (uRep O (M := P) r χ) Dl)),
      (∀ a (g : Dl), Kc a g = inc ((Kz a : Dl → P) g)) ∧ (∀ a, Submodule.mkQ _ (Kz a) ∈ Hf₁) ∧
      ∀ a, ∀ g ∈ Dl, Kc a g • v₁ = ((ℓ : O) ^ e') • κ a g

def StatColk : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type*) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (δO : O) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (ev : P →ₗ[O] ↥(Ideal.span {δO})),
    (∀ p, ∃ a : A, inc p = a * E) → (∀ p (m : M), inc p • m = ((ev p : ↥(Ideal.span {δO})) : O) • m) →
    ∀ (hev : ∀ g p, ev (uElt r χ g • p) = ev p), Function.Surjective ev →
    ∀ (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl)))
      (Hf₂ : Submodule O (H1z (Representation.trivial O Dl ↥(Ideal.span {δO})))) (ℓ e' : ℕ)
      (u : G → O) (uz : coZ1s (Representation.trivial O Dl ↥(Ideal.span {δO}))),
    (∀ g : Dl, (((uz : Dl → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u g) →
    Submodule.mkQ _ uz ∈ Hf₂ →
    LiftO ℓ Hf₁ Hf₂ (mapH1 _ _ ev (ev_equiv_triv r χ Dl ev hev)) e' →
    ∃ (k0 : G → A) (kz : coZ1s (resRep (uRep O (M := P) r χ) Dl)),
      (∀ g : Dl, k0 g = inc ((kz : Dl → P) g)) ∧ Submodule.mkQ _ kz ∈ Hf₁ ∧
      (∀ g, ∃ a : A, k0 g = a * E) ∧
      ∀ g ∈ Dl, ∀ m : M, k0 g • m = ((ℓ : O) ^ e' * δO * u g) • m

def StatColFun : Prop :=
  ∀ (O A T' G : Type*) [CommRing O] [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (P : Type*) [AddCommGroup P] [Module A P] [Module O P] [SMulCommClass A O P]
    (V : Type*) [AddCommGroup V] [Module A V]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (inc : P →ₗ[A] A)
    (Hf₁ : Submodule O (H1z (resRep (uRep O (M := P) r χ) Dl))) (Lf : Set (Dl → V)),
    (∀ (f : P →ₗ[A] V) (z : coZ1s (resRep (uRep O (M := P) r χ) Dl)), Submodule.mkQ _ z ∈ Hf₁ →
      (fun g : Dl => f ((z : Dl → P) g)) ∈ Lf) →
    ∀ (K : G → A) (Kz : coZ1s (resRep (uRep O (M := P) r χ) Dl)),
    (∀ g : Dl, K g = inc ((Kz : Dl → P) g)) → Submodule.mkQ _ Kz ∈ Hf₁ →
    ∀ s : V, (fun g : Dl => K g • s) ∈ Lf

end Formalism.RepresentationBoundsCohomology.JL
