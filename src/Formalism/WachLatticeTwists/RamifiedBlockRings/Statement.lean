module

public import Formalism.CharacterColumnKernels.Bundle0002
public import Formalism.TruncatedSeriesCounting.LemmaDetPoly

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

def blockPoly {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    Polynomial A :=
  Matrix.det ((Polynomial.X : Polynomial A) • e.map Polynomial.C - a.map Polynomial.C +
    (1 - e).map Polynomial.C)

def AbsIrr {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {G : Type*}
    (ρ : G → Matrix n n k) : Prop :=
  (∀ W : Submodule k (n → k), (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
  (∀ M : Matrix n n k, (∀ g, M * ρ g = ρ g * M) → ∃ c : k, M = c • (1 : Matrix n n k))

def BlockDiagonalIrreducibleAt {K : Type*} [Field K] {d : Type*} [Fintype d] [DecidableEq d] {G : Type*}
    (ρ : G → Matrix d d K) (m : ℕ) (c : d → Fin m) (P : Matrix d d K) : Prop :=
  IsUnit P ∧
  (∀ g a b, c a ≠ c b → (P * ρ g * P⁻¹) a b = 0) ∧
  (∀ i, AbsIrr (fun g => (P * ρ g * P⁻¹).toSquareBlock c i)) ∧
  (∀ i j, i ≠ j → ∀ M : Matrix {a // c a = i} {a // c a = j} K,
    (∀ g, M * (P * ρ g * P⁻¹).toSquareBlock c j = (P * ρ g * P⁻¹).toSquareBlock c i * M) → M = 0)

def PrimHyp (O : Type) [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ) : Prop :=
  IsLocalRing T ∧
  (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) ∧
  (∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T) ∧
  (∀ g a b, bl a ≠ bl b → r g π a b = 0) ∧
  (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) ∧
  (∀ g a, bl a ≠ 0 → r g π a a = (χ₁ g : O) * (((ε g)⁻¹ ^ ((bl a : ℕ) - 1) : Oˣ) : O))

def IdemHyp (O : Type) [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type}
    [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O)) (π : X) {t : ℕ}
    (bl : d → Fin (t + 1)) (eB e₁ : X → Matrix d d O) : Prop :=
  eB ∈ tSpan T r ∧ e₁ ∈ tSpan T r ∧ eB * eB = eB ∧ e₁ * e₁ = e₁ ∧ eB * e₁ = 0 ∧ e₁ * eB = 0 ∧
  (∀ x, ((eB x).map (algebraMap O (FractionRing O))).rank = t) ∧
  (∀ x, ((e₁ x).map (algebraMap O (FractionRing O))).rank = 1) ∧
  eB π = Matrix.diagonal (fun a => if bl a = 0 then 0 else 1) ∧
  (∀ a b, (bl a ≠ 0 ∨ bl b ≠ 0) → e₁ π a b = 0)

def StatResConst : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) (T : Subalgebra O (X → O)), IsLocalRing T →
    ∀ f ∈ T, ∀ x y : X, IsLocalRing.residue O (f x) = IsLocalRing.residue O (f y)

def StatBlockPolyT : Prop :=
  ∀ (O : Type) [CommRing O] (X : Type) (T : Subalgebra O (X → O)) (d : Type) [Fintype d]
    [DecidableEq d] (G : Type) [Group G] (r : G →* (X → Matrix d d O)),
    (∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T) →
    ∀ e ∈ tSpan T r, ∀ a ∈ tSpan T r, ∀ k : ℕ, (fun x => (blockPoly (e x) (a x)).coeff k) ∈ T

def StatBurnsideMat : Prop :=
  ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (G : Type) [Monoid G]
    (ρ : G →* Matrix n n k), AbsIrr ρ → Submodule.span k (Set.range ρ) = ⊤

end Formalism.RepresentationBoundsCohomology.ringDataObjects
