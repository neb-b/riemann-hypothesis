module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SubspaceCounting.Statement
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

def AllButLE {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (π : R)
    (M P : Submodule R X) (g E : ℕ) : Prop :=
  ∃ C : Finset X, (↑C : Set X) ⊆ M ∧ C.card ≤ g ∧
    ∀ x ∈ M, π ^ E • x ∈ P ⊔ Submodule.span R (↑C : Set X)

inductive Slot
  | base
  | ball
  | dual

def vertexLabel {V : ℕ} (B : Finset (Fin V)) : Fin V → Slot :=
  fun v => if v ∈ B then Slot.dual else Slot.base

def monoOp {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (e : Fin V → Bool) :
    Module.End R X :=
  ((List.finRange V).map fun v => if e v then y v ^ m else (π ^ S v) • (1 : Module.End R X)).prod

def prodIdealMap {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {V : ℕ} (π : R)
    (y : Fin V → Module.End R X) (m : ℕ) (S : Fin V → ℕ) (M : Submodule R X) :
    Submodule R X :=
  ⨆ e : Fin V → Bool, M.map (monoOp π y m S e)

def WalkSharp : Prop :=
  ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (V : ℕ) (π : R)
    (L : (Fin V → Slot) → Submodule R X) (y : Fin V → Module.End R X)
    (m β c₀ S : ℕ) (a b c Sv : Fin V → ℕ) (g : Finset (Fin V) → ℕ)
    (G : Finset (Fin V) → Finset X),
    1 ≤ m →
    (∀ v w, Commute (y v) (y w)) →
    (∀ σ v, L (Function.update σ v Slot.base) ≤ L (Function.update σ v Slot.ball)) →
    (∀ σ v, L (Function.update σ v Slot.dual) ≤ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ a v • x ∈ L (Function.update σ v Slot.base)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.base),
      π ^ b v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      π ^ c v • x ∈ L (Function.update σ v Slot.dual)) →
    (∀ σ v, ∀ x ∈ L (Function.update σ v Slot.ball),
      y v x ∈ L (Function.update σ v Slot.dual)) →
    (∀ B : Finset (Fin V), B.card = β + 1 →
      (↑(G B) : Set X) ⊆ L (vertexLabel B) ∧ (G B).card ≤ g B ∧
      ∀ x ∈ L (vertexLabel B), π ^ c₀ • x ∈
        (⨆ v ∈ B, (L (Function.update (vertexLabel B) v Slot.ball)).map (y v)) ⊔
          Submodule.span R (↑(G B) : Set X)) →
    (∀ v, Sv v ≤ S) →
    AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base))
        (∑ B ∈ (Finset.univ : Finset (Fin V)).powersetCard (β + 1), m ^ (β + 1) * g B)
        (∑ v, (a v + b v + (m - 1) * c v + m * c₀) + β * S) ∧
      AllButLE π (L fun _ => Slot.base) (prodIdealMap π y m Sv (L fun _ => Slot.base)) 0
        (∑ v, Sv v)

end Formalism.G0
end
end

-- bundled from Formalism.SubspaceCounting.StatementB
section
noncomputable section

open scoped BigOperators

namespace Formalism.G0

def window (n i L : ℕ) : Finset ℕ :=
  (Finset.range L).image fun j => (i + j) % n

def CondA (n : ℕ) (T : Finset ℕ) (L₂ K : ℕ) : Prop :=
  ∀ i < n, (T ∩ window n i L₂).card ≤ K

def gaussBinom (q : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1)

def countAbove {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // A ≤ U ∧ Module.finrank F U = j}

def countBelow {F W : Type} [Field F] [AddCommGroup W] [Module F W] [Finite W]
    (A : Submodule F W) (j : ℕ) : ℕ :=
  Nat.card {U : Submodule F W // U ≤ A ∧ Module.finrank F U = j}

def SubspaceCount : Prop :=
  ∀ {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W] (k : ℕ),
    countBelow (⊤ : Submodule F W) k = gaussBinom (Fintype.card F) (Module.finrank F W) k

def TypeIIUp : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (countAbove (LinearMap.range f) j : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ (l * (N + l - j)) * gaussBinom (Fintype.card F) g l *
          Nat.card {U : Submodule F P // U ≤ LinearMap.ker f ∧
            Module.finrank F U + (j - l) = N}

def TypeIIDown : Prop :=
  ∀ {F P Q : Type} [Field F] [Fintype F] [AddCommGroup P] [Module F P] [Finite P]
    [AddCommGroup Q] [Module F Q] [Finite Q] (f : P →ₗ[F] Q) (N g j : ℕ),
    Module.finrank F P = N → Module.finrank F Q = N + g →
    (Nat.card {U : Submodule F Q // LinearMap.range f ≤ U ∧ Module.finrank F U + j = N + g} : ℤ) =
      ∑ l ∈ Finset.range (j + 1),
        (Fintype.card F : ℤ) ^ ((j - l) * (g - l)) * gaussBinom (Fintype.card F) g l *
          countBelow (LinearMap.ker f) (j - l)

end Formalism.G0
end
end

