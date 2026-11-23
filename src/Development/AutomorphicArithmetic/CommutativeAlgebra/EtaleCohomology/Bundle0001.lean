module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
section
noncomputable section
open IsLocalRing

namespace UpperTheory.Et

structure TC (A D : Type) [CommRing A] [CommRing D] [Algebra A D] where
  B : Subalgebra A D
  C : Subalgebra A D
  t : D
  s : D
  ts : t * s = 1
  tB : t ∈ B
  sC : s ∈ C
  locB : ∀ x, ∃ k : ℕ, t ^ k * x ∈ B
  locC : ∀ x, ∃ k : ℕ, s ^ k * x ∈ C

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

def TC.Int (T : TC A D) : Prop :=
  (∀ x ∈ T.B, IsIntegral (Algebra.adjoin A {T.t}) x) ∧ ∀ x ∈ T.C, IsIntegral (Algebra.adjoin A {T.s}) x

def TC.Fin (T : TC A D) : Prop :=
  ∃ X : Finset D, (∀ x ∈ X, x ∈ T.B) ∧ ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x}

def TC.S (T : TC A D) (j : ℕ) : Submodule A D :=
  Subalgebra.toSubmodule T.B ⊓ (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j))

def TC.Coord (T : TC A D) : Prop :=
  ∃ (ι : Type) (β : Module.Basis ι A D) (U : Set ι) (V : ℕ → Set ι), Subalgebra.toSubmodule T.B = Submodule.span A (β '' U) ∧
    ∀ j, (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j)) = Submodule.span A (β '' V j) ∧ (U ∩ V j).Finite

def mm [IsLocalRing A] (S : Subalgebra A D) : Submodule A D := maximalIdeal A • Subalgebra.toSubmodule S

def Roots (S : Subalgebra A D) : Prop := ∀ p : Polynomial S, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0

def GoodRoot (q : ℕ) {S : Type} [CommRing S] (ζ : S) : Prop :=
  ζ ^ q = 1 ∧ (∀ a b : ZMod q, a ≠ b → IsUnit (ζ ^ a.val - ζ ^ b.val)) ∧
    ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x : S'), x ^ q - 1 = ∏ a ∈ Finset.range q, (x - φ ζ ^ a)

end UpperTheory.Et

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.LocallyExactCech
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Et

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

variable {R : Type} [CommRing R]

abbrev sec (M : PMod R) (U : Scheme.{0}) : Type 1 := M.obj (op U)

abbrev rs (M : PMod R) {V U : Scheme.{0}} (g : V ⟶ U) (x : sec M U) : sec M V := (M.map g.op).hom x

abbrev ap {M N : PMod R} (α : M ⟶ N) {U : Scheme.{0}} (x : sec M U) : sec N U := (α.app (op U)).hom x

def LocT (τ : GrothendieckTopology Scheme.{0}) (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ τ U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

def Inv (q : ℕ) (U : Scheme.{0}) : Prop := IsUnit (q : Γ(U, ⊤))

def Gen (τ : GrothendieckTopology Scheme.{0}) (q : ℕ) (M : PMod R) {U : Scheme.{0}} (g : sec M U) : Prop :=
  q • g = 0 ∧ (∀ (V : Scheme.{0}) (k : V ⟶ U) (c : ℕ), Nonempty V → c • rs M k g = 0 → q ∣ c) ∧
  ∀ (V : Scheme.{0}) (k : V ⟶ U) (y : sec M V), LocT τ V fun _ h => ∃ c : ℕ, rs M h y = c • rs M (h ≫ k) g

section Cech
variable {Y X : Scheme.{0}} (f : Y ⟶ X)




variable {f}

variable (f)


end Cech

end UpperTheory.Et

end
end

