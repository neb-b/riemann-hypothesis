module

public import Mathlib

@[expose] public section

open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.V.Lang.PsR

section generic
variable (n : ℕ) {G : Type*}

abbrev GenRing (G : Type*) := MvPolynomial (G × Fin n × Fin n) ℤ

def genMat (g : G) : Matrix (Fin n) (Fin n) (GenRing n G) := Matrix.of fun a b => X (g, a, b)

def genWord (w : FreeMonoid G) : Matrix (Fin n) (Fin n) (GenRing n G) := FreeMonoid.lift (genMat n) w
end generic

def detPoly {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {k : ℕ} (x : Fin k → Matrix ι ι R) :
    MvPolynomial (Fin k) R := (∑ j, (X j : MvPolynomial (Fin k) R) • (x j).map C).det

def Inv (n : ℕ) (G : Type*) : Subring (GenRing n G) :=
  Subring.closure {c | ∃ (k : ℕ) (w : Fin k → FreeMonoid G) (α : Fin k →₀ ℕ),
    c = AddMonoidAlgebra.coeff (detPoly fun j => genWord n (w j)) α}

def invCoef (n : ℕ) {G : Type*} {k : ℕ} (w : Fin k → FreeMonoid G) (α : Fin k →₀ ℕ) : Inv n G :=
  ⟨AddMonoidAlgebra.coeff (detPoly fun j => genWord n (w j)) α, Subring.subset_closure ⟨k, w, α, rfl⟩⟩

def evalW {G : Type*} [Monoid G] (w : FreeMonoid G) : G := FreeMonoid.lift id w

structure Det (n : ℕ) (A E B : Type*) [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B] where
  D : ∀ k : ℕ, (Fin k → E) → MvPolynomial (Fin k) B
  lin : ∀ (k k' : ℕ) (y : Fin k' → E) (c : Fin k → Fin k' → A), D k (fun j => ∑ l, c j l • y l) =
    bind₁ (fun l => ∑ j, C (algebraMap A B (c j l)) * X j) (D k' y)
  Θ : Inv n E →+* B
  inv : ∀ (k : ℕ) (w : Fin k → FreeMonoid E) (α : Fin k →₀ ℕ),
    AddMonoidAlgebra.coeff (D k fun j => evalW (w j)) α = Θ (invCoef n w α)

namespace Det
variable {n : ℕ} {A E B : Type*} [CommRing A] [Ring E] [Algebra A E] [CommRing B] [Algebra A B] (D : Det n A E B)

def val (x : E) : B := eval (fun _ => 1) (D.D 1 fun _ => x)

def lam (i : ℕ) (x : E) : B := (aeval ![1, Polynomial.X] (D.D 2 ![1, x]) : Polynomial B).coeff i

def tr (x : E) : B := D.lam 1 x

def Kills (x : E) : Prop := ∀ (k : ℕ) (w : Fin k → E), D.D (k + 1) (Fin.cons x w) = rename Fin.succ (D.D k w)

end Det

section sch
variable {n : ℕ} {A E : Type*} [CommRing A] [Ring E] [Algebra A E]

end sch

section sqz
variable {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N] [Module Aᵐᵒᵖ N] [IsCentralScalar A N]

end sqz

def Det.IsMap {n : ℕ} {G B A : Type} [Group G] [CommRing B] [CommRing A]
    (D : Det n B (MonoidAlgebra B G) B) (D' : Det n A (MonoidAlgebra A G) A) (φ : B →+* A) : Prop :=
  ∀ (k : ℕ) (y : Fin k → MonoidAlgebra B G),
    D'.D k (fun j => MonoidAlgebra.mapRingHom G φ (y j)) = MvPolynomial.map φ (D.D k y)

end Formalism.MainNotions.V.Lang.PsR
