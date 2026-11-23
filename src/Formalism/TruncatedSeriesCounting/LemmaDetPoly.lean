module

public import Formalism.CharacterColumnKernels.StatementN

@[expose] public section

open Finset Classical Polynomial

noncomputable section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

universe u v w

open Formalism.NG

section Det

variable {O K X G : Type*} [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
  {n : Type} [Fintype n] [DecidableEq n]

def tSpan (T : Subalgebra O (X → O)) (r : G →* (X → Matrix n n K)) : Set (X → Matrix n n K) :=
  {F | ∃ (s : Finset G) (c : G → X → O), (∀ g, c g ∈ T) ∧
    F = ∑ g ∈ s, fun x => algebraMap O K (c g x) • r g x}

def FromT (T : Subalgebra O (X → O)) (f : X → K) : Prop :=
  ∃ t ∈ T, ∀ x, algebraMap O K (t x) = f x

end Det

def LemmaDetPoly : Prop :=
  ∀ (O K X G : Type*) [CommRing O] [CommRing K] [Algebra O K] [Monoid G]
    (n : Type) [Fintype n] [DecidableEq n] (T : Subalgebra O (X → O))
    (r : G →* (X → Matrix n n K)),
    (∀ (g : G) (k : ℕ), FromT T (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    ∀ (m : ℕ) (a : Fin m → X → Matrix n n K), (∀ i, a i ∈ tSpan T r) →
    ∀ s : Fin m →₀ ℕ, FromT T (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) K) • (a i x).map MvPolynomial.C))
      s)

def LemmaDetSub : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] (X' G : Type*) [Monoid G] (T' : Subalgebra O (X' → O))
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (r : G →* (X' → Matrix d d (FractionRing O))),
    (∀ (g : G) (k : ℕ), FromT T' (fun x => (Matrix.charpolyRev (r g x)).coeff k)) →
    (∀ a ∈ R', a ∈ tSpan T' r) →
    ∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det

def BridgeDet : Prop :=
  LemmaDetPoly.{u, u, v, w} → StatBlockDet.{u, v} → LemmaDetSub.{u, v, w}

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
