module

public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

def radical (k : Type) [CommRing k] (r a : ℕ) : Set (GL (Fin r) k) :=
  {u | ∀ i j : Fin r, (u : Matrix (Fin r) (Fin r) k) i j ≠ (1 : Matrix (Fin r) (Fin r) k) i j → i.val < a ∧ a ≤ j.val}

def NoFixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) : Prop :=
  ∀ x : V, (∀ u ∈ S, τ u x = x) → x = 0

def HypH {P : Type} {k : P → Type} [∀ v, CommRing (k v)] {r : ℕ} {V : P → Type} [∀ v, AddCommGroup (V v)]
    [∀ v, Module ℂ (V v)] (τ : ∀ v, Representation ℂ (GL (Fin r) (k v)) (V v)) : Prop :=
  ∀ a : ℕ, 0 < a → a < r → ∃ v, NoFixed (τ v) (radical (k v) r a)

def IsSubrep {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ G V) (π : Representation ℂ G W) : Prop :=
  ∃ T : V →ₗ[ℂ] W, Function.Injective T ∧ ∀ t : G, T ∘ₗ τ t = π t ∘ₗ T

def FixedVectorBlocks : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (b : Fin r → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (blockTri (κ := k) b) W), IsCuspDatum b ρ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin r) k) V), IsSubrep τ (parInd b ρ) →
    ∀ a : ℕ, 0 < a → a < r → ¬ NoFixed τ (radical k r a) →
      ∃ J ⊆ Finset.univ.image b, a = ∑ c ∈ J, Fintype.card {i : Fin r // b i = c}


end GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors
