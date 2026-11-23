module

public import Mathlib
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003

@[expose] public section

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ]

def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))

def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))

theorem zIdem_eq_centralIdem [Fintype Γ] (τ : FDRep ℂ Γ) : zIdem τ = centralIdem τ.ρ := rfl



end Gen

section GeneralLinearIntegers

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ



variable {K}



variable (K) in
def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ


variable (K) in
def patSet {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) : Set (GL ι K) :=
  {u | ∀ i j, (i = j → (u : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬ Φ i j → (u : Matrix ι ι K) i j = 0)}

def patChar {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (u : GL ι K) : ℂ :=
  ψ₀ (∑ i, ∑ j, E i j * (u : Matrix ι ι K) i j)


open Classical in
def wh {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (χ : GL ι K → ℂ) : ℂ :=
  by
    classical
    exact ((patSet (K := K) Φ).ncard : ℂ)⁻¹ * ∑ u, if u ∈ patSet (K := K) Φ then (patChar E ψ₀ u)⁻¹ * χ u else 0

def IsPat {ι : Type} (Φ : ι → ι → Prop) : Prop := (∀ i, ¬ Φ i i) ∧ ∀ i j k, Φ i j → Φ j k → Φ i k



variable (K) in
def cutE (N k : ℕ) (i j : Fin N) : K := if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k then 1 else 0




end GeneralLinearIntegers

namespace Lq

end Lq

end ReciprocityTheory.Ty.Fin
