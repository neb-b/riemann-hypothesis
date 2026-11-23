module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Round

variable {O : Type} [CommRing O] (bar : O → O)

def IsMultCell (φ : InvFun O) (M : ℕ) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ h : IsCell bar φ δ, LinearIndependent ℤ δ ∧ (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) ∧
    cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) = M


variable (O) in
structure FormFamily : Type 1 where

  X : Type
  [acg : AddCommGroup X]
  [mod : Module O X]

  m : ℕ

  δ : Fin m → LinearMap.BilinForm ℤ X

attribute [instance] FormFamily.acg FormFamily.mod

variable {bar}

def FormFamily.Carries (c : FormFamily O) {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ∃ (e : X ≃ₗ[O] c.X) (s : Fin m ≃ Fin c.m), ∀ i, δ i = pull e.toLinearMap (c.δ (s i))


variable (bar) in
def MultCellsAmong (q : ℕ) (φ : InvFun O) (M n : ℕ) : Prop :=
  ∃ R : Fin n → FormFamily O, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
    Module.finrank O X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell bar φ M δ → ∃ k, (R k).Carries δ

end Round

end GlobalTheory.PolFan
