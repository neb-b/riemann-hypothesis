module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0001

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

section Defs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def leviChar {R : Type} [CommRing R] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (θ : α → Rˣ →* ℂˣ) : Levi R m →* ℂˣ :=
  ∏ a, (detChar (m a) (θ a)).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

omit [LinearOrder α] in
theorem leviChar_apply {R : Type} [CommRing R] (θ : α → Rˣ →* ℂˣ) (x : Levi R m) :
    leviChar m θ x = ∏ a, θ a (GeneralLinearGroup.det (x a)) := by
  simp [leviChar, MonoidHom.finsetProd_apply]

def typeChar (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : parahoric k e →* ℂˣ :=
  (leviChar m θ).comp (parahoricProj k e)

theorem typeChar_apply (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) (g : parahoric k e) :
    typeChar e θ g = ∏ a, θ a (GeneralLinearGroup.det (parahoricProj k e g a)) :=
  leviChar_apply θ _

def typeSp (π : Representation ℂ (GL n k) V) (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : Submodule ℂ V where
  carrier := {v | ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v}
  add_mem' := fun {a b} ha hb g => by rw [map_add (f := _), ha g, hb g, smul_add]
  zero_mem' := fun g => by simp
  smul_mem' := fun c v hv g => by rw [map_smul, hv g, smul_comm]

theorem mem_typeSp {π : Representation ℂ (GL n k) V} {e : (Σ a, m a) ≃ n} {θ : α → 𝓀[k]ˣ →* ℂˣ} {v : V} :
    v ∈ typeSp π e θ ↔ ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v := Iff.rfl

def HasTypeVec (π : Representation ℂ (GL n k) V) (e : (Σ a, m a) ≃ n) (θ : α → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ v : V, v ≠ 0 ∧ ∀ g : parahoric k e, π g v = (typeChar e θ g : ℂ) • v



abbrev blockOf {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) (i : Fin N) : Fin s := ((stdBlocks d hd).symm i).1

def HasTameSupp {N : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (ω : Fin N → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ μ : Fin N → kˣ →* ℂˣ, (∀ i, IsTameLift (μ i) (ω i)) ∧
    IsCuspSupport π (fun _ : Fin N => 1) (fun i => detRep (Fin 1) (μ i))

def IsTameSphProd {N s : ℕ} (π : Representation ℂ (GL (Fin N) k) V) (d : Fin s → ℕ) (hd : ∑ a, d a = N)
    (θ : Fin s → 𝓀[k]ˣ →* ℂˣ) : Prop :=
  ∃ η : Fin s → kˣ →* ℂˣ, (∀ a, IsSmoothChar (η a) ∧ IsTameLift (η a) (θ a)) ∧ UpperTheory.TNZ.IsTwSphProd π d hd η

end Defs

def SuppOfType : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ θ : Fin s → 𝓀[k]ˣ →* ℂˣ, HasTypeVec π (stdBlocks d hd) θ → HasTameSupp π fun i => θ (blockOf d hd i)

def TopB : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ θ : Fin s → 𝓀[k]ˣ →* ℂˣ, Function.Injective θ → HasTypeVec π (stdBlocks d hd) θ → IsTameSphProd π d hd θ

end UpperTheory.Gal.TypesAndIwahori
