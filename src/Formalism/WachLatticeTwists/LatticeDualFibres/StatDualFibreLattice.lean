module

public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement

@[expose] public section

universe u

open Formalism.NG (KO)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

section Lat

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def IsLatticeIn {V : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] (L : Submodule O V) : Prop :=
  L.FG ∧ Submodule.span (FractionRing O) (L : Set V) = ⊤

def StableUnder {G V : Type u} [Group G] [AddCommGroup V] [Module O V] (ρ : Representation O G V)
    (L : Submodule O V) : Prop := ∀ g, ∀ x ∈ L, ρ g x ∈ L

def EquivToQuot {G VY VT : Type u} [Group G] [AddCommGroup VY] [Module O VY] [AddCommGroup VT]
    [Module O VT] (ρY : Representation O G VY) (ρT : Representation O G VT) (Y : Submodule O VY)
    (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Prop :=
  ∀ (g : G) (y : Y) (hy : ρY g y ∈ Y) (x : VT), φ y = Submodule.Quotient.mk x →
    φ ⟨ρY g y, hy⟩ = Submodule.Quotient.mk (ρT g x)

def fibre {VY VT : Type u} [AddCommGroup VY] [Module O VY] [AddCommGroup VT] [Module O VT]
    (Y : Submodule O VY) (T : Submodule O VT) (φ : Y →ₗ[O] VT ⧸ T) : Submodule O (VY × VT) where
  carrier := {p | ∃ h : p.1 ∈ Y, φ ⟨p.1, h⟩ = Submodule.Quotient.mk p.2}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Y.add_mem ha hb, ?_⟩
    have : (⟨(a + b).1, Y.add_mem ha hb⟩ : Y) = ⟨a.1, ha⟩ + ⟨b.1, hb⟩ := rfl
    rw [this, map_add (f := _), ha', hb']; rfl
  zero_mem' := ⟨Y.zero_mem, by
    have : (⟨(0 : VY × VT).1, Y.zero_mem⟩ : Y) = 0 := rfl
    rw [this, map_zero]; rfl⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨Y.smul_mem c ha, ?_⟩
    have : (⟨(c • a).1, Y.smul_mem c ha⟩ : Y) = c • ⟨a.1, ha⟩ := rfl
    rw [this, map_smul, ha']; rfl

def dualLat {V V' : Type u} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) : Submodule O V' where
  carrier := {f | ∀ x ∈ T, b x f ∈ (1 : Submodule O (FractionRing O))}
  add_mem' := by
    intro f g hf hg x hx
    rw [map_add (f := _)]; exact Submodule.add_mem _ (hf x hx) (hg x hx)
  zero_mem' := by
    intro x _
    rw [map_zero]; exact Submodule.zero_mem _
  smul_mem' := by
    intro c f hf x hx
    rw [map_smul]; exact Submodule.smul_mem _ c (hf x hx)

def PerfectRight {V V' : Type u} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ ψ : V →ₗ[FractionRing O] FractionRing O, ∃! f : V', ∀ x, b x f = ψ x

def EquivPair {G V V' : Type u} [Group G] [AddCommGroup V] [Module O V] [AddCommGroup V']
    [Module O V'] (ε : G →* Oˣ) (ρ : Representation O G V) (ρ' : Representation O G V')
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) : Prop :=
  ∀ g x f, b (ρ g x) (ρ' g f) = (ε g : O) • b x f

end Lat

end Formalism.RepresentationBoundsCohomology.LOC
