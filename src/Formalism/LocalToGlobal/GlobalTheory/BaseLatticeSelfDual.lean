module

public import Formalism.LocalToGlobal.GlobalTheory.ExistsUnitaryOneDetEq
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.MajDual

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

structure Coord (hc : CMData F E) (S : HSpace E) (n : Type) [Fintype n] where
  κ : S.V ≃ₗ[E] (n → E)
  J : Matrix n n E
  form : ∀ x y, S.hT x y = hform (hc.sig : E →+* E) J (κ x) (κ y)

variable {hc : CMData F E} {S : HSpace E}

def Coord.lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) (n → E) :=
  L.map ((K.κ : S.V →ₗ[E] (n → E)).restrictScalars (𝓞 E))

theorem Coord.mem_lat (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) (y : n → E) : y ∈ K.lat L ↔ K.κ.symm y ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show K.κ.symm (K.κ x) ∈ L
    rwa [LinearEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, K.κ.apply_symm_apply y⟩

theorem Coord.lat_dual (K : Coord hc S n) (L : Submodule (𝓞 E) S.V) :
    K.lat (Formalism.HermitianLatticesTheory.dual S.hT L) = dl hc.sig K.J (K.lat L) := by
  ext y
  rw [K.mem_lat, Formalism.HermitianLatticesTheory.dualBasic_mem_dual, mem_dl]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩
    have h1 := h x hx
    rw [K.form, LinearEquiv.apply_symm_apply] at h1
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
    exact ⟨r, hr⟩
  · intro h x hx
    have h1 := h (K.κ x) ⟨x, hx, rfl⟩
    rw [K.form, LinearEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := h1
    exact Submodule.mem_one.2 ⟨r, hr⟩

theorem Coord.isLat_lat (K : Coord hc S n) {L : Submodule (𝓞 E) S.V} (hL : Submodule.IsFullLattice E L) :
    IsLat (K.lat L) := by
  refine ⟨Module.Finite.iff_fg.2 (hL.fg.map _), ?_⟩
  rw [eq_top_iff]
  intro y _
  have h1 : K.κ.symm y ∈ Submodule.span E (L : Set S.V) := by rw [hL.span_eq_top]; trivial
  have h2 : K.κ (K.κ.symm y) ∈ (Submodule.span E (L : Set S.V)).map (K.κ : S.V →ₗ[E] (n → E)) := ⟨_, h1, rfl⟩
  rw [LinearEquiv.apply_symm_apply, Submodule.map_span] at h2
  exact h2

theorem star_int (r : 𝓞 E) : star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) :=
  ⟨⟨_, Formalism.HermitianLatticesTheory.majDual_star_int r⟩, rfl⟩

end Formalism.L2.GlobalTheoryTheory.Comp

end
