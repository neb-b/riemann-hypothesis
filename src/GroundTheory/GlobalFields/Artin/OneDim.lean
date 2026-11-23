module

public import Mathlib
public import GroundTheory.GlobalFields.GlobalReciprocity.General
public import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
public import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
public import GroundTheory.GlobalFields.ClassFieldConsequences.ConductorLocal
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
public import GroundTheory.GlobalFields.Artin.InflationTower

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IntermediateField WithZero

noncomputable section

section Circle

variable {G : Type*} [Group G] [Finite G]

end Circle

section CharField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

abbrev charField : IntermediateField K L :=
  fixedField χ.ker

end CharField

section Hecke

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

end Hecke

section Places

theorem IsArithFrobAt.eq_of_inertia_eq_bot {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S}
    (hI : Q.inertia G = ⊥) {σ σ' : G} (h : IsArithFrobAt R σ Q) (h' : IsArithFrobAt R σ' Q) :
    σ = σ' := by
  have := h.mul_inv_mem_inertia h'
  rwa [hI, Subgroup.mem_bot, mul_inv_eq_one] at this

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]


end Places

end

end GroundTheory.Global
