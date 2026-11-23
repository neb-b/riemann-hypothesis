module

public import Mathlib
public import GroundTheory.GlobalFields.Artin.ConductorInflation
public import GroundTheory.GlobalFields.Artin.OneDim
public import GroundTheory.LocalFields.Bundle0018
public import GroundTheory.LocalFields.SeparableClosure

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

open IdeleGroup

section LocalConductor

variable {k M : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M] [IsGalois k M]

end LocalConductor

section Units

open ValuativeRel

variable {K : Type*} [Field K] [NumberField K]

theorem unitFiltrationUnits_eq_unitsLevel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n = unitsLevel v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact unitFiltrationUnits_zero_eq_unitsLevel_zero v
  ext x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, GroundTheory.Global.mem_unitsLevel_of_one_le hn, ← map_pow,
    (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ,
    ← WithZero.exp_nsmul]
  simp

end Units

section OneDim

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (χ : Gal(L/K) →* ℂˣ)

end OneDim

end GroundTheory.Global
