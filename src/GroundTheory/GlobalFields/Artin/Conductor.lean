module

public import Mathlib
public import GroundTheory.GlobalFields.SemilocalAlgebras.Galois
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import GroundTheory.GlobalFields.TateThesis.ChebotarevAbelian
public import GroundTheory.GlobalFields.TateThesis.Bundle0005
public import GroundTheory.LocalFields.Bundle0013
public import GroundTheory.LocalFields.Bundle0015
public import GroundTheory.LocalFields.Bundle0018
public import GroundTheory.LocalFields.Bundle0001

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

section Transport

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra F L₁] [ValuativeExtension F L₁] [FiniteDimensional F L₁] [IsGalois F L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra F L₂] [ValuativeExtension F L₂] [FiniteDimensional F L₂] [IsGalois F L₂]

end Transport

section Local

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

theorem exists_smul_eq_of_liesOver (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] : ∃ σ : Gal(L/K), w' = σ • w := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w.asIdeal w'.asIdeal Gal(L/K)
  exact ⟨σ, HeightOneSpectrum.ext (by rw [SemiLocal.smul_asIdeal, hσ])⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

end Local

section Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]




end Ideal

end GroundTheory.Global
