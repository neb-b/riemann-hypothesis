module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GaloisModules.CoeGalRootsOfUnityHomApply
public import GroundTheory.LocalFields.Bundle0005
public import GroundTheory.LocalFields.UnitsGalois
public import GroundTheory.TateCohomology.Bundle0005

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

noncomputable abbrev galIntegerUnitsZ : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ

noncomputable def integerUnitsToUnits : galIntegerUnitsZ K L ⟶ galUnitsZ K L :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (unitsIncl L)).toIntLinearMap, fun σ => by
    ext x
    rfl⟩

noncomputable def unitsValuation : galUnitsZ K L ⟶ Rep.trivial ℤ Gal(L/K) ℤ :=
  Rep.ofHom ⟨(unitsOrd (L := L)).toIntLinearMap, fun σ => by
    ext x
    change ord (↑(σ • x.toMul) : L) = ord (x.toMul : L)
    have hOrd : ord (σ (x.toMul : L)) = ord (x.toMul : L) := by
      rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
        valuation_algEquiv_apply K L σ (x.toMul : L)]
    rw [AlgEquiv.smul_units_def, Units.coe_map]
    exact hOrd⟩

@[simp]
theorem unitsValuation_hom_apply (x : Additive Lˣ) :
    (unitsValuation K L).hom x = ord ((x.toMul : Lˣ) : L) :=
  rfl

noncomputable def unitsValuationSES : ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (integerUnitsToUnits K L) (unitsValuation K L) (by
    ext x
    exact ord_unit (K := L) x.toMul)

theorem unitsValuationSES_shortExact : (unitsValuationSES K L).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine GroundTheory.GroupCoh.shortComplex_exact_of_forall fun x hx => ?_
    change Additive Lˣ at x
    change ord ((x.toMul : Lˣ) : L) = 0 at hx
    have hMem : x.toMul ∈ (unitsIncl L).range := by
      rwa [ord_eq_zero_iff_mem, unitFiltrationUnits, unitFiltration_zero,
        ← MonoidHom.range_eq_map] at hx
    obtain ⟨u, hu⟩ := hMem
    exact ⟨Additive.ofMul u, Additive.toMul.injective hu⟩
  · exact (Rep.mono_iff_injective (integerUnitsToUnits K L)).2 fun _ _ h =>
      Additive.toMul.injective (unitsIncl_injective (K := L) (congrArg Additive.toMul h))
  · have hSurj : Function.Surjective (unitsOrd (L := L)) := by
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
      intro n
      refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
      rw [map_zsmul]
      change n • ord (uniformizerUnit hϖ : L) = n
      rw [coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]
    exact (Rep.epi_iff_surjective (unitsValuation K L)).2 hSurj

end GroundTheory.ProfCoh
