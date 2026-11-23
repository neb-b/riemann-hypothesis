module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.Bundle0001
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight

@[expose] public section

noncomputable section

namespace SiegelEisensteinSeries.BRoad

open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem isCompact_intHat : IsCompact (intHat F E : Set (AE F E)) := by
  have hZ : (⊤ : Submodule ℤ (𝓞 E)).FG := Module.Finite.fg_top
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have : CompactSpace (GlobalTheory.ThK.Dbl.St.intF F) := isCompact_iff_compactSpace.1 GlobalTheory.ThK.Dbl.St.isCompact_intF
  let f : (Fin m → GlobalTheory.ThK.Dbl.St.intF F) →+ AE F E :=
    AddMonoidHom.mk' (fun (a : Fin m → GlobalTheory.ThK.Dbl.St.intF F) => ∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)) fun (a b : Fin m → GlobalTheory.ThK.Dbl.St.intF F) => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : ((a + b) j : AF F) = a j + b j := rfl
      rw [this, add_smul]
  have hf : Continuous f := by
    change Continuous fun a : Fin m → GlobalTheory.ThK.Dbl.St.intF F => ∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun a : Fin m → GlobalTheory.ThK.Dbl.St.intF F => (a j : AF F) :=
      Continuous.subtype_val (continuous_apply j)
    exact h1.fun_smul continuous_const
  have e : intHat F E = f.range := by
    refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨a, ha, ha', o, rfl⟩
      have ho : o ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ho
      refine ⟨fun j => c j • ⟨a, ha, ha'⟩, ?_⟩
      change ∑ j, (c j • a) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E) =
        a • inclR (F := F) (AF F) (((∑ j, c j • s j : 𝓞 E)) : E)
      have hc : (((∑ j, c j • s j : 𝓞 E)) : E) = ∑ j, c j • ((s j : 𝓞 E) : E) := by push_cast; rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hc, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    · rintro _ ⟨a, rfl⟩
      change (∑ j, (a j : AF F) • inclR (F := F) (AF F) ((s j : 𝓞 E) : E)) ∈ intHat F E
      exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨a j, (a j).2.1, (a j).2.2, s j, rfl⟩
  rw [e, AddMonoidHom.coe_range]
  exact isCompact_range hf

end SiegelEisensteinSeries.BRoad
