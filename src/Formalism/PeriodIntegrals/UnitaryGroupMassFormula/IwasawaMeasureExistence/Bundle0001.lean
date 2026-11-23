module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
section
noncomputable section

namespace PI.IwaMeasEx.MF

open MeasureTheory Measure Set
open scoped ENNReal NNReal

section Idx

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem measure_eq_relIndex_mul (μ : Measure G) [IsMulLeftInvariant μ] {U W : Subgroup G} (hWU : W ≤ U)
    (hU : MeasurableSet (U : Set G)) (hW : MeasurableSet (W : Set G)) (hfin : W.relIndex U ≠ 0) :
    μ U = W.relIndex U * μ W := by
  classical
  have hcard : Nat.card (U ⧸ W.subgroupOf U) = W.relIndex U := rfl
  haveI : Finite (U ⧸ W.subgroupOf U) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hfin)
  letI : Fintype (U ⧸ W.subgroupOf U) := Fintype.ofFinite _
  choose r hr using fun q : U ⧸ W.subgroupOf U => QuotientGroup.mk_surjective q
  have hC : (U : Set G) = ⋃ q, (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk (⟨x, hx⟩ : U) : U ⧸ W.subgroupOf U), ?_⟩
      have h := QuotientGroup.eq.mp (hr (QuotientGroup.mk (⟨x, hx⟩ : U)))
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    · rintro ⟨q, hq⟩
      have e : x = ((r q : U) : G) * (((r q : U) : G)⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (r q).2 (hWU hq)
  have hdisj : Pairwise (Function.onFun Disjoint fun q => (fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) := by
    intro q q' hne
    change Disjoint ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
      ((fun x => ((r q' : U) : G)⁻¹ * x) ⁻¹' (W : Set G))
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    apply hne
    simp only [Set.mem_preimage, SetLike.mem_coe] at hx hx'
    rw [← hr q, ← hr q']
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have key : ((r q : U) : G)⁻¹ * ((r q' : U) : G) ∈ W := by
      have e : ((r q : U) : G)⁻¹ * ((r q' : U) : G) =
          (((r q : U) : G)⁻¹ * x) * (((r q' : U) : G)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact W.mul_mem hx (W.inv_mem hx')
    simpa using key
  have hmeas : ∀ q, MeasurableSet ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) :=
    fun q => hW.preimage (measurable_const_mul _)
  have hval : ∀ q, μ ((fun x => ((r q : U) : G)⁻¹ * x) ⁻¹' (W : Set G)) = μ W :=
    fun q => measure_preimage_mul μ _ _
  have hfc : (Fintype.card (U ⧸ W.subgroupOf U) : ℝ≥0∞) = (W.relIndex U : ℝ≥0∞) := by
    rw [← Nat.card_eq_fintype_card, hcard]
  rw [hC, measure_iUnion hdisj hmeas, tsum_fintype]
  simp only [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hfc]

end Idx

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

end Conj

section Scale

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

end Scale

end PI.IwaMeasEx.MF

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MulEquivHaarCharEqOfChart
section
noncomputable section

namespace PI.IwaMeasEx.MG

open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal

theorem smul_cancel {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨x⟩ := ‹Nonempty Y›
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
  have h0 : ρ K ≠ 0 := (measure_pos_of_mem_nhds ρ hKx).ne'
  have htop : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have hK' : (a : ℝ≥0∞) * ρ K = (b : ℝ≥0∞) * ρ K := by
    have e := congrArg (fun m : Measure Y => m K) h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact e
  have hab : (a : ℝ≥0∞) = b := (ENNReal.mul_left_inj h0 htop).mp hK'
  exact_mod_cast hab

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]

theorem mulEquivHaarChar_eq_of_chart (μ : Measure G) [IsHaarMeasure μ] [Regular μ] (ν : Measure Y)
    [IsAddHaarMeasure ν] [Regular ν] (χ : G → Y) (hχm : Measurable χ) (hχ : μ.map χ = ν) (φ : G ≃ₜ* G)
    (L : Y ≃ₜ+ Y) (h : ∀ x, χ (φ x) = L (χ x)) : mulEquivHaarChar φ = addEquivAddHaarChar L := by
  have hφ : Measurable φ := (map_continuous φ).measurable
  have hL : Measurable L := (map_continuous L).measurable
  have hcomp : χ ∘ φ = L ∘ χ := funext h
  have h1 : mulEquivHaarChar φ • map L ν = ν := by
    have e := congrArg (Measure.map χ) (mulEquivHaarChar_smul_map μ φ)
    rw [Measure.map_smul, Measure.map_map hχm hφ, hcomp, ← Measure.map_map hL hχm, hχ] at e
      <;> try exact hχm.aemeasurable
    exact e
  have h2 : addEquivAddHaarChar L • map L ν = ν := addEquivAddHaarChar_smul_map ν L
  have h3 : addEquivAddHaarChar L • ν = mulEquivHaarChar φ • ν := by
    calc addEquivAddHaarChar L • ν = addEquivAddHaarChar L • (mulEquivHaarChar φ • map L ν) := by rw [h1]
      _ = mulEquivHaarChar φ • (addEquivAddHaarChar L • map L ν) := by
        rw [smul_smul, smul_smul, mul_comm]
      _ = mulEquivHaarChar φ • ν := by rw [h2]
  exact (smul_cancel ν h3).symm

theorem shear_map {A B : Type*} [MeasurableSpace A] [AddGroup B] [MeasurableSpace B] [MeasurableAdd₂ B]
    [MeasurableAdd B] (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]
    (f : A → B) (hf : Measurable f) :
    (μ.prod ν).map (fun p : A × B => (p.1, p.2 + f p.1)) = μ.prod ν := by
  have hm : Measurable (fun p : A × B => (p.1, p.2 + f p.1)) :=
    measurable_fst.prodMk (measurable_snd.add (hf.comp measurable_fst))
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply hs, Measure.prod_apply (hm hs)]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : A × B => (p.1, p.2 + f p.1)) ⁻¹' s)
      = (fun b => b + f x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre, measure_preimage_add_right]

end PI.IwaMeasEx.MG

end
end

