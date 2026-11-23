module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory Module ZLattice


open scoped Classical in
theorem CovolumeRelIndex.proof : CovolumeRelIndex.Statement := by
  intro E _ _ _ _ _ μ _ L₁ L₂ _ _ _ _ h
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := (Module.finBasis ℝ E).equivFunL.symm
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  have : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    simp only [ν]
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (⇑f ∘ ⇑f.symm) = id := by ext x; simp
    rw [this, Measure.map_id]
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • volume := ⟨_, Measure.isAddLeftInvariant_eq_smul ν volume⟩
  have scale : ∀ (L : Submodule ℤ (Fin (finrank ℝ E) → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L],
      covolume L ν = (c : ℝ) * covolume L volume := by
    intro L _ _
    rw [covolume_eq_measure_fundamentalDomain L ν
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) ν),
      covolume_eq_measure_fundamentalDomain L volume
        (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume)]
    conv_lhs => rw [hν]
    exact measureReal_nnreal_smul_apply c
  have hidx : ((ZLattice.comap ℝ L₁ f.toLinearMap).toAddSubgroup.relIndex
      (ZLattice.comap ℝ L₂ f.toLinearMap).toAddSubgroup : ℝ) =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) := by
    rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup, Nat.cast_inj,
      LinearEquiv.toAddMonoidHom_commutes, AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.comap_equiv_eq_map_symm',
      AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]
  have key := covolume_div_covolume_eq_relIndex (ZLattice.comap ℝ L₁ f.toLinearMap)
    (ZLattice.comap ℝ L₂ f.toLinearMap) (fun _ h' ↦ h h')
  have hne := covolume_ne_zero (ZLattice.comap ℝ L₂ f.toLinearMap) volume
  rw [← covolume_comap L₁ μ ν hf, ← covolume_comap L₂ μ ν hf, scale, scale, ← hidx, ← key]
  field_simp

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace


open scoped Classical in
theorem EmbeddingSumPlaces.proof : EmbeddingSumPlaces.Statement := by
  intro F _ _ g hg
  rw [← Finset.univ.sum_fiberwise (fun σ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have h : ∀ σ ∈ ({σ | InfinitePlace.mk σ = w} : Finset (F →+* ℂ)), g σ = g w.embedding := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    subst hσ
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast card_filter_mk_eq w

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeCountVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeCountVolume

theorem measure_le_encard_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La] [IsZLattice ℝ La]
    (S T : Set E) (hS : MeasurableSet S) (hST : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) {F : Set E}
    (fund : IsAddFundamentalDomain La F μ) :
    μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * μ F := by
  have : MeasurableVAdd La E := (inferInstance : MeasurableVAdd La.toAddSubgroup E)
  have : VAddInvariantMeasure La E μ :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup E μ)
  have : Countable La := inferInstance
  set A := {x : E | x ∈ La ∧ x ∈ T} with hAdef
  have key : ∀ y : E, ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) ≤
      ((A.encard : ℕ∞) : ℝ≥0∞) := by
    intro y
    set U : Set La := {g | (g : E) + y ∈ S} with hUdef
    have h1 : ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, U.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    refine ENat.toENNReal_le.mpr ?_
    rcases U.eq_empty_or_nonempty with hU | ⟨g₀, hg₀⟩
    · simp [hU]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : E) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hsub : (g : E) - g₀ = ((g : E) + y) - ((g₀ : E) + y) := by abel
      show (g : E) - g₀ ∈ T
      rw [hsub]
      exact hST _ hg _ hg₀
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc μ S = ∫⁻ z, S.indicator 1 z ∂μ := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) ∂μ := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) ∂μ :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, ((A.encard : ℕ∞) : ℝ≥0∞) ∂μ := lintegral_mono fun z => key z
    _ = ((A.encard : ℕ∞) : ℝ≥0∞) * μ F := setLIntegral_const _ _


open scoped Classical in
theorem proof : LatticeCountVolume.Statement := by
  intro E _ _ _ _ _ μ _ La _ _ S T hS hST
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La μ fund
  have hFtop : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hFtop]
  exact measure_le_encard_mul μ La S T hS hST fund

end LatticeCountVolume

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMixedBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Metric
open scoped ENNReal NNReal

namespace MixedBoxCount


open scoped Classical in
theorem finite_box (F : Type) [Field F] [NumberField F] (La : Submodule ℤ (mixedSpace F))
    [DiscreteTopology La] (f : InfinitePlace F → ℝ) (hf : ∀ w, 0 < f w) :
    {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w}.Finite := by
  have hsub : {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} ⊆
      closedBall 0 (∑ w, f w) ∩ (La : Set (mixedSpace F)) := by
    rintro y ⟨hyL, hy⟩
    refine ⟨?_, hyL⟩
    rw [mem_closedBall_zero_iff, norm_eq_sup'_normAtPlace]
    refine Finset.sup'_le _ _ fun w _ => (hy w).trans ?_
    exact Finset.single_le_sum (fun v _ => (hf v).le) (Finset.mem_univ w)
  refine Set.Finite.subset ?_ hsub
  refine Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete isBounded_closedBall ?_
  rw [← Submodule.coe_toAddSubgroup]
  exact AddSubgroup.isClosed_of_discrete


open scoped Classical in
theorem normAtPlace_lt_of_mem (F : Type) [Field F] [NumberField F] (g : InfinitePlace F → ℝ≥0)
    {x : mixedSpace F} (hx : x ∈ convexBodyLT F g) (w : InfinitePlace F) : normAtPlace w x < g w := by
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    have := hx.1 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this
  · rw [normAtPlace_apply_of_isComplex hw]
    have := hx.2 ⟨w, hw⟩ (Set.mem_univ _)
    simpa [mem_ball_zero_iff] using this

end MixedBoxCount


open scoped Classical in
theorem MixedBoxCount.proof (h : LatticeCountVolume.Statement) : MixedBoxCount.Statement := by
  intro F _ _ La _ _ f hf
  have hfin := MixedBoxCount.finite_box F La f hf
  refine ⟨hfin, ?_⟩
  set B := {y : mixedSpace F | y ∈ La ∧ ∀ w, normAtPlace w y ≤ f w} with hB
  let g : InfinitePlace F → ℝ≥0 := fun w => ⟨f w / 2, (half_pos (hf w)).le⟩
  have hS : MeasurableSet (convexBodyLT F g) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_ball).prod
      (MeasurableSet.univ_pi fun _ => measurableSet_ball)
  have hdiff : ∀ x ∈ convexBodyLT F g, ∀ y ∈ convexBodyLT F g,
      x - y ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w} := by
    intro x hx y hy w
    have h1 := MixedBoxCount.normAtPlace_lt_of_mem F g hx w
    have h2 := MixedBoxCount.normAtPlace_lt_of_mem F g hy w
    have h3 := normAtPlace_add_le w x (-y)
    rw [normAtPlace_neg, ← sub_eq_add_neg] at h3
    have : ((g w : ℝ≥0) : ℝ) = f w / 2 := rfl
    linarith
  have hle := h (mixedSpace F) volume La (convexBodyLT F g) _ hS hdiff
  have hset : {x : mixedSpace F | x ∈ La ∧ x ∈ {z : mixedSpace F | ∀ w, normAtPlace w z ≤ f w}} = B := rfl
  rw [hset, convexBodyLT_volume, ← hfin.cast_ncard_eq] at hle
  have hcpos := ZLattice.covolume_pos La volume
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hle
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hcpos.le, NNReal.coe_prod,
    NNReal.coe_pow, ENat.toENNReal_coe, ENNReal.toReal_natCast] at hreal
  have hg : ∀ w, ((g w : ℝ≥0) : ℝ) = f w / 2 := fun _ => rfl
  simp only [hg] at hreal
  have hNpos : 0 < B.ncard :=
    (Set.ncard_pos hfin).mpr ⟨0, La.zero_mem, fun w => by simp [(hf w).le]⟩
  have hN : (0 : ℝ) < (B.ncard : ℝ) := by exact_mod_cast hNpos
  have hc : (0 : ℝ) < (convexBodyLTFactor F : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (convexBodyLTFactor_ne_zero F))
  have hfac : ∀ w, 0 < (f w / 2) ^ mult w := fun w => pow_pos (half_pos (hf w)) _
  have hprod : 0 < ∏ w, (f w / 2) ^ mult w := Finset.prod_pos fun w _ => hfac w
  have hlog := Real.log_le_log (mul_pos hc hprod) hreal
  rw [Real.log_mul hc.ne' hprod.ne', Real.log_mul hN.ne' hcpos.ne',
    Real.log_prod (fun w _ => (hfac w).ne')] at hlog
  have hl : ∀ w, Real.log ((f w / 2) ^ mult w) = (mult w : ℝ) * Real.log (f w) - (mult w : ℝ) * Real.log 2 :=
    fun w => by rw [Real.log_pow, Real.log_div (hf w).ne' two_ne_zero, mul_sub]
  have hcast : (∑ w : InfinitePlace F, (mult w : ℝ)) = (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast sum_mult_eq
  simp only [hl, Finset.sum_sub_distrib, ← Finset.sum_mul, hcast] at hlog
  linarith

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StComponentsGenericCount
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def ComponentsGenericCount.Statement : Prop :=
  ∀ (n d : ℕ) (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ J ∈ F, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) ∧ IsFiniteProjection J A) →
    (∀ J ∈ F, ∀ J' ∈ F, J ≤ J' → J = J') →
      (∀ y : Fin d → ℂ,
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard ≤ ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞)) ∧
      ∃ Δ : MvPolynomial (Fin d) ℂ, Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard = ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞) ∧
        ∀ x, (∃ J ∈ F, x ∈ zeroSet J) → A *ᵥ x = y →
          ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ ∃ J ∈ F, g y' ∈ zeroSet J

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeSliceIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeSliceIdeal.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)) (t : Fin n → ℂ) (V : Ideal (MvPolynomial (Fin n) ℂ)),
    (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) → MvPolynomial.vanishingIdeal ℂ C ≤ V →
      MvPolynomial.vanishingIdeal ℂ {x | x ∈ C ∧ MvPolynomial.eval x (linForm t) = 1} ≤
        V ⊔ Ideal.span {linForm t - 1}

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StConeVanishingHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

def ConeVanishingHomog.Statement : Prop :=
  ∀ (n : ℕ) (C : Set (Fin n → ℂ)), (∀ c ∈ C, ∀ a : ℂ, a ≠ 0 → a • c ∈ C) →
    IsHomogIdeal (MvPolynomial.vanishingIdeal ℂ C)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsNumberFieldBoxCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField

def NumberFieldBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B : AddSubgroup F), B.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) →
    ∃ C : ℝ, ∀ L : AddSubgroup F, L.FG → (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∀ ρ : (F →+* ℂ) → ℝ, (∀ σ, 0 < ρ σ) → (∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) →
        ∑ σ : F →+* ℂ, Real.log (ρ σ) + Real.log (genIndex L B) - C ≤
          Real.log (Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ})

end GroundTheory.Heights₂.Heights.Targets
end

