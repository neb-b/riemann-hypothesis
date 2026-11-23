module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaLiftOfPurelyInseparable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaLift

theorem mem_iff_pow_mem {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (y : F) :
    y ∈ A ↔ y ^ m ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_pow]
  exact (pow_le_one_iff_of_nonneg zero_le' hm.ne').symm

theorem nonunit_of_pow {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (z : F)
    (h : A.valuation (z ^ m) < 1) : A.valuation z < 1 := by
  rw [map_pow] at h
  by_contra h'
  push_neg at h'
  exact absurd h (not_lt.2 (one_le_pow₀ h'))

end GlobalTheory.InertiaLift

open GlobalTheory.InertiaLift in
theorem GlobalTheory.inertia_lift_of_purelyInseparable : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra L Ω'] [Algebra K Ω'] (j : Ω →ₐ[K] Ω'), (∀ y : Ω', ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m) → ∀ (V' : ValuationSubring Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[L] Ω'), (∀ x, σ' (j x) = j (σ x)) → σ ∈ inertia K (V'.comap (j : Ω →+* Ω')) → σ' ∈ inertia L V' := by
  intro K L Ω Ω' _ _ _ _ _ _ _ j hpi V' σ σ' hcomm hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨hσV, hσv⟩ := hσ
  set V := V'.comap (j : Ω →+* Ω') with hV
  have hmemV : ∀ x, j x ∈ V' ↔ x ∈ V := fun x => Iff.rfl
  have hσmem : ∀ x, σ x ∈ V ↔ x ∈ V := by
    intro x
    constructor
    · intro h
      have h2 : σ x ∈ σ • V := by rw [hσV]; exact h
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h2
      simpa using h2
    · intro h
      have h2 : σ • x ∈ σ • V := ValuationSubring.smul_mem_pointwise_smul σ x V h
      rw [hσV] at h2
      exact h2
  have hσ'mem : ∀ y, σ' y ∈ V' ↔ y ∈ V' := by
    intro y
    obtain ⟨m, x, hm, hyx, -⟩ := hpi y
    rw [mem_iff_pow_mem V' hm, mem_iff_pow_mem V' hm y, ← map_pow, hyx, hcomm, hmemV, hmemV, hσmem]
  have hlt : ∀ w, V.valuation w < 1 → V'.valuation (j w) < 1 := by
    intro w hw
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hw ⊢
    rcases hw with hw | hw
    · left; simp [hw]
    · right
      rw [← map_inv₀]
      exact hw
  refine ⟨?_, ?_⟩
  · ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ'mem (σ'⁻¹ • z)
    simp only [AlgEquiv.smul_def] at this ⊢
    rw [← this]
    simp
  · intro y hy
    obtain ⟨m, x, hm, hyx, hfrob⟩ := hpi y
    have hx : x ∈ V := by rw [← hmemV, ← hyx]; exact (mem_iff_pow_mem V' hm y).1 hy
    apply nonunit_of_pow V' hm
    rw [hfrob, ← map_pow, hyx, hcomm, ← map_sub]
    exact hlt _ (hσv x hx)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDegreeOfNormBound
section
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

end GlobalTheory.DegCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · have hl : A.loc α i v = 0 := by
        unfold loc
        exact dif_neg ht
      simp only [hr, hl, dens_zero, Complex.zero_re]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwiseStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise : ∀ (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ), (∀ a, Continuous (g a)) →
    (∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) →
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | exact GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | (intros; apply GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
section
set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder ENNReal
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def reDens (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem loc_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α - β) i v = A.loc α i v - A.loc β i v := by
  unfold loc; split_ifs
  · rfl
  · exact (sub_zero 0).symm

theorem dens_sub' (x y : Alt n) : dens (x - y) = dens x - dens y := by
  simp only [dens, map_sub, Finsupp.sub_apply, sub_div]

theorem reDens_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.reDens (α - β) i v = A.reDens α i v - A.reDens β i v := by
  simp only [reDens, loc_sub, dens_sub', Complex.sub_re]

theorem reDens_compat {α : A.Fld} (hα : A.IsForm α) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    A.reDens α i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * A.reDens α j (A.e j y) := by
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [reDens]
  erw [h1, h2, h3, _root_.GlobalTheory.CxForm.dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

theorem continuousOn_reDens {α : A.Fld} (hα : A.IsForm α) (i : A.ι) :
    ContinuousOn (A.reDens α i) (A.e i).target := by
  have := (hα.smooth i Finset.univ).continuousOn
  exact Complex.continuous_re.comp_continuousOn (this.div_const _)

theorem aemeasurable_ofReal_chart [MeasurableSpace M] (e : OpenPartialHomeomorph M (V n)) (r : V n → ℝ)
    (hr : ContinuousOn r e.target) :
    AEMeasurable (fun v => ENNReal.ofReal (r (e (e.symm v)))) (volume.restrict (e.target ∩ e.symm ⁻¹' univ)) := by
  rw [preimage_univ, inter_univ]
  have h := (ENNReal.continuous_ofReal.comp_continuousOn hr).aemeasurable (μ := volume) e.open_target.measurableSet
  refine h.congr ((ae_restrict_iff' e.open_target.measurableSet).2 (Filter.Eventually.of_forall fun v hv => ?_))
  simp [e.right_inv hv]

theorem ofReal_compat (r : A.ι → V n → ℝ)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source) (hj : y ∈ (A.e j).source) :
    ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]

theorem glueMeas_add_three [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (r₁ r₂ r₃ : A.ι → V n → ℝ)
    (hr₁ : ∀ i, ContinuousOn (r₁ i) (A.e i).target) (hr₂ : ∀ i, ContinuousOn (r₂ i) (A.e i).target)
    (hc₁ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₁ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₁ j (A.e j y))
    (hc₂ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₂ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₂ j (A.e j y))
    (hc₃ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₃ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₃ j (A.e j y)) :
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) univ =
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₂ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₃ i (A.e i y))) univ := by
  have c₁ := A.ofReal_compat r₁ hc₁
  have c₂ := A.ofReal_compat r₂ hc₂
  have c₃ := A.ofReal_compat r₃ hc₃
  rw [ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aemeasurable_ofReal_chart (A.e i) _ (hr₁ i)).add (aemeasurable_ofReal_chart (A.e i) _ (hr₂ i))),
    ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aemeasurable_ofReal_chart (A.e i) _ (hr₁ i))]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal (-x) + ENNReal.ofReal y =
      ENNReal.ofReal (-(x - y)) + ENNReal.ofReal x + ENNReal.ofReal (-y) := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x - y) 0 + max (-x) 0 + max y 0 = max (-(x - y)) 0 + max x 0 + max (-y) 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x - y), m (-x), m y, m (-(x - y)), m x, m (-y),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

theorem integral_sub [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α - β) = A.integral α - A.integral β := by
  have hF := A.reDens_compat hα
  have hG := A.reDens_compat hβ
  have cF := A.continuousOn_reDens hα
  have cG := A.continuousOn_reDens hβ

  let lin (c d : ℝ) : A.ι → V n → ℝ := fun i v => c * A.reDens α i v + d * A.reDens β i v
  have hlin (c d : ℝ) : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      lin c d i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * lin c d j (A.e j y) := by
    intro i j y hi hj
    simp only [lin, hF i j y hi hj, hG i j y hi hj]
    ring
  have clin (c d : ℝ) (i : A.ι) : ContinuousOn (lin c d i) (A.e i).target :=
    (continuousOn_const.mul (cF i)).add (continuousOn_const.mul (cG i))
  let P (c d : ℝ) : ℝ≥0∞ := ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (lin c d i (A.e i y))) univ
  have fin (c d : ℝ) : P c d ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (lin c d) (clin c d) (hlin c d)
  have part_eq (γ : A.Fld) (ε : ℤˣ) (c d : ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = lin c d i v) :
      A.part γ ε univ = P c d := by
    simp only [part, P]
    congr 2
    funext i y
    rw [← h]
    rfl
  have e1 := part_eq (α - β) 1 1 (-1) fun i v => by simp [lin, reDens_sub]; ring
  have e2 := part_eq (α - β) (-1) (-1) 1 fun i v => by simp [lin, reDens_sub]; ring
  have e3 := part_eq α 1 1 0 fun i v => by simp [lin]
  have e4 := part_eq α (-1) (-1) 0 fun i v => by simp [lin]
  have e5 := part_eq β 1 0 1 fun i v => by simp [lin]
  have e6 := part_eq β (-1) 0 (-1) fun i v => by simp [lin]
  have key : P 1 (-1) + P (-1) 0 + P 0 1 = P (-1) 1 + P 1 0 + P 0 (-1) := by
    simp only [P]
    rw [← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _),
      ← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _)]
    congr 2
    funext i y
    have := ofReal_posNeg (A.reDens α i (A.e i y)) (A.reDens β i (A.e i y))
    simp only [lin]
    convert this using 3 <;> ring_nf
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)] at key'
  simp only [integral, Measure.real, e1, e2, e3, e4, e5, e6]
  linarith

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_sub_of_isForm : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.integral (α - β) = A.integral α - A.integral β :=
  fun A α β hα hβ => A.integral_sub α β hα hβ

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem isAbelianScheme_baseChange_field_and_comm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) ∧ IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A) := by
  intro K L _ _ _ A _ _ hA
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap (algebraMap K L)) A hA
  exact ⟨hB, hB.comm⟩

end GlobalTheory.Published.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmConnProper

theorem isAbelianScheme_of_smConn_of_isProper (S : Scheme.{0}) (G : Over S) [GrpObj G]
    (h : GlobalTheory.SS.SmConn G) (hp : IsProper G.hom) : IsAbelianScheme G :=
  ⟨h.1, h.2.1, hp, h.2.2.2.2⟩

end GlobalTheory.SmConnProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAbove
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbVarRed

theorem isDiscreteValuationRing_of_isAbove :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
      [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
      (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  intro R K _ _ _ _ _ _ L _ _ _ V h
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun _ => rfl
  have memV : ∀ a : K, algebraMap K L a ∈ V ↔ a ∈ (algebraMap R K).range := fun a => by
    rw [← h]; rfl
  let W : Subalgebra R L :=
    { V.toSubring with
      algebraMap_mem' := fun r => (memV (algebraMap R K r)).2 ⟨r, rfl⟩ }
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki K W).1
  have hnf : ¬ IsField V := by
    intro hf
    apply IsDiscreteValuationRing.not_isField R
    have hs : Function.Surjective (algebraMap R K) := fun x => by
      by_cases hx : x = 0
      · exact ⟨0, by simp [hx]⟩
      have hxL : algebraMap K L x ≠ 0 := (map_ne_zero _).2 hx
      have hmem : algebraMap K L x ∈ V := by
        rcases V.mem_or_inv_mem (algebraMap K L x) with h1 | h1
        · exact h1
        · obtain ⟨y, hy⟩ := hf.mul_inv_cancel (a := (⟨_, h1⟩ : V))
            (fun e => inv_ne_zero hxL (congrArg Subtype.val e))
          have hy' : (algebraMap K L x)⁻¹ * (y : L) = 1 := congrArg Subtype.val hy
          have : (y : L) = algebraMap K L x := by
            rw [← inv_inv (algebraMap K L x)]
            exact eq_inv_of_mul_eq_one_right hy'
          exact this ▸ y.2
      exact (memV x).1 hmem
    exact (RingEquiv.ofBijective (algebraMap R K) ⟨IsFractionRing.injective R K, hs⟩).toMulEquiv.isField
      (Field.toIsField K)
  have hval : ValuationRing V := inferInstance
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval

end GlobalTheory.AbVarRed
end

