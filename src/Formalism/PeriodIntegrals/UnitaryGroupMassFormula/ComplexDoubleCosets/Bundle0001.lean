module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.CplxDC
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0011
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.ComplexDoubleCoset
section
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

def cf : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]

def part (k : Fin 4) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (![z.re, -z.re, z.im, -z.im] k)

theorem part_ne_top (k : Fin 4) (z : ℂ) : part k z ≠ ⊤ := ENNReal.ofReal_ne_top

theorem part_le (k : Fin 4) (z : ℂ) : part k z ≤ ‖z‖ₑ := by
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  fin_cases k
  · simpa using Complex.re_le_norm z
  · simpa using le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z)
  · simpa using Complex.im_le_norm z
  · simpa using le_trans (neg_le_abs z.im) (Complex.abs_im_le_norm z)

theorem measurable_part (k : Fin 4) : Measurable (part k) := by
  fin_cases k
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_re.neg
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im
  · exact ENNReal.measurable_ofReal.comp Complex.measurable_im.neg

theorem split (z : ℂ) : z = ∑ k, cf k * ((part k z).toReal : ℂ) := by
  simp only [Fin.sum_univ_four, cf, part]
  apply Complex.ext <;> simp [ENNReal.toReal_ofReal'] <;>
    linarith [max_zero_sub_max_neg_zero_eq_self z.re, max_zero_sub_max_neg_zero_eq_self z.im]

theorem toReal_int {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hfin : ∫⁻ x, f x ∂ν ≠ ⊤) (hpt : ∀ x, f x ≠ ⊤) :
    Integrable (fun x => ((f x).toReal : ℂ)) ν ∧
      ∫ x, ((f x).toReal : ℂ) ∂ν = (((∫⁻ x, f x ∂ν).toReal : ℝ) : ℂ) := by
  refine ⟨(integrable_toReal_of_lintegral_ne_top hf hfin).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_toReal hf (Filter.Eventually.of_forall fun x => (hpt x).lt_top)]

theorem poinc_split {G : Type*} [Group G] (E : Set G) (v : Fin 4 → G → ℝ≥0∞) (f : G → ℂ)
    (hf : ∀ x, f x = ∑ k, cf k * ((v k x).toReal : ℂ))
    (hv : ∀ k x, ∑' δ : E, v k ((δ : G) * x) ≠ ⊤) (x : G) :
    poinc E f x = ∑ k, cf k * (((∑' δ : E, v k ((δ : G) * x))).toReal : ℂ) := by
  have hsum : ∀ k, Summable (fun δ : E => ((v k ((δ : G) * x)).toReal : ℂ)) :=
    fun k => Complex.summable_ofReal.2 (ENNReal.summable_toReal (hv k x))
  unfold poinc
  simp_rw [hf]
  rw [Summable.tsum_finsetSum (fun k _ => (hsum k).mul_left (cf k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tsum_mul_left, ← Complex.ofReal_tsum, ENNReal.tsum_toReal_eq (fun δ => ENNReal.ne_top_of_tsum_ne_top (hv k x) δ)]

private theorem sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (a b : Fin 4 → ℝ≥0∞) :
    (∑ k, cf k * ((a k).toReal : ℂ)) * (∑ j, cf j * ((b j).toReal : ℂ)) =
      ∑ k, ∑ j, cf k * cf j * (((a k * b j).toReal : ℝ) : ℂ) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.toReal_mul]; push_cast; ring

theorem complex_double_coset : CplxDC.{u} := by
  unfold CplxDC
  intro G _ _ _ μ _ Γ S S' _ hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ φ ψ hφ hψ hφS hψS hφf hψf hfin
  have hΓc : (Γ : Set G).Countable := Set.countable_coe_iff.1 (by assumption)
  haveI : Countable D := (hΓc.mono hD.1).to_subtype
  haveI : Countable D' := (hΓc.mono hD'.1).to_subtype
  set g : Fin 4 → G → ℝ≥0∞ := fun k y => part k (φ y) with hg_def
  set h : Fin 4 → G → ℝ≥0∞ := fun j y => part j (ψ y) with hh_def
  have hgm : ∀ k, Measurable (g k) := fun k => (measurable_part k).comp hφ
  have hhm : ∀ j, Measurable (h j) := fun j => (measurable_part j).comp hψ
  have hgS : ∀ k, ∀ s ∈ S, ∀ y, g k (s * y) = g k y := fun k s hs y => by simp only [g, hφS s hs y]
  have hhS : ∀ j, ∀ s ∈ S', ∀ y, h j (s * y) = h j y := fun j s hs y => by simp only [h, hψS s hs y]
  have hA : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≤ ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ :=
    fun k x => ENNReal.tsum_le_tsum fun δ => part_le k _
  have hB : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≤ ∑' δ : D', ‖ψ ((δ : G) * x)‖ₑ :=
    fun j x => ENNReal.tsum_le_tsum fun δ => part_le j _
  have hAfin : ∀ k x, ∑' δ : D, g k ((δ : G) * x) ≠ ⊤ := fun k x => ne_top_of_le_ne_top (hφf x) (hA k x)
  have hBfin : ∀ j x, ∑' δ : D', h j ((δ : G) * x) ≠ ⊤ := fun j x => ne_top_of_le_ne_top (hψf x) (hB j x)
  have hprod : ∀ x, poinc D φ x * poinc D' ψ x = ∑ k, ∑ j, cf k * cf j *
      ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ) := fun x => by
    rw [poinc_split D g φ (fun y => split (φ y)) hAfin x, poinc_split D' h ψ (fun y => split (ψ y)) hBfin x,
      sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul]
  have hABm : ∀ k j, Measurable (fun x => (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)) :=
    fun k j => (Measurable.tsum fun δ => (hgm k).comp (measurable_const_mul _)).mul
      (Measurable.tsum fun δ => (hhm j).comp (measurable_const_mul _))
  have hABfin : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ ≠ ⊤ :=
    fun k j => ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul' (hA k x) (hB j x))
  have hint := fun k j => toReal_int (ν := μ.restrict FΓ) (hABm k j).aemeasurable (hABfin k j)
    (fun x => ENNReal.mul_ne_top (hAfin k x) (hBfin j x))
  have hunf : ∀ k j, ∫⁻ x in FΓ, (∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x) ∂μ =
      ∑' r : R, ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ := fun k j =>
    fold_dc_unfold G μ Γ S S' hSΓ hS'Γ D D' hD hD' R hR Fs hFs FΓ hFΓ (g k) (h j) (hgm k) (hhm j)
      (hgS k) (hhS j)
  have hIfin : ∀ k j (r : R), ∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ ≠ ⊤ := fun k j r =>
    ENNReal.ne_top_of_tsum_ne_top (by rw [← hunf k j]; exact hABfin k j) r
  have hrint := fun k j (r : R) => toReal_int (ν := μ.restrict (Fs r)) (f := fun x => g k x * h j ((r : G)⁻¹ * x))
    ((hgm k).mul ((hhm j).comp (measurable_const_mul _))).aemeasurable (hIfin k j r)
    (fun x => ENNReal.mul_ne_top (part_ne_top _ _) (part_ne_top _ _))
  have hprod2 : ∀ (r : G) x, φ x * ψ (r⁻¹ * x) =
      ∑ k, ∑ j, cf k * cf j * (((g k x * h j (r⁻¹ * x)).toReal : ℝ) : ℂ) := fun r x => by
    rw [split (φ x), split (ψ (r⁻¹ * x))]
    exact sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul _ _
  have hsI : ∀ k j, Summable (fun r : R => (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ)) :=
    fun k j => Complex.summable_ofReal.2 (ENNReal.summable_toReal (by rw [← hunf k j]; exact hABfin k j))
  rw [show (fun x => poinc D φ x * poinc D' ψ x) = _ from funext hprod]
  have hI1 : Integrable (fun x => ∑ k, ∑ j, cf k * cf j *
      ((((∑' δ : D, g k ((δ : G) * x)) * ∑' δ : D', h j ((δ : G) * x)).toReal : ℝ) : ℂ)) (μ.restrict FΓ) :=
    MeasureTheory.integrable_finsetSum _ fun k _ => MeasureTheory.integrable_finsetSum _ fun j _ => ((hint k j).1).const_mul _
  refine ⟨hI1, ?_⟩
  have hr : ∀ r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ =
      ∑ k, ∑ j, cf k * cf j * (((∫⁻ x in Fs r, g k x * h j ((r : G)⁻¹ * x) ∂μ).toReal : ℝ) : ℂ) := by
    intro r
    simp_rw [hprod2 (r : G)]
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _ fun j _ => ((hrint k j r).1).const_mul _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => ((hrint k j r).1).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, (hrint k j r).2]
  rw [tsum_congr hr, MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _ fun j _ => ((hint k j).1).const_mul _),
    Summable.tsum_finsetSum (fun k _ => summable_sum fun j _ => (hsI k j).mul_left _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => ((hint k j).1).const_mul _),
    Summable.tsum_finsetSum (fun j _ => (hsI k j).mul_left _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, (hint k j).2, hunf k j, tsum_mul_left, ← Complex.ofReal_tsum,
    ENNReal.tsum_toReal_eq (hIfin k j)]

end PI.PoincareSeriesInner.W
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ComplexDoubleCosets.FoldL2ComplexOf
section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

theorem fold_L2_complex_of (hc : CplxDC.{u}) (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : PoincareSeriesInner G μ := by
  intro Γ S S' hΓ hS hS' Ω hΩ h1 a a' Ph Ph' hP hP' F F' hF hF' hm hm' D D' hD hD' R hR Fs hFs FΓ hFΓ
  haveI : Countable Γ := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  obtain ⟨hPm, hPinv, hPb⟩ := hP
  obtain ⟨hPm', hPinv', hPb'⟩ := hP'
  have hΩm : MeasurableSet Ω := hΩ.isClosed.measurableSet
  obtain ⟨hM1, hMfin, hMinv, hMm⟩ := overlapMultiplicityProperties G Γ hΓ Ω hΩ h1
  have hbd := foldBound_holds G μ Γ S hΓ hS Ω hΩm a Ph hPm hPinv hPb F hF D hD
  have hbd' := foldBound_holds G μ Γ S' hΓ hS' Ω hΩm a' Ph' hPm' hPinv' hPb' F' hF' D' hD'
  have hQf : quotientLIntegral μ F Ph < ∞ := by
    refine lt_of_le_of_lt ?_ hm
    exact lintegral_mono fun y => le_mul_of_one_le_left zero_le' (hM1 y)
  have hQf' : quotientLIntegral μ F' Ph' < ∞ := by
    refine lt_of_le_of_lt ?_ hm'
    exact lintegral_mono fun y => le_mul_of_one_le_left zero_le' (hM1 y)
  have hK : ∫⁻ x in FΓ, mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ = multiplicityLIntegral μ Γ Ω F' Ph' := by
    have hfun : (fun x => mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ)
        = fun x => ∑' δ' : D', mult Γ Ω (δ' * x) * ‖Ph' (δ' * x)‖ₑ := by
      funext x
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun δ' => ?_
      rw [hMinv δ' (hD'.1 δ'.2) x]
    rw [hfun]
    exact lintegralTransversalSum G μ Γ S' hS' F' hF' FΓ hFΓ D' hD' (fun y => mult Γ Ω y * ‖Ph' y‖ₑ)
      (hMm.mul hPm'.enorm) (fun s hs y => by simp only [hMinv s (hS' hs) y, hPinv' s hs y])
  have hne : (a : ℝ≥0∞) * quotientLIntegral μ F Ph ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hQf.ne
  have hfin : (a : ℝ≥0∞) * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' < ∞ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hQf) hm'
  have hI : ∫⁻ x in FΓ, (∑' δ : D, ‖Ph (δ * x)‖ₑ) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ
      ≤ a * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' := by
    calc _ ≤ ∫⁻ x in FΓ, ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * (mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc (∑' δ : D, ‖Ph (δ * x)‖ₑ) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ
              ≤ (a * mult Γ Ω x * quotientLIntegral μ F Ph) * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ := mul_le_mul' (hbd x) le_rfl
            _ = _ := by ring
      _ = ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * ∫⁻ x in FΓ, mult Γ Ω x * ∑' δ' : D', ‖Ph' (δ' * x)‖ₑ ∂μ :=
          lintegral_const_mul' _ _ hne
      _ = _ := by rw [hK]
  have hunf := fold_dc_unfold G μ Γ S S' hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ
    (fun x => ‖Ph x‖ₑ) (fun x => ‖Ph' x‖ₑ) hPm.enorm hPm'.enorm
    (fun s hs y => by simp only [hPinv s hs y]) (fun s hs y => by simp only [hPinv' s hs y])
  have h2 : ∑' r : R, ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ < ∞ := by
    rw [← hunf]
    exact hI.trans_lt hfin
  have hconj : Measurable (fun z : ℂ => (starRingEnd ℂ) z) := Complex.continuous_conj.measurable
  have henc : ∀ z : ℂ, ‖(starRingEnd ℂ) z‖ₑ = ‖z‖ₑ := fun z => by simp
  refine ⟨?_, h2, ?_, ?_⟩
  · calc ∫⁻ x in F', ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph (δ * x)‖ₑ ∂μ
        ≤ ∫⁻ x in F', ((a : ℝ≥0∞) * quotientLIntegral μ F Ph) * (mult Γ Ω x * ‖Ph' x‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc ‖Ph' x‖ₑ * ∑' δ : D, ‖Ph (δ * x)‖ₑ ≤ ‖Ph' x‖ₑ * (a * mult Γ Ω x * quotientLIntegral μ F Ph) :=
                mul_le_mul' le_rfl (hbd x)
            _ = _ := by ring
      _ = a * quotientLIntegral μ F Ph * multiplicityLIntegral μ Γ Ω F' Ph' := by
          rw [lintegral_const_mul' _ _ hne]
          rfl
  · intro r hr
    have hle : ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' (r⁻¹ * x)‖ₑ ∂μ < ∞ :=
      (ENNReal.le_tsum (f := fun r : R => ∫⁻ x in Fs r, ‖Ph x‖ₑ * ‖Ph' ((r : G)⁻¹ * x)‖ₑ ∂μ)
        ⟨r, hr⟩).trans_lt h2
    refine ⟨(hPm.mul (hconj.comp (hPm'.comp (measurable_const_mul _)))).aestronglyMeasurable, ?_⟩
    simpa [HasFiniteIntegral, enorm_mul, henc] using hle
  · have hψm : Measurable (fun x => (starRingEnd ℂ) (Ph' x)) := hconj.comp hPm'
    have hpc : ∀ x, poinc D' (fun y => (starRingEnd ℂ) (Ph' y)) x = (starRingEnd ℂ) (poinc D' Ph' x) :=
      fun x => by simp only [poinc, Complex.conj_tsum]
    have key := hc G μ Γ S S' hS hS' D D' hD hD' R hR Fs hFs FΓ hFΓ Ph (fun x => (starRingEnd ℂ) (Ph' x))
      hPm hψm hPinv (fun s hs y => by simp only [hPinv' s hs y])
      (fun x => ((hbd x).trans_lt (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.coe_lt_top (hMfin x)) hQf)).ne)
      (fun x => by
        simp only [henc]
        exact ((hbd' x).trans_lt (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top ENNReal.coe_lt_top (hMfin x)) hQf')).ne)
      (by
        simp only [henc]
        exact (hI.trans_lt hfin).ne)
    simp only [hpc] at key
    exact key

end PI.PoincareSeriesInner.W
end

