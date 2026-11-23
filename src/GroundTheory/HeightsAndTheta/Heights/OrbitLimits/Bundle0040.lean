module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PClosedPointUnitSection
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveBoxSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxSmall.zpow_mul_toNat_neg {F : Type} [Field F] {t : F} (ht : t ≠ 0) (n : ℤ) :
    t ^ n * t ^ (-n).toNat = t ^ n.toNat :=
  calc t ^ n * t ^ (-n).toNat = t ^ ((n.toNat : ℤ) - ((-n).toNat : ℤ)) * t ^ (-n).toNat := by
        rw [Int.toNat_sub_toNat_neg]
    _ = t ^ n.toNat := by
        rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ ht)]

theorem CurveBoxSmall.proof : CurveBoxSmall.Statement := by
  intro K _ ι _ Ω _ y A c hP hB hc τ s
  classical
  have hU : ∀ σ : Ω →+* ℂ, ‖σ (chartUnit y c A.a τ)‖ = (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ => by
    rw [chartUnit, map_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀, norm_zpow, ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
  have hQ : ∀ σ : Ω →+* ℂ, 0 < (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ =>
    pow_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr ((map_ne_zero σ).mpr (hc k))) _) _
  constructor
  · intro hS σ
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB (s / chartUnit y c A.a τ)
    let ap : K → ℕ := fun k => ((τ : ℤ) * A.a k).toNat
    let am : K → ℕ := fun k => (-((τ : ℤ) * A.a k)).toNat
    have hU0 : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hu : chartUnit y c A.a τ * ∏ k, y ⟨k, c k⟩ ^ am k = ∏ k, y ⟨k, c k⟩ ^ ap k := by
      rw [chartUnit, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => CurveBoxSmall.zpow_mul_toNat_neg (hc k) _
    have hdeg : ∀ k, (((d + ap) k : ℕ) : ℤ) = ((d + am) k : ℕ) + τ * A.a k := fun k => by
      have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
      simp only [Pi.add_apply, Nat.cast_add, ap, am]
      omega
    have hval : aeval y (g * curveChartMono c ap) = s * aeval y (h * curveChartMono c am) := by
      simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X]
      rw [← hu, hgh]
      field_simp
    have hS' := hS _ _ _ _ _ (CurveOrbit.isMultiHomog_mul hg (isMultiHomog_curveChartMono c ap))
      (CurveOrbit.isMultiHomog_mul hh (isMultiHomog_curveChartMono c am)) hdeg hval (CurveOrbit.mem_mcPts σ y hc)
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp] at hS'
    simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X, norm_mul, norm_prod, norm_pow] at hS'
    have hsu : s / chartUnit y c A.a τ = aeval y g / aeval y h := eq_div_of_mul_eq hh0 hgh.symm
    have hσh : 0 < ‖σ (aeval y h)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hh0)
    have ht : ∀ k, ‖σ (y ⟨k, c k⟩)‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (hc k))
    have hR : (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k =
        ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
      exact CurveBoxSmall.zpow_mul_toNat_neg (ht k) _
    have hRm : 0 < ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k :=
      Finset.prod_pos fun k _ => pow_pos (lt_of_le_of_ne (norm_nonneg _) (ht k).symm) _
    rw [hsu, map_div₀, norm_div, chartRadius, div_pow, div_le_div_iff₀ hσh (hQ σ)]
    refine le_of_mul_le_mul_right ?_ hRm
    calc ‖σ (aeval y g)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k
        = ‖σ (aeval y g)‖ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by rw [mul_assoc, hR]
      _ ≤ ‖σ (aeval y h)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k) * A.h (fun p => σ (y p)) ^ τ := hS'
      _ = _ := by ring
  · intro hbox dg dh g h z hg hh hdeg hgs hz
    obtain ⟨σ, l, hl, rfl⟩ := CurveOrbit.exists_sameOrbit hP hB hz
    beta_reduce
    have hb := hbox σ
    rw [map_div₀, norm_div, chartRadius, div_pow, hU σ, div_le_div_iff_of_pos_right (hQ σ)] at hb
    have hlam : ‖∏ k, l k ^ dg k‖ = ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ := by
      rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hlk : ‖l k‖ ≠ 0 := norm_ne_zero_iff.mpr (hl k)
      rw [norm_pow, norm_pow, ← zpow_natCast (‖l k‖) (dg k), hdeg k, zpow_add₀ hlk, zpow_natCast,
        ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
    rw [CurveOrbit.eval_smul _ l hg, CurveOrbit.eval_smul _ l hh, A.smul l _ hl, CurveOrbit.eval_comp,
      CurveOrbit.eval_comp, hgs, map_mul, norm_mul, norm_mul, norm_mul, hlam, mul_pow]
    calc ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * (‖σ s‖ * ‖σ (aeval y h)‖)
        = (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * ‖σ s‖ := by ring
      _ ≤ (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * A.h (fun p => σ (y p)) ^ τ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveClosedPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

noncomputable section

namespace CurveClosedPointChartAlt

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k)

abbrev fld : IntermediateField ℚ Ω :=
  CoordinateConeArithVar.ratioField (SegreChart.segre y) (fun _ ↦ f)

def pt : (Σ _ : Unit, ∀ k, ι k) → fld y f :=
  CoordinateConeArithVar.ratioPtL (SegreChart.segre y) (fun _ ↦ f)

theorem coe_pt (q : Σ _ : Unit, ∀ k, ι k) :
    ((pt y f q : fld y f) : Ω) = SegreChart.segre y q / SegreChart.segre y ⟨(), f⟩ := rfl

variable {y f}

theorem numberField (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : NumberField (fld y f) := by
  have : Finite (coneRatios (SegreChart.segre y) fun _ ↦ f) := (Set.finite_range _).to_subtype
  have : FiniteDimensional ℚ (fld y f) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    exact (SegreChart.isAlgebraic_segre_ratio hP f hf g).isIntegral)
  exact {}

theorem isArithVar_pt (hP : IsArithVar (mCoordIdeal y) 1) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    IsArithVar (mCoordIdeal (pt y f)) 1 := by
  rw [pt, CoordinateConeArithVar.mCoordIdeal_ratioPtL _ _ fun _ ↦ (SegreChart.segre_ne_zero_iff y f).mpr hf]
  exact SegreChart.isArithVar_segre hP f hf

theorem pt_ne_zero_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    pt y f ⟨(), g⟩ ≠ 0 ↔ ∀ k, y ⟨k, g k⟩ ≠ 0 := by
  rw [← SegreChart.segre_ne_zero_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, coe_pt, div_eq_zero_iff, not_or,
    and_iff_left ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem coe_pt_ratio (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g h : ∀ k, ι k) :
    ((pt y f ⟨(), h⟩ / pt y f ⟨(), g⟩ : fld y f) : Ω) =
      SegreChart.segre y ⟨(), h⟩ / SegreChart.segre y ⟨(), g⟩ := by
  rw [IntermediateField.coe_div, coe_pt, coe_pt,
    div_div_div_cancel_right₀ ((SegreChart.segre_ne_zero_iff y f).mpr hf)]

theorem map_chartRingZ (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0) :
    (chartRingZ (pt y f) (fun _ ↦ g)).map (algebraMap (fld y f) Ω).toIntAlgHom = chartRingZ y g := by
  rw [chartRingZ, ← Algebra.adjoin_image, ← Set.range_comp, ← SegreChart.chartRingZ_segre y g hg, chartRingZ]
  congr 2
  funext q
  obtain ⟨⟨⟩, h⟩ := q
  exact coe_pt_ratio hf g h

theorem mem_chartRingZ_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) (hg : ∀ k, y ⟨k, g k⟩ ≠ 0)
    (x : fld y f) : x ∈ chartRingZ (pt y f) (fun _ ↦ g) ↔ (x : Ω) ∈ chartRingZ y g := by
  rw [← map_chartRingZ hf g hg, Subalgebra.mem_map]
  refine ⟨fun h ↦ ⟨x, h, rfl⟩, ?_⟩
  rintro ⟨x', hx', he⟩
  rwa [show x' = x from Subtype.ext he] at hx'

theorem mem_curveRing_iff (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (x : fld y f) :
    x ∈ curveRing (pt y f) ↔ (x : Ω) ∈ curveRing y := by
  rw [mem_curveRing, mem_curveRing]
  refine ⟨fun h g hg ↦ (mem_chartRingZ_iff hf g hg x).1 (h _ fun _ ↦ (pt_ne_zero_iff hf g).2 hg),
    fun h c hc ↦ ?_⟩
  have hc' := (pt_ne_zero_iff hf (c ())).1 (hc ())
  exact (mem_chartRingZ_iff hf (c ()) hc' x).2 (h _ hc')

theorem exists_of_mem_curveRing (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) {b : Ω} (hb : b ∈ curveRing y) :
    ∃ x : fld y f, (x : Ω) = b := by
  have h := mem_curveRing.mp hb f hf
  rw [← map_chartRingZ hf f hf, Subalgebra.mem_map] at h
  obtain ⟨x, -, hx⟩ := h
  exact ⟨x, hx⟩

end CurveClosedPointChartAlt


open CurveClosedPointChartAlt in
theorem CurveClosedPointChart.proof : CurveClosedPointChart.Statement := by
  classical
  intro K _ ι _ Ω _ y hP m hm
  have := SegreChart.charZero_of_isArithVar hP
  obtain ⟨f, hf⟩ := SegreChart.exists_chart hP
  have := numberField hP hf
  let φ : curveRing (pt y f) →+* curveRing y :=
    RingHom.codRestrict ((algebraMap (fld y f) Ω).comp (curveRing (pt y f)).subtype) (curveRing y)
      fun x ↦ (mem_curveRing_iff hf x).1 x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := exists_of_mem_curveRing hf hb
    exact ⟨⟨x, (mem_curveRing_iff hf x).2 hb⟩, rfl⟩
  have hm' : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  obtain ⟨t, ht, hrat⟩ := ClosedPointChart.proof ClosedPointUnitSection.proof (∀ k, ι k) (fld y f) (pt y f)
    (isArithVar_pt hP hf) (m.comap φ) hm'
  have hyt := (pt_ne_zero_iff hf t).1 ht
  refine ⟨t, hyt, fun p ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := hrat (Function.update t p.1 p.2)
  refine ⟨φ a, φ b, hb, ?_⟩
  have h1 := congrArg (fun x : fld y f ↦ (x : Ω)) hab
  simp only [IntermediateField.coe_mul] at h1
  rw [coe_pt_ratio hf, SegreChart.segre_ratio, SegreChart.prod_ratio_update y t hyt p] at h1
  exact h1

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveEmbedOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

namespace CurveEmbedOrbit

theorem sameOrbit_refl {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_symm {K : Type} {ι : K → Type} {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : SameOrbit w z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

theorem sameOrbit_trans {K : Type} {ι : K → Type} {z w u : (Σ k, ι k) → ℂ} (h1 : SameOrbit z w)
    (h2 : SameOrbit w u) : SameOrbit z u := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  exact ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), funext fun p => by simp only; ring⟩

theorem eq_of_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} (hB : Birational y) {σ τ : Ω →+* ℂ}
    (hst : SameOrbit (fun p => σ (y p)) (fun p => τ (y p))) : σ = τ := by
  obtain ⟨c, hc, hcy⟩ := hst
  ext s
  obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
  have key : ∀ ρ : Ω →+* ℂ, ρ s * eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) h) =
      eval (fun p => ρ (y p)) (map (Int.castRingHom ℂ) g) := fun ρ => by
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp, hgs, map_mul]
  have e1 := key σ
  have e2 := key τ
  rw [hcy, CurveOrbit.eval_smul _ _ hh, CurveOrbit.eval_smul _ _ hg] at e1
  have hE : eval (fun p => τ (y p)) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    rw [CurveOrbit.eval_comp]
    exact (map_ne_zero τ).mpr hh0
  have hC : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  apply mul_right_cancel₀ (mul_ne_zero hC hE)
  linear_combination e1 - (∏ k, c k ^ d k) * e2

end CurveEmbedOrbit


open CurveEmbedOrbit in
theorem CurveEmbedOrbit.proof : CurveEmbedOrbit.Statement := by
  intro K _ ι _ Ω _ y R hP hB hR hRu
  classical
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hex : ∀ t : R, ∃ σ : Ω →+* ℂ, SameOrbit (t : (Σ k, ι k) → ℂ) (fun p => σ (y p)) :=
    fun t => CurveOrbit.exists_sameOrbit hP hB (hR t t.2)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro t s hts
    have h1 : SameOrbit (t : (Σ k, ι k) → ℂ) s :=
      sameOrbit_trans (hf t) (by rw [hts]; exact sameOrbit_symm (hf s))
    exact Subtype.ext ((hRu t (hR t t.2)).unique ⟨t.2, sameOrbit_refl _⟩ ⟨s.2, h1⟩)
  have hsurj : Function.Surjective f := by
    intro τ
    obtain ⟨t, ⟨htR, hzt⟩, -⟩ := hRu _ (CurveOrbit.mem_mcPts τ y hj)
    exact ⟨⟨t, htR⟩, eq_of_sameOrbit hB
      (sameOrbit_trans (sameOrbit_symm (hf ⟨t, htR⟩)) (sameOrbit_symm hzt))⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveFieldNumber
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

noncomputable section

theorem CurveFieldNumber.proof (hR1 : RegularityFunctionFieldNumber.Statement) : CurveFieldNumber.Statement := by
  intro K _ ι _ Ω _ y hA hB
  set P := mCoordIdeal y with hPdef
  have : P.IsPrime := hA.2.1.1
  obtain ⟨hF, hN⟩ := hR1 K ι P hA
  let L := FractionRing (MvPolynomial K Ω)

  let j : MRing ι ⧸ P →+* L :=
    (algebraMap (MvPolynomial K Ω) L).comp (RingHom.kerLift (mConeMap y : MRing ι →+* MvPolynomial K Ω))
  have hj : Function.Injective j :=
    (IsFractionRing.injective (MvPolynomial K Ω) L).comp (RingHom.kerLift_injective _)
  let Φ : FractionRing (MRing ι ⧸ P) →+* L := IsFractionRing.lift hj
  let c : Ω →+* L := (algebraMap (MvPolynomial K Ω) L).comp MvPolynomial.C
  have hΦ : ∀ f, Φ (algebraMap _ _ (Ideal.Quotient.mk P f)) = algebraMap _ L (mConeMap y f) := fun f =>
    (IsFractionRing.lift_algebraMap hj _).trans (congrArg (algebraMap (MvPolynomial K Ω) L)
      (RingHom.kerLift_mk (mConeMap y : MRing ι →+* MvPolynomial K Ω) f))

  have hform : ∀ {g : MRing ι} {a : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      Φ (algebraMap _ _ (Ideal.Quotient.mk P g)) = c (aeval y g) * algebraMap _ L (∏ k, (X k : MvPolynomial K Ω) ^ a k) := by
    intro g a hg
    rw [hΦ, LowerBoundFree.mConeMap_of_isMultiHomog y hg, map_mul]; rfl
  have hT : ∀ a : K → ℕ, algebraMap (MvPolynomial K Ω) L (∏ k, (X k : MvPolynomial K Ω) ^ a k) ≠ 0 := fun a =>
    (map_ne_zero_iff _ (IsFractionRing.injective _ L)).2 (Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ (X_ne_zero k))

  have hmem : ∀ {g : MRing ι} {a : K → ℕ}, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a → aeval y g = 0 → g ∈ P := by
    intro g a hg h0
    show mConeMap y g = 0
    rw [LowerBoundFree.mConeMap_of_isMultiHomog y hg, h0, map_zero, zero_mul]

  have heq : (funField P).map Φ = c.range := by
    apply le_antisymm
    · rw [Subring.map_le_iff_le_comap, funField, Subring.closure_le]
      rintro x ⟨u, v, a, hv, hu, hvf, rfl⟩
      have hvP : v ∉ P := fun h => nonZeroDivisors.ne_zero hv ((Ideal.Quotient.eq_zero_iff_mem).2 h)
      have hvy : aeval y v ≠ 0 := fun h => hvP (hmem hvf h)
      refine ⟨aeval y u / aeval y v, ?_⟩
      have h1 := congrArg Φ (IsLocalization.mk'_spec (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩)
      rw [map_mul, hform hvf, hform hu] at h1
      have hcv : c (aeval y v) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hvy
      rw [map_div₀, div_eq_iff hcv]
      exact mul_right_cancel₀ (hT a) (by rw [← h1]; ring)
    · rintro _ ⟨s, rfl⟩
      obtain ⟨d, g, h, hg, hh, hh0, hgs⟩ := hB s
      have hhP : h ∉ P := fun hP => by
        have : mConeMap y h = 0 := hP
        rw [LowerBoundFree.mConeMap_of_isMultiHomog y hh] at this
        exact mul_ne_zero ((map_ne_zero_iff _ (MvPolynomial.C_injective K Ω)).2 hh0)
          (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
      obtain ⟨x, hx⟩ := exists_funField_mul_eq hg hh hhP
      refine ⟨x, x.2, ?_⟩
      have h1 := congrArg Φ hx
      rw [map_mul, hform hh, hform hg, hgs, map_mul] at h1
      have hch : c (aeval y h) ≠ 0 := (map_ne_zero_iff _ c.injective).2 hh0
      exact mul_right_cancel₀ (mul_ne_zero hch (hT d)) (by rw [h1]; ring)

  have hc : Function.Injective c.rangeRestrict := fun a b h => c.injective (congrArg Subtype.val h)
  let e : funField P ≃+* Ω :=
    ((Subring.equivMapOfInjective (funField P) Φ Φ.injective).trans (RingEquiv.subringCongr heq)).trans
      (RingEquiv.ofBijective c.rangeRestrict ⟨hc, c.rangeRestrict_surjective⟩).symm
  exact @NumberField.of_ringEquiv _ _ hF.toField _ e hN

end

end GroundTheory.Heights₂.Heights.Targets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalIndex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem span_toAddSubgroup (y : (Σ k, ι k) → Ω) (x : Ω) :
    (Submodule.span (curveRing y) {x}).toAddSubgroup = curveMul y x := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton, curveMul, AddSubgroup.mem_map,
    AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, b.2, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, by rw [Subring.smul_def, smul_eq_mul, mul_comm]⟩


omit [∀ k, Fintype (ι k)] in
theorem genIndex_eq_card (y : (Σ k, ι k) → Ω) (a : K → ℤ) {x : Ω} (hx : x ∈ curveSectionMod y a) :
    genIndex (chartLat y a 1) (curveMul y x) = Nat.card (curveSectionQuot y a x) := by
  have hle : curveMul y x ≤ chartLat y a 1 := by
    rw [← span_toAddSubgroup]
    intro z hz
    exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) hz
  rw [genIndex, AddSubgroup.relIndex_eq_one.mpr hle, Nat.cast_one, div_one, ← span_toAddSubgroup]
  rfl

end CurveVerticalIndex

theorem CurveVertIndex.proof (hF : CurveSectionQuotFinite.Statement) (hV : CurveVertPointLength.Statement)
    (hR : CurveVertPointResidue.Statement) : CurveVertIndex.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  have := hF K ι Ω y s d hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV K ι Ω y s d hP hs hsP
  rw [CurveVerticalIndex.genIndex_eq_card y _ (HilbertSamuel.LiftBirationalAmple.chartLat_form hs),
    LogCardLength.proof (curveRing y) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)), vertR]
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal y) s,
          (locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W)) := by
        refine finsum_mem_congr rfl fun W hW => ?_
        rw [if_neg (IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full K ι _ s d hP hs hsP W hW), hmult W hW,
          ← hR K ι Ω y s d hP hs hsP W hW]
        congr 3
    _ = ∑ᶠ m ∈ {m : Ideal (curveRing y) |
          m.IsMaximal ∧ locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) ≠ 0},
          (locLen m (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) : ℝ) *
            Real.log (Nat.card (curveRing y ⧸ m)) :=
        finsum_mem_eq_of_bijOn _ hbij fun _ _ => rfl
    _ = _ := by
        refine finsum_mem_inter_support_eq _ _ {m : Ideal (curveRing y) | m.IsMaximal} ?_
        ext m
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support]
        exact ⟨fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h1, fun h0 => h2 (by simp [h0])⟩, h2⟩⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

