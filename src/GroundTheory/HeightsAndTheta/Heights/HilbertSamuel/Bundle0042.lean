module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmoothChartVolume
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanSectionPairing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace SectionPairing

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

def pairing (W : Weight L) (n : ℕ) (s t : Fin A.n → X → ℂ) (x : X) : ℂ :=
  conj (s (chartIdx A x) x) * t (chartIdx A x) x *
    ((Real.exp (-(n : ℝ) * W.φ (chartIdx A x) x) : ℝ) : ℂ)

theorem mem_chartIdx (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

theorem pairing_eq (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (ht : t ∈ L.sections n) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    pairing W n s t x = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
  have hi := mem_chartIdx (A := A) x
  set i := chartIdx A x
  have hix : x ∈ (A.chart i).source ∩ (A.chart j).source := ⟨hi, hx⟩
  have hg := L.ne_zero i j x hix
  have ha : (0 : ℝ) < ‖L.g i j x‖ ^ 2 := pow_pos (norm_pos_iff.2 hg) 2
  have hexp : Real.exp (-(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2))) =
      Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n := by
    rw [show -(n : ℝ) * (W.φ j x + Real.log (‖L.g i j x‖ ^ 2)) =
        -(n : ℝ) * W.φ j x - n * Real.log (‖L.g i j x‖ ^ 2) by ring, Real.exp_sub,
      Real.exp_nat_mul, Real.exp_log ha]
  have hc : conj (L.g i j x ^ n) * L.g i j x ^ n = (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.conj_mul']
    push_cast
    ring
  have hne : (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos ha n).ne'
  rw [pairing, hs.2.1 i j x hix, ht.2.1 i j x hix, W.compat i j x hix, hexp]
  calc conj (L.g i j x ^ n * s j x) * (L.g i j x ^ n * t j x) *
        ((Real.exp (-(n : ℝ) * W.φ j x) / (‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ)
      = (conj (L.g i j x ^ n) * L.g i j x ^ n) *
          (conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ)) /
          (((‖L.g i j x‖ ^ 2) ^ n : ℝ) : ℂ) := by
        rw [map_mul, Complex.ofReal_div]
        ring
    _ = conj (s j x) * t j x * ((Real.exp (-(n : ℝ) * W.φ j x) : ℝ) : ℂ) := by
        rw [hc]
        field_simp

theorem pairing_self (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    pairing W n s s x = ((ptNormSq W n s x : ℝ) : ℂ) := by
  rw [pairing, ptNormSq, Complex.conj_mul']
  push_cast
  ring

theorem continuousAt_of_chart {β : Type*} [TopologicalSpace β] {f : X → β} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source))
    {x : X} (hx : x ∈ (A.chart j).source) : ContinuousAt f x := by
  have hy : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hx⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source) :=
    (A.chart j).isOpen_inter_preimage_symm (A.chart j).open_source
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    (hf.continuousAt (hopen.mem_nhds hy)).comp ((A.chart j).continuousAt hx)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  simp [(A.chart j).left_inv hy]

theorem pairing_continuous (W : Weight L) (n : ℕ) {s t : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) (ht : t ∈ L.sections n) : Continuous (pairing W n s t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  have h1 : ContinuousAt (s j) x := continuousAt_of_chart j (hs.1 j j).continuousOn hx
  have h2 : ContinuousAt (t j) x := continuousAt_of_chart j (ht.1 j j).continuousOn hx
  have h3 : ContinuousAt (W.φ j) x := continuousAt_of_chart j (W.smooth j j).continuousOn hx
  have h : ContinuousAt
      (fun y ↦ conj (s j y) * t j y * ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x := by
    have h4 : ContinuousAt (fun y ↦ ((Real.exp (-(n : ℝ) * W.φ j y) : ℝ) : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul h3))
    exact ((Complex.continuous_conj.continuousAt.comp h1).mul h2).mul h4
  refine h.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hx] with y hy
  exact (pairing_eq W n hs ht j hy).symm

theorem ptNormSq_continuous (W : Weight L) (n : ℕ) {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  have h := Complex.continuous_re.comp (pairing_continuous W n hs hs)
  refine h.congr fun x ↦ ?_
  simp [pairing_self]

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq
  positivity

variable [MeasurableSpace X] [BorelSpace X]

theorem isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 ↦ ?_⟩
  obtain ⟨x, hxU⟩ := hne
  have hx := mem_chartIdx (A := A) x
  set j := chartIdx A x
  set T := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U
  have hTo : IsOpen T := (A.chart j).isOpen_inter_preimage_symm hU
  have hTx : A.chart j x ∈ T :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hlin := dV.chart_lintegral j (U.indicator 1) (measurable_one.indicator hU.measurableSet)
  have hleft : ∫⁻ x in (A.chart j).source, U.indicator 1 x ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left h0
  have hT : ∫⁻ y in T, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ y in T, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in T, U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          setLIntegral_congr_fun hTo.measurableSet fun y hy ↦ by
            rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target,
            U.indicator 1 ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) :=
          lintegral_mono_set inter_subset_left
      _ = 0 := by rw [← hlin, hleft]
  have hmeas : AEMeasurable (fun y ↦ ENNReal.ofReal (dV.dens j y)) (volume.restrict T) :=
    (((dV.smooth j).continuousOn.mono inter_subset_left).aemeasurable
      hTo.measurableSet).ennreal_ofReal
  have hae := (lintegral_eq_zero_iff' hmeas).1 hT
  rw [Filter.EventuallyEq, ae_restrict_iff' hTo.measurableSet] at hae
  have hzero : volume T = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyT
    have := hy hyT
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at this
    exact absurd (dV.pos j y hyT.1) (not_lt.2 this)
  exact (hTo.measure_pos volume ⟨_, hTx⟩).ne' hzero

end SectionPairing

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CoeffLeOfEvalLeMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

namespace ArithmeticVolumeDegreeZero

theorem arithmeticVolume_nonneg {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) :
    0 ≤ arVolP P La a D := by
  unfold arVolP
  have hu : ∀ k : ℕ, 0 ≤ smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
    fun k => div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
  · exact le_limsup_of_frequently_le (Frequently.of_forall hu) hb
  · rw [Real.limsup_of_not_isBoundedUnder hb]

theorem charZero_of_horizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem coeff_le_of_eval_le_mul {D : ℕ} (p r : Polynomial ℝ) {C : ℝ} (hC : 0 ≤ C) (hp : p.natDegree ≤ D + 1)
    (hr : r.natDegree ≤ D) (hrD : r.coeff D ≤ 0)
    (h : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ)) : p.coeff (D + 1) ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set g : Polynomial ℝ := p - Polynomial.C C * ((Polynomial.X + 1) * r) with hg
  have hr1 : r.coeff (D + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hgc : g.coeff (D + 1) = p.coeff (D + 1) - C * r.coeff D := by
    rw [hg, Polynomial.coeff_sub, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, hr1, add_zero]
  have hgpos : 0 < g.coeff (D + 1) := by
    rw [hgc]; nlinarith
  have hgdeg : g.natDegree ≤ D + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hp ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      simp
    omega
  have hgnat : g.natDegree = D + 1 :=
    le_antisymm hgdeg (Polynomial.le_natDegree_of_ne_zero hgpos.ne')
  have hlead : 0 ≤ g.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hgnat]; exact hgpos.le
  have hdeg : 0 < g.degree := by
    rw [Polynomial.degree_eq_natDegree (fun h0 => by simp [h0] at hgpos), hgnat]
    exact_mod_cast Nat.succ_pos D
  have ht := (g.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead).comp tendsto_natCast_atTop_atTop
  obtain ⟨q, hq1, hq⟩ := ((eventually_ge_atTop 1).and (ht.eventually (eventually_gt_atTop 0))).exists
  have hev : g.eval (q : ℝ) = p.eval (q : ℝ) - C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    simp only [hg, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    ring
  have := h q hq1
  simp only [Function.comp_apply] at hq
  linarith

end ArithmeticVolumeDegreeZero

theorem ArithmeticVolumeDegreeZero.proof (hB : G6.StatementB) (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement)
    (hI : ShiftIntersectionPolynomial.Statement) (hG : ShiftDegreePolynomial.Statement) :
    ArithmeticVolumeDegreeZero.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc hdeg
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  refine le_trans ?_ (ArithmeticVolumeDegreeZero.arithmeticVolume_nonneg _ _ _ _)
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ArithmeticVolumeBigDimensionOne.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) 1 → Birational y →
    P0 ≤ mCoordIdeal y → ReciprocityTheory.ChartRestriction.G.Geo.IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) 1 (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 0

namespace ArithmeticVolumeBigDimensionOne

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end ArithmeticVolumeBigDimensionOne

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem AmpleOfGenTwist.proof (hGen : GenTwistGenerated.Statement) (hVan : GenTwistVanish.Statement) :
    AmpleOfGenTwist.Statement := by
  intro S _ K _ _ ι _ _ V α p q hV hα hp
  refine ⟨1, le_rfl, ?_, fun e => ?_⟩
  · rw [one_smul]
    exact hGen S K ι V α q p hα
  · obtain ⟨c₀, hc₀⟩ := hVan S K ι V α hV hα e
    refine ⟨c₀, fun c hc => ?_⟩
    have hN : e + (c * 1) • ((q : ℤ) • α + fun _ => (p : ℤ)) =
        e + ((c * q : ℕ) : ℤ) • α + fun _ => ((c * p : ℕ) : ℤ) := by
      funext k
      change e k + (c * 1) • ((q : ℤ) • α k + (p : ℤ)) = e k + ((c * q : ℕ) : ℤ) • α k + ((c * p : ℕ) : ℤ)
      simp only [nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
    rw [hN]
    exact hc₀ (c * q) (c * p) (le_trans hc (Nat.le_mul_of_pos_right c hp))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

theorem BlockResolutionDegree.proof (hRank : BlockSectionsRank.Statement)
    (hInt : BlockResolutionDegreeIntegral.Statement) : BlockResolutionDegree.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h₀ h₁ s₀ s₁ t ht
  obtain ⟨C, hC⟩ := hRank D K ι Ω d.y d.k₀ d.one_le d.arith d.birat
  refine ⟨C, fun n => ?_⟩
  rw [hInt D K ι Ω d A₀ A₁ h₀ h₁ s₀ s₁ t ht]
  exact hC n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem ResVolume.proof : ResVolume.Statement := by
  intro K _ ι _ P J e R _ _ hP
  obtain ⟨z, hzP, hzJ⟩ := exists_mcPts_not_mem_mcPts hP R.nondeg
  obtain ⟨x, -⟩ := R.surj z hzP hzJ
  have : Nonempty R.X := ⟨x⟩
  exact ChartVolume.exists_isSmoothVolume R.A

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

