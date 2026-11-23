module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithRes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjective
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial ReciprocityTheory.AnForm.M Filter Topology MeasureTheory
open scoped ContDiff

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {P J : Ideal (MRing ι)} {e : ℕ}

def potOf (R : AnRes P J e) (L : HermLine ι) : LocPot R.X where
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  φ x y := Real.log (L.h (R.lift x y))

theorem contDiffOn_lift (R : AnRes P J e) (x : R.X) (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => R.lift x ((R.A.chart j).symm y))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) :=
  contDiffOn_pi.mpr fun p => ((R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem contDiffOn_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X)
    (j : Fin R.A.n) :
    ContDiffOn ℝ ∞ (fun y => Real.log (L.h (R.lift x ((R.A.chart j).symm y))))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
  have hmc : ∀ y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x,
      R.lift x ((R.A.chart j).symm y) ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    fun y hy => (R.mem x _ hy.2).1
  refine (hL.comp (contDiffOn_lift R x j) hmc).log fun y hy => ?_
  exact (L.pos _ (hmc y hy)).ne'

theorem smoothOn_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) (x : R.X) :
    R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) :=
  fun j => contDiffOn_potOf R hL x j

theorem continuousOn_lift (R : AnRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have hzt : R.A.chart j z ∈ (R.A.chart j).target := (R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => R.lift x z p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    (R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem isPotential_potOf (R : AnRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) := by
  classical
  refine ⟨smoothOn_potOf R hL, fun x x' y hy => ?_⟩
  have hy' : y ∈ R.U x ∩ R.U x' := hy
  choose p hp using (R.mem x' y hy'.2).1
  obtain ⟨c, hc, hcy⟩ := R.compat x x' y hy'
  have hnum : ∀ k, R.lift x y ⟨k, p k⟩ ≠ 0 := fun k => by
    rw [hcy]; exact mul_ne_zero (hc k) (hp k)
  have hr : ∀ k, R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩ ≠ 0 :=
    fun k => div_ne_zero (hnum k) (hp k)
  have hO : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')

  let q : K → R.X → ℂ := fun k z => R.lift x z ⟨k, p k⟩ / R.lift x' z ⟨k, p k⟩ /
    (R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩)
  let W : Set R.X := {z | z ∈ R.U x ∩ R.U x' ∧ ∀ k, R.lift x' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ∀ k, ContinuousAt (fun z => R.lift x z ⟨k, p k⟩) z := fun k =>
      ((continuousOn_lift R x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ∀ k, ContinuousAt (fun z => R.lift x' z ⟨k, p k⟩) z := fun k =>
      ((continuousOn_lift R x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
      eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
        (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
    exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
  have hyW : y ∈ W := by
    refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
    have : q k y = 1 := div_self (hr k)
    rw [this]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : R.X → ℂ := fun z => ∑ k, ((L.a k : ℝ) : ℂ) *
    (Complex.log (q k z) + ((Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ : ℝ) : ℂ))
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  ·
    have hz : (R.A.chart j).symm y' ∈ W := hy''.2
    have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((L.a k : ℝ) : ℂ) *
        (Complex.log (q k ((R.A.chart j).symm y'')) +
          ((Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
      intro k
      have hn : AnalyticAt ℂ (fun y'' => R.lift x ((R.A.chart j).symm y'') ⟨k, p k⟩) y' :=
        R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
      have hd : AnalyticAt ℂ (fun y'' => R.lift x' ((R.A.chart j).symm y'') ⟨k, p k⟩) y' :=
        R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
      have hq : AnalyticAt ℂ (fun y'' => q k ((R.A.chart j).symm y'')) y' :=
        (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
      have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((R.A.chart j).symm y'')) y' :=
        AnalyticAt.comp (f := fun y'' => q k ((R.A.chart j).symm y'')) (analyticAt_clog (hz.2 k).2) hq
      exact analyticAt_const.mul (hl.add analyticAt_const)
    exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
  ·
    have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := R.compat x x' z hzW.1
    have hpos : 0 < L.h (R.lift x' z) := L.pos _ (R.mem x' z hzW.1.2).1
    have hprod : (∏ k, ‖c' k‖ ^ L.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    have hterm : ∀ k, Real.log ‖q k z‖ +
        Real.log ‖R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
      intro k
      have hqz : q k z = c' k / (R.lift x y ⟨k, p k⟩ / R.lift x' y ⟨k, p k⟩) := by
        simp only [q]
        rw [hcz, mul_div_assoc, div_self (hzW.2 k).1, mul_one]
      rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k))
        (norm_ne_zero_iff.mpr (hr k))]
      ring
    show Real.log (L.h (R.lift x z)) - Real.log (L.h (R.lift x' z)) = (G z).re
    rw [hcz, L.smul c' _ hc', Real.log_mul hprod hpos.ne', add_sub_cancel_right,
      Real.log_prod fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))]
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
      Complex.ofReal_re]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k, Real.log_zpow]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjectiveVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP
open scoped ComplexConjugate ENNReal ContDiff

noncomputable section

variable {N : ℕ}

namespace ProjFS

lemma isOpen_chartVec_ne (i j : Fin (N + 1)) : IsOpen {z : Fin N → ℂ | chartVec i z j ≠ 0} :=
  isOpen_ne_fun (contDiff_chartVec_apply ℂ i j).continuous continuous_const

lemma transition_transition {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0) :
    transition j i (transition i j z) = z := by
  change chartCoord i (chartInv j (chartCoord j (chartInv i z))) = z
  rw [chartInv_chartCoord j (show chartInv i z ∈ chartDomain j from hz), chartCoord_chartInv]

lemma chartVec_transition_apply {i j : Fin (N + 1)} {z : Fin N → ℂ} (hz : chartVec i z j ≠ 0)
    (m : Fin (N + 1)) : chartVec j (transition i j z) m = (chartVec i z j)⁻¹ * chartVec i z m := by
  rw [chartVec_transition i j hz]; rfl

lemma image_transition (j : Fin (N + 1)) :
    transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} = {y | chartVec j y 0 ≠ 0} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change chartVec j (transition 0 j z) 0 ≠ 0
    rw [chartVec_transition_apply hz, chartVec_self, mul_one]
    exact inv_ne_zero hz
  · intro hy
    refine ⟨transition j 0 y, ?_, transition_transition hy⟩
    change chartVec 0 (transition j 0 y) j ≠ 0
    rw [chartVec_transition_apply hy, chartVec_self, mul_one]
    exact inv_ne_zero hy

lemma injOn_transition (i j : Fin (N + 1)) :
    Set.InjOn (transition i j) {z : Fin N → ℂ | chartVec i z j ≠ 0} := fun z hz z' hz' h => by
  rw [← transition_transition hz, h, transition_transition hz']

lemma ae_chartVec_ne (j : Fin (N + 1)) : ∀ᵐ y : Fin N → ℂ, chartVec j y 0 ≠ 0 := by
  obtain h | ⟨k, hk⟩ := Fin.eq_self_or_eq_succAbove j 0
  · exact Filter.Eventually.of_forall fun y => by rw [h, chartVec_self]; exact one_ne_zero
  · rw [ae_iff]
    have hset : {y : Fin N → ℂ | ¬ chartVec j y 0 ≠ 0} = Function.eval k ⁻¹' {0} := by
      ext y
      simp only [ne_eq, not_not, mem_setOf_eq, mem_preimage, Function.eval, mem_singleton_iff]
      rw [hk, chartVec_succAbove]
    rw [hset, volume_pi]
    exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

theorem setLIntegral_fsMeasure_chartDomain (j : Fin (N + 1)) (g : CP N → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y) := by
  have hD : MeasurableSet (chartDomain (N := N) j) := (isOpen_chartDomain j).measurableSet
  rw [fsMeasure, setLIntegral_map hD hg (measurable_chartInv 0), fsChartMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_fsVolumeDensity 0).ennreal_ofReal
      (show Measurable (fun x => g (chartInv 0 x)) from hg.comp (measurable_chartInv 0))
      (hD.preimage (measurable_chartInv 0))]
  have hW : chartInv 0 ⁻¹' chartDomain j = {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := rfl
  rw [hW]
  have hae : (Set.univ : Set (Fin N → ℂ)) =ᵐ[volume]
      transition 0 j '' {z : Fin N → ℂ | chartVec 0 z j ≠ 0} := by
    rw [image_transition]
    filter_upwards [ae_chartVec_ne j] with y hy
    exact ⟨fun _ => hy, fun _ => trivial⟩
  conv_rhs => rw [← setLIntegral_univ]
  rw [setLIntegral_congr hae,
    lintegral_image_eq_lintegral_normSq_det_mul (transition 0 j) _ (isOpen_chartVec_ne 0 j)
      (fun z hz => analyticAt_transition 0 j hz) (injOn_transition 0 j)]
  refine setLIntegral_congr_fun (isOpen_chartVec_ne 0 j).measurableSet fun z hz => ?_
  have h1 : chartInv j (transition 0 j z) = chartInv 0 z :=
    chartInv_chartCoord j (show chartInv 0 z ∈ chartDomain j from hz)
  have h2 : fsVolumeDensity 0 z =
      Complex.normSq (jacC (transition 0 j) z).det * fsVolumeDensity j (transition 0 j z) := by
    rw [fsVolumeDensity_transition 0 j hz,
      det_fderiv_real_eq_normSq _ z (differentiableAt_transition 0 j hz),
      abs_of_nonneg (Complex.normSq_nonneg _)]
  simp only [Pi.mul_apply]
  rw [h1, h2, ENNReal.ofReal_mul (Complex.normSq_nonneg _)]
  ring

end ProjFS

def fsVolume (N : ℕ) : SmoothVolume (projAtlas N) where
  μ := fsMeasure N
  isProb := inferInstance
  dens := fsVolumeDensity
  smooth (j : Fin (N + 1)) := by
    have h : fsVolumeDensity (N := N) j =
        fun z => (N.factorial : ℝ) / (Real.pi ^ N * (1 + normSqSum z) ^ (N + 1)) :=
      funext fun z => fsVolumeDensity_eq j z
    rw [h]
    have hs : ContDiff ℝ ∞ (normSqSum (N := N)) := by
      unfold normSqSum; exact contDiff_normSqSum
    refine (contDiff_const.div (contDiff_const.mul ((contDiff_const.add hs).pow _))
      fun z => ?_).contDiffOn
    have := one_add_normSqSum_pos z
    have := Real.pi_pos
    positivity
  pos (j : Fin (N + 1)) y _ := fsVolumeDensity_pos j y
  chart_lintegral (j : Fin (N + 1)) g hg := by
    change ∫⁻ x in chartDomain j, g x ∂fsMeasure N =
      ∫⁻ y in univ, g (chartInv j y) * ENNReal.ofReal (fsVolumeDensity j y)
    rw [setLIntegral_univ]
    exact ProjFS.setLIntegral_fsMeasure_chartDomain j g hg

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace MultiDegreePositive

theorem tendsto_diag (K : Type) [Fintype K] :
    Filter.Tendsto (fun n : ℤ => fun _ : K => n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨∑ k, |b k|, fun a ha k => ?_⟩
  exact (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ k)).trans ha)

theorem mixedDiff_succ {L : Type} [DecidableEq L] (b : L → ℤ) (H : (L → ℤ) → ℤ) (r : ℕ) :
    mixedDiff (fun _ : Fin (r + 1) => b) H = diffStep b (mixedDiff (fun _ : Fin r => b) H) := by
  simp only [mixedDiff, List.ofFn_succ, List.foldr_cons]

theorem mixedDiff_diag {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by
  induction r generalizing n with
  | zero => simpa [mixedDiff] using hg n
  | succ r ih =>
    rw [mixedDiff_succ, mixedDiff_succ]
    have e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1 :=
      fun L => funext fun _ => rfl
    simp only [diffStep, e1, ih]

theorem pos_of_isEmpty {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] [IsEmpty K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ) (hq : IsMultiProjPrime q)
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ)) := by
  have hle := (ringKrullDim_quotient_le q).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ k, ι k))
  rw [hd, ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard,
    Nat.card_of_isEmpty, Fintype.card_eq_zero,
    add_zero] at hle
  have he : e = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hle) : (e : ℕ∞) = 0)
  subst he
  have hrel : FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (0 + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  obtain ⟨hA, -⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant 0 hrel
  obtain ⟨m, hm⟩ := (hA (fun _ : Fin 0 => fun _ : K => (1 : ℤ))).exists
  rw [← hm]
  have hm0 : mixedDiff (fun _ : Fin 0 => fun _ : K => (1 : ℤ)) (hilbFn q) m = hilbFn q m := rfl
  rw [hm0]
  obtain ⟨hfin, hval⟩ := FieldNumbers.GradedFinite.full F K ι q (fun _ => 0)
  have hmm : m = fun k => ((fun _ : K => (0 : ℕ)) k : ℤ) := funext fun k => isEmptyElim k
  rw [hmm, hval]
  have hne : (⟨Ideal.Quotient.mkₐ F q 1, Submodule.mem_map_of_mem
      (mem_weightedHomogeneousSubmodule F _ _ _ |>.mpr (isWeightedHomogeneous_one F _))⟩ :
        gradedPiece q (fun _ : K => 0)) ≠ 0 := by
    intro h0
    have h1 := congrArg Subtype.val h0
    simp only [Submodule.coe_zero, map_one] at h1
    exact hq.isPrime.ne_top (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1) |>
      (Ideal.eq_top_iff_one q).mpr)
  exact_mod_cast Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end MultiDegreePositive

theorem MultiDegreePositive.proof (hPrime : SegrePrime.Statement) (hHilb : SegreHilb.Statement)
    (hDim : SegreDimGe.Statement) : MultiDegreePositive.Statement := by
  intro F _ K _ _ ι _ q e hq hd
  rcases isEmpty_or_nonempty K with hK | hK
  · exact MultiDegreePositive.pos_of_isEmpty q e hq hd

  have hq' := hPrime F K ι q hq
  have hge := hDim F K ι q e hq hd
  have hle := (ringKrullDim_quotient_le (segrePrime F q)).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F)
      (ι := Σ _ : Unit, ∀ k, ι k))
  rw [ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard] at hle

  obtain ⟨D, hD, heD⟩ : ∃ D : ℕ, ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸
      segrePrime F q) = ((D + 1 : ℕ) : WithBot ℕ∞) ∧ e ≤ D := by
    generalize ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = x at hge hle ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hge (by simp)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((Nat.card (Σ _ : Unit, ∀ k, ι k) : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (not_le.mpr (ENat.natCast_lt_top _))
      | coe m =>
        have hm : e + 1 ≤ m := by exact_mod_cast hge
        exact ⟨m - 1, by rw [Nat.sub_add_cancel (by omega)]; rfl, by omega⟩
  have hrel : FieldNumbers.relDim q = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (e + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  have hrel' : FieldNumbers.relDim (segrePrime F q) = ((D : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq (segrePrime F q) (D + 1) hD]
    simp only [Fintype.card_unit, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  obtain ⟨hA, hB⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant e hrel
  obtain ⟨hA', -⟩ := FieldNumbers.MixedDiffConst.full F Unit (fun _ => ∀ k, ι k) (segrePrime F q)
    hq'.multiHomog hq'.relevant D hrel'
  have hpos := DegreePositive.proof F (∀ k, ι k) (segrePrime F q) D hq' hD
  have hdiag := MultiDegreePositive.mixedDiff_diag (hilbFn q) (hilbFn (segrePrime F q))
    (fun n => hHilb F K ι q n)
  have hA'd := (MultiDegreePositive.tendsto_diag Unit).eventually
    (hA' (fun _ : Fin D => fun _ : Unit => (1 : ℤ)))

  have hDe : D = e := by
    by_contra hne
    have hBd := (MultiDegreePositive.tendsto_diag K).eventually
      (hB D (by omega) (fun _ : Fin D => fun _ : K => (1 : ℤ)))
    obtain ⟨n, h1, h2⟩ := (hA'd.and hBd).exists
    rw [hdiag] at h1
    omega
  subst hDe
  have hAd := (MultiDegreePositive.tendsto_diag K).eventually
    (hA (fun _ : Fin D => fun _ : K => (1 : ℤ)))
  obtain ⟨n, h1, h2⟩ := (hA'd.and hAd).exists
  rw [hdiag] at h1
  omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace SemiampleNefAlt

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem charOf_prime {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} [W.IsPrime]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.charOf W ≠ 0) : (ReciprocityTheory.ChartRestriction.G.Geo.charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) ≠ 0 := by
    intro h0
    apply h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.charOf
    rw [h0]
    rfl
  rw [← Submodule.IsPrincipal.span_singleton_generator
    (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι))] at hI
  exact Int.prime_iff_natAbs_prime.mp ((Ideal.span_singleton_prime hg).mp hI)


end SemiampleNefAlt


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

