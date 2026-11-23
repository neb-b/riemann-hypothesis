module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyGluedSectionLe
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.GlueEnergy

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] {A : WeightedAtlas n Y ι La}

theorem exists_bound (C : Cover A) : ∃ B : ℝ, 0 ≤ B ∧ ∀ a b j, ∀ v ∈ ball (C.c b) (C.r b),
    ‖wdb n j (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ)) v‖ ≤ B := by
  have h : ∀ p : Fin C.m × Fin C.m × Fin n, ∃ B : ℝ, ∀ v ∈ closedBall (C.c p.2.1) (C.r p.2.1),
      ‖wdb n p.2.2 (fun x => (C.chi p.1 ((A.chart (C.idx p.2.1)).symm x) : ℂ)) v‖ ≤ B := by
    rintro ⟨a, b, j⟩
    apply (isCompact_closedBall _ _).exists_bound_of_continuousOn
    refine ContinuousOn.mono ?_ (C.sub b)
    have h1 : ContDiffOn ℝ ∞ (fun x => (C.chi a ((A.chart (C.idx b)).symm x) : ℂ))
        (A.chart (C.idx b)).target :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (C.smooth a (C.idx b))
    have h2 := h1.continuousOn_fderiv_of_isOpen (A.chart (C.idx b)).open_target (by simp)
    unfold wdb
    exact ((h2.clm_apply continuousOn_const).add
      (continuousOn_const.mul (h2.clm_apply continuousOn_const))).div_const _
  choose B hB using h
  refine ⟨∑ p, |B p|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun a b j v hv => ?_⟩
  exact ((hB (a, b, j) v (ball_subset_closedBall hv)).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun p => |B p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _))

theorem wdb_eq_zero (C : Cover A) (a : Fin C.m) (i : ι) (j : Fin n) (v : V n)
    (hv : v ∈ (A.chart i).target)
    (h : (A.chart i).symm v ∉
      (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :
    wdb n j (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) v = 0 := by
  have h1 : (A.chart i).symm v ∉ tsupport (C.chi a) := fun h' => h (C.supp a h')
  have h2 := notMem_tsupport_iff_eventuallyEq.mp h1
  have h3 := ((A.chart i).continuousAt_symm hv).eventually h2
  have h4 : (fun x => (C.chi a ((A.chart i).symm x) : ℂ)) =ᶠ[𝓝 v] fun _ => 0 :=
    h3.mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
  unfold wdb
  rw [h4.fderiv_eq]
  simp

theorem sq_sum_le {m : ℕ} (x d : Fin m → ℂ) (B : ℝ) (e : Fin m → ℝ)
    (h : ∀ a, ‖x a * d a‖ ^ 2 ≤ B ^ 2 * e a) :
    ‖∑ a, x a * d a‖ ^ 2 ≤ m * B ^ 2 * ∑ a, e a := by
  calc ‖∑ a, x a * d a‖ ^ 2 ≤ (∑ a, ‖x a * d a‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ m * ∑ a, ‖x a * d a‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖x a * d a‖)
    _ ≤ m * ∑ a, B ^ 2 * e a := by gcongr with a; exact h a
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem energy_glue_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K : ℝ, 0 ≤ K ∧ ∀ (la : La) (F0 : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), A.IsSSec (A.kap + la) F0 → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → n1 C la (glue C la u) ≤ ENNReal.ofReal K * ∑ a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
  intro n Y _ _ _ _ _ ι La _ A C
  obtain ⟨B, hB0, hB⟩ := exists_bound C
  refine ⟨C.m * (n * (C.m * B ^ 2)), by positivity, fun la F0 u hF hu => ?_⟩
  set D : Fin C.m → ι → Y → ℂ := fun a i y =>
    A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y) - F0 i y with hD
  set U : Fin C.m → Set Y := fun a =>
    (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) with hU
  have hUo : ∀ a, IsOpen (U a) := fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hbt : ∀ b, ball (C.c b) (C.r b) ⊆ (A.chart (C.idx b)).target := fun b =>
    ball_subset_closedBall.trans (C.sub b)
  set W : Fin C.m → Fin C.m → Set (V n) := fun b a =>
    ball (C.c b) (C.r b) ∩ ((A.chart (C.idx b)).target ∩ (A.chart (C.idx b)).symm ⁻¹' U a) with hW
  have hWo : ∀ b a, IsOpen (W b a) := fun b a =>
    isOpen_ball.inter ((A.chart (C.idx b)).isOpen_inter_preimage_symm (hUo a))
  have hDc : ∀ b a, ContinuousOn (D a (C.idx b) ∘ (A.chart (C.idx b)).symm) (W b a) := by
    intro b a
    have hov : W b a ⊆ ovl A.chart (C.idx b) (C.idx a) := fun v hv => ⟨hv.2.1, hv.2.2.1⟩
    have h1 := (A.holo_g (A.kap + la) (C.idx b) (C.idx a)).continuousOn.mono hov
    have h2 := (A.holo_trans (C.idx b) (C.idx a)).continuousOn.mono hov
    have h3 := (hu a).continuousOn.comp h2 (fun v hv => hv.2.2.2)
    have h4 := (hF.1 (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact (h1.mul h3).sub h4
  have hcomp : ∀ a i y, y ∈ (A.chart i).source → y ∈ (A.chart (C.idx a)).source →
      D a (A.pick y) y = A.g (A.kap + la) (A.pick y) i y * D a i y := by
    intro a i y hi ha
    simp only [hD]
    rw [A.g_cocycle _ (A.pick y) i (C.idx a) y (A.mem_pick y) hi ha,
      hF.2 (A.pick y) i y (A.mem_pick y) hi]
    ring
  set f : Fin C.m → Fin C.m → V n → ℝ≥0∞ := fun b a v => ENNReal.ofReal
    (‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2 *
      Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) with hf
  have hk : ∀ b a, ∫⁻ y in (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' W b a,
      ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu = ∫⁻ v in W b a, f b a v := by
    intro b a
    refine _root_.GlobalTheory.OTY.lintegral_nsq_chart_part n Y ι La A la (C.idx b) (W b a) (D a) (hWo b a).measurableSet
      (fun v hv => hv.2.1) (fun y hy hy' => hcomp a _ y hy ?_)
      ((hDc b a).aemeasurable (hWo b a).measurableSet)
    have := hy'.2.2.1
    rwa [(A.chart (C.idx b)).left_inv hy] at this
  have hWaa : ∀ a, W a a = ball (C.c a) (C.r a) := by
    intro a
    refine Set.inter_eq_left.mpr fun v hv => ⟨hbt a hv, (A.chart _).map_target (hbt a hv), ?_⟩
    show A.chart (C.idx a) ((A.chart (C.idx a)).symm v) ∈ ball (C.c a) (C.r a)
    rwa [(A.chart (C.idx a)).right_inv (hbt a hv)]
  have hE : ∀ b a, ∫⁻ v in W b a, f b a v ≤ ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
    intro b a
    calc _ = _ := (hk b a).symm
      _ ≤ ∫⁻ y in (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' W a a,
          ENNReal.ofReal (A.nsq (A.kap + la) (D a) y) ∂A.mu := by
        apply lintegral_mono_set
        intro y hy
        rw [hWaa]
        have := hy.2.2.2
        rwa [Set.mem_preimage, (A.chart (C.idx b)).left_inv hy.1] at this
      _ = _ := hk a a
      _ = _ := by
        rw [hWaa]
        refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
        have hs := (A.chart (C.idx a)).map_target (hbt a hv)
        have h1 : A.g (A.kap + la) (C.idx a) (C.idx a) ((A.chart (C.idx a)).symm v) = 1 := by
          have h2 := A.g_cocycle (A.kap + la) _ _ _ _ hs hs hs
          have h3 := A.g_ne (A.kap + la) _ _ _ hs hs
          exact (mul_right_eq_self₀.mp h2.symm).resolve_right h3
        simp only [hf, hD]
        rw [h1, one_mul, (A.chart (C.idx a)).right_inv (hbt a hv), norm_sub_rev]
  have hfm : ∀ b a, AEMeasurable ((W b a).indicator (f b a))
      (volume.restrict (ball (C.c b) (C.r b))) := by
    intro b a
    refine AEMeasurable.restrict ?_
    rw [aemeasurable_indicator_iff (hWo b a).measurableSet]
    refine ContinuousOn.aemeasurable ?_ (hWo b a).measurableSet
    have h4 := (A.smooth_ph la (C.idx b)).continuousOn.mono (t := W b a) (fun v hv => hv.2.1)
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hDc b a).norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h4.neg))
  have hpt : ∀ b, ∀ v ∈ ball (C.c b) (C.r b), ENNReal.ofReal
      ((∑ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) ≤
      ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a, (W b a).indicator (f b a) v := by
    intro b v hv
    set e : Fin C.m → ℝ := fun a => (W b a).indicator
      (fun v => ‖D a (C.idx b) ((A.chart (C.idx b)).symm v)‖ ^ 2) v with he
    have he0 : ∀ a, 0 ≤ e a := fun a => Set.indicator_nonneg (fun _ _ => by positivity) _
    have h1 : ∀ j, ‖wdb n j (glue C la u (C.idx b) ∘ (A.chart (C.idx b)).symm) v‖ ^ 2 ≤
        C.m * B ^ 2 * ∑ a, e a := by
      intro j
      rw [_root_.GlobalTheory.glue_wdb_eq n Y ι La A C la u (C.idx b) v (F0 (C.idx b) ((A.chart (C.idx b)).symm v))
        j hu (hbt b hv)]
      apply sq_sum_le
      intro a
      by_cases hm : v ∈ W b a
      · simp only [he, Set.indicator_of_mem hm, hD]
        rw [norm_mul, mul_pow]
        gcongr
        exact hB a b j v hv
      · rw [wdb_eq_zero C a (C.idx b) j v (hbt b hv) (fun h => hm ⟨hv, hbt b hv, h⟩)]
        simp only [zero_mul, norm_zero]
        have := he0 a
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    have h2 : ∑ a, (W b a).indicator (f b a) v = ENNReal.ofReal ((∑ a, e a) *
        Real.exp (-A.ph la (C.idx b) ((A.chart (C.idx b)).symm v))) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg
        (fun a _ => mul_nonneg (he0 a) (Real.exp_pos _).le)]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hm : v ∈ W b a
      · simp only [he, hf, Set.indicator_of_mem hm]
      · simp [he, Set.indicator_of_notMem hm]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    apply ENNReal.ofReal_le_ofReal
    gcongr
    calc _ ≤ ∑ _j : Fin n, C.m * B ^ 2 * ∑ a, e a := Finset.sum_le_sum fun j _ => h1 j
      _ = _ := by simp [mul_assoc]
  unfold n1
  calc _ ≤ ∑ _b : Fin C.m, ENNReal.ofReal (n * (C.m * B ^ 2)) * ∑ a,
        ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
        (‖F0 (C.idx a) ((A.chart (C.idx a)).symm v) - u a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
        refine Finset.sum_le_sum fun b _ => ?_
        refine (setLIntegral_mono' measurableSet_ball (hpt b)).trans ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ (fun a _ => hfm b a)]
        refine mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _
        refine le_trans (setLIntegral_le_lintegral _ _) ?_
        rw [lintegral_indicator (hWo b a).measurableSet]
        exact hE b a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (C.m : ℝ)) (by positivity), ENNReal.ofReal_natCast, mul_assoc]

end GlobalTheory.OTY.GlueEnergy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetUnitaryChartSectionConjugatedMatrix
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem det_secM_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → ∀ {w : V (nd X)}, cpt X x w ∈ X.dom → ∀ τ : X.Ψ, (secM X x w τ).det = 1 := by
  intro E _ _ _ r X x hx w hw τ
  have hG := FrameDegreeData.ortho_bOf X hw τ
  rw [bOf_cpt X hx w] at hG
  have hm : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [hm, FrameDegreeData.gram_mul, hx τ] at hG
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
  have hc : ((yM X w τ).map (starRingEnd ℂ)).det = starRingEnd ℂ (yM X w τ).det :=
    (RingHom.map_det (starRingEnd ℂ) (yM X w τ)).symm
  rw [hc] at hd
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast PoinPf.sgn_ne _ _
  have hY : (yM X w τ).det = ((∏ k, gsS X w τ k : ℝ) : ℂ) := by
    rw [yM, Matrix.det_mul, gsB, Matrix.det_mul, Matrix.det_diagonal]
    rw [Matrix.det_of_lowerTriangular _ (fun a b hab => ?_)]
    · rw [gsU, Matrix.det_of_upperTriangular (FrameDegreeData.uMat_upper _)]
      simp only [FrameDegreeData.uMat_diag, Finset.prod_const_one, one_mul]
      have : ∀ i, mat (nmat X w) τ i i = 1 := fun i => by
        simp [mat, nmat]
      simp only [this, Finset.prod_const_one, one_mul]
      push_cast; rfl
    · show nmat X w τ a b = 0
      simp only [nmat]
      have hab' : a < b := hab
      have h1 : ¬ b < a := not_lt.2 (le_of_lt hab')
      rw [dite_eq_right h1, if_neg (ne_of_lt hab')]
  set t : ℝ := ∏ k, gsS X w τ k with ht
  have hpos : 0 ≤ t := Finset.prod_nonneg fun k _ => inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [hY, Complex.conj_ofReal] at hd
  have htt : ((t * t : ℝ) : ℂ) = 1 := by
    have h2 : (t : ℂ) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det * (t : ℂ) =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [hd, one_mul]
    push_cast
    have h3 : ((t : ℂ) * t) * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det =
      1 * (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)).det := by rw [← h2]; ring
    exact mul_right_cancel₀ hJ h3
  have htt' : t * t = 1 := by exact_mod_cast htt
  have ht1 : t = 1 := by nlinarith
  rw [secM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))) (yM X w τ), hY, ht1, Complex.ofReal_one]

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorsOfConstantsFlatNormalStageAtOrigin
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.GoodStageOrigin

theorem local_props (A' : Type) [CommRing A'] [IsDomain A'] [IsNoetherianRing A'] [IsIntegrallyClosed A']
    (E : Type) [CommRing E] [Algebra (Polynomial A') E] [Algebra.Etale (Polynomial A') E]
    (Q : Ideal E) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) ∧
      IsIntegrallyClosed (Localization.AtPrime Q) ∧
      (letI : Algebra A' (Localization.AtPrime Q) :=
        ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
       Module.Flat A' (Localization.AtPrime Q)) := by
  haveI : IsIntegrallyClosed (Polynomial A') := by
    haveI := GlobalTheory.isIntegrallyClosed_mvPolynomial_fin A' 1
    exact IsIntegrallyClosed.of_equiv
      (MvPolynomial.uniqueAlgEquiv A' (Fin 1)).toRingEquiv
  obtain ⟨h1, h2⟩ := GlobalTheory.etale_localization_atPrime_isDomain_isIntegrallyClosed (Polynomial A') E Q
  haveI : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing (Polynomial A') E
  refine ⟨h1, IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance, h2, ?_⟩
  letI : Algebra A' (Localization.AtPrime Q) :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q)).comp Polynomial.C).toAlgebra
  haveI : IsScalarTower A' (Polynomial A') (Localization.AtPrime Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat (Polynomial A') E := inferInstance
  haveI : Module.Flat E (Localization.AtPrime Q) := IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat (Polynomial A') (Localization.AtPrime Q) := Module.Flat.trans (Polynomial A') E _
  exact Module.Flat.trans A' (Polynomial A') _

theorem good_stage : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP A _ _ _ _ _ _ i hi hil EA _ _ _ _ _ QA _ hQA jA hjA sA hsA
  have hO : (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T := by
    haveI : IsLocalHom φ := hsh.2.2.1
    rw [← hφ, ← Ideal.comap_comap, GlobalTheory.comap_maximalIdeal_of_localHom_strictHens φ, ← hP]
    first
      | exact Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
      | exact Localization.AtPrime.under_maximalIdeal
      | simpa [Ideal.under] using Localization.AtPrime.under_maximalIdeal (Localization.AtPrime P) P
  obtain ⟨A', _, _, _, _, _, _, ι, α, hια, hα⟩ := GlobalTheory.T.exists_local_hom_to_strictly_henselian_normal T hT A i hil
  obtain ⟨E', _, _, _, Q', _, hQ', β, γ, h1, h2, h3⟩ :=
    GlobalTheory.T.exists_localStage_tensor_polynomial_origin T O hO A i hil EA QA hQA jA hjA A' ι α hια hα
  obtain ⟨hd, hn, hic, hfl⟩ := local_props A' E' Q'
  letI alg : Algebra A' (Localization.AtPrime Q') :=
    ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).toAlgebra
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, Localization.AtPrime Q',
    inferInstance, hd, inferInstance, hn, hic, alg, hfl, ι, α, β, γ, ?_, h2, h3, ?_, ?_⟩
  · have e : algebraMap A (Localization.AtPrime QA) =
        (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C := by
      rw [IsScalarTower.algebraMap_eq A EA (Localization.AtPrime QA),
        IsScalarTower.algebraMap_eq A (Polynomial A) EA, Polynomial.algebraMap_eq,
        IsScalarTower.algebraMap_eq (Polynomial A) EA (Localization.AtPrime QA)]
      rfl
    rw [e]
    exact h1
  · intro h
    apply hsA
    apply hi
    rw [map_zero, ← hια, RingHom.comp_apply, h, map_zero]
  · intro 𝔭 _ _ _
    exact GlobalTheory.T.origin_ideal_extension_prime A' 𝔭 E' Q' hQ'

end GlobalTheory.GoodStageOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePow
section
noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity : GlobalTheory.EtC.B1 := by
  first | (exact @GlobalTheory.EtC.pairingProperties) | (exact GlobalTheory.EtC.pairingProperties) | (intros; apply GlobalTheory.EtC.pairingProperties  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEnlargeByUniformiserRoots
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem etale_enlarge : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    GlobalTheory.KeyOriginEnlarge.PointAtZero A (Localization.AtPrime QA) DA ρ →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hρ hpt
  have htor := hFits.2.2.2.2.2.2
  obtain ⟨a, ha0, ha⟩ := GlobalTheory.T.exists_ne_zero_closureEtaleAt_alt q A EA QA DA actA hq hFits.2.2.1 htor
  obtain ⟨A₁, _, _, _, _, _, _, f, i₁, hf, hi₁, hloc₁, hcomp, hK⟩ :=
    GlobalTheory.T.exists_kummerEnlargement_rootsOfUniformisers T hT q hq hqT A i hFits.1 hFits.2.1 a ha0
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, hFits₁, ⟨ρ₁, hρ₁, hpt₁⟩, hEt, β, h, hβ, hh⟩ :=
    GlobalTheory.T.baseChange_integralClosure_etale_height_one T O hT P φ hφ hsh hP q hq hqT A i EA QA jA ψA DA actA hFits ρ hρ hpt a ha0 ha
      A₁ f i₁ hf hi₁ hloc₁ hcomp hK
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hFits₁, ⟨ρ₁, hρ₁, ?_⟩, β, h, hβ, hh⟩
  exact (GlobalTheory.KeyOriginEnlarge.good_iff_etaleAt _ _ _ _).2
    ⟨GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity q A₁ EA₁ QA₁ DA₁ actA₁ hFits₁.2.2.2.2.2.2 hEt, hpt₁⟩

end GlobalTheory.KeyOriginEnlarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_level_base_change : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_pull  <;> assumption)
end

