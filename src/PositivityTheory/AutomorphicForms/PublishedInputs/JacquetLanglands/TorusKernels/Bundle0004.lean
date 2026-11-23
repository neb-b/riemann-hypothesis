module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ExistsFix
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

theorem kap_rot (m : GL (Fin 2) ℝ) (a b : ℝ) (h00 : m 0 0 = a) (h01 : m 0 1 = b)
    (h10 : m 1 0 = -b) (h11 : m 1 1 = a) (hb : b ≠ 0) (z : P) (hz : 0 < z.1.im) :
    kap z (m • z) ≤ (a ^ 2 + b ^ 2) / b ^ 2 * kap iP z := by
  set x := z.1.re with hx
  set y := z.1.im with hy
  have hden : den m z.1 ≠ 0 := den_ne m z.2
  have hnd : 0 < Complex.normSq (den m z.1) := Complex.normSq_pos.2 hden
  have hdet : m.val.det = a ^ 2 + b ^ 2 := by rw [det_eq, h00, h01, h10, h11]; ring
  have hb2 : 0 < b ^ 2 := by positivity
  have hs : 0 < a ^ 2 + b ^ 2 := by positivity
  have hwim : (m • z).1.im = (a ^ 2 + b ^ 2) * y / Complex.normSq (den m z.1) := by
    rw [coe_smul, im_div, hdet]
  have hwpos : 0 < (m • z).1.im := by rw [hwim]; positivity
  have hconj : z.1 - conj (m • z).1 = (z.1 * conj (den m z.1) - conj (num m z.1)) / conj (den m z.1) := by
    have : conj (den m z.1) ≠ 0 := (map_ne_zero _).2 hden
    rw [coe_smul, map_div₀]
    field_simp
  have hE : Complex.normSq (z.1 * conj (den m z.1) - conj (num m z.1)) =
      b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    rw [Complex.normSq_apply]
    simp [num, den, h00, h01, h10, h11, ← hx, ← hy]
    ring
  have hN : ‖z.1 - conj (m • z).1‖ ^ 2 = (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) / Complex.normSq (den m z.1) := by
    rw [hconj, Complex.sq_norm, Complex.normSq_div, Complex.normSq_conj, hE]
  have hI : ‖iP.1 - conj z.1‖ ^ 2 = x ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, ← hx, ← hy]
    ring
  have hk1 : kap z (m • z) = 4 * (a ^ 2 + b ^ 2) * y ^ 2 / (b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2) := by
    rw [kap, if_pos (mul_pos hz hwpos), hN, hwim]
    simp only [← hy]
    field_simp
  have hk2 : kap iP z = 4 * y / (x ^ 2 + (1 + y) ^ 2) := by
    rw [kap, if_pos (by simpa [iP] using hz), hI]
    simp [iP, ← hy]
  rw [hk1, hk2]
  have hQ : 0 < b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by positivity
  have hR : 0 < x ^ 2 + (1 + y) ^ 2 := by positivity
  rw [div_mul_div_comm, div_le_div_iff₀ hQ (mul_pos hb2 hR)]
  have h1 : 2 * y ≤ x ^ 2 + y ^ 2 + 1 := by nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have key : b ^ 2 * (y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2) ≤ b ^ 2 * (x ^ 2 + y ^ 2 + 1) ^ 2 + 4 * a ^ 2 * y ^ 2 := by
    have : y * (x ^ 2 + y ^ 2 + 1) + 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2 + 1) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hb2.le, sq_nonneg a, sq_nonneg y]
  have e : x ^ 2 + (1 + y) ^ 2 = (x ^ 2 + y ^ 2 + 1) + 2 * y := by ring
  rw [e]
  have hs' : 0 ≤ 4 * (a ^ 2 + b ^ 2) * y := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hs']

theorem exists_fix (g : GL (Fin 2) ℝ) (hg : g.val.trace ^ 2 < 4 * g.val.det) : ∃ z : P, g • z = z := by
  have htr : g.val.trace = g 0 0 + g 1 1 := Matrix.trace_fin_two _
  rw [htr, det_eq] at hg
  set p := g 0 0 with hp
  set q := g 0 1 with hq
  set r := g 1 0 with hr
  set t := g 1 1 with ht
  set D := 4 * (p * t - q * r) - (p + t) ^ 2 with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hg
    nlinarith [sq_nonneg (p - t)]
  set sD := Real.sqrt D with hsD
  have hsD0 : 0 < sD := Real.sqrt_pos.2 hD0
  have hsD2 : (sD : ℂ) ^ 2 = (D : ℂ) := by
    rw [← Complex.ofReal_pow, hsD, Real.sq_sqrt hD0.le]
  set z0 : ℂ := (((p - t : ℝ) : ℂ) + Complex.I * sD) / (2 * (r : ℂ)) with hz0
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0
  have him : z0.im ≠ 0 := by
    have : z0 = (((p - t) / (2 * r) : ℝ) : ℂ) + ((sD / (2 * r) : ℝ) : ℂ) * Complex.I := by
      rw [hz0]; push_cast; field_simp
    rw [this]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, zero_add]
    rw [add_zero]
    exact div_ne_zero hsD0.ne' (mul_ne_zero two_ne_zero hr0)
  have hz : (2 * (r : ℂ)) * z0 = ((p - t : ℝ) : ℂ) + Complex.I * sD := by
    rw [hz0]; field_simp
  have hquad : (r : ℂ) * z0 ^ 2 + ((t : ℂ) - p) * z0 - q = 0 := by
    have h4 : (4 * (r : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hrc
    apply mul_left_cancel₀ h4
    rw [mul_zero]
    have hDc : (D : ℂ) = 4 * ((p : ℂ) * t - q * r) - (p + t) ^ 2 := by rw [hD]; push_cast; ring
    rw [hDc] at hsD2
    push_cast at hz
    linear_combination (2 * (r : ℂ) * z0 + ((p : ℂ) - t + Complex.I * sD) + 2 * ((t : ℂ) - p)) * hz
      + (sD : ℂ) ^ 2 * Complex.I_sq - hsD2
  refine ⟨(⟨z0, him⟩ : P), Subtype.ext ?_⟩
  change num g z0 / den g z0 = z0
  have hd := den_ne g (z := z0) him
  rw [div_eq_iff hd]
  simp only [num, den]
  rw [← hp, ← hq, ← hr, ← ht]
  linear_combination (-1 : ℂ) * hquad

end UpperTheory.Esk.RadialIntegralLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HalfPlaneMeasureInvariantProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HalfPlaneMeasureLemmas

open UpperTheory.Esk

def U : Set ℂ := {z | z.im ≠ 0}

theorem isOpen_U : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const

def val (z : P) : ℂ := z.1

def mk (z : ℂ) (hz : z.im ≠ 0) : P := ⟨z, hz⟩

theorem openEmb : Topology.IsOpenEmbedding val :=
  isOpen_U.isOpenEmbedding_subtypeVal

theorem measEmb : MeasurableEmbedding val :=
  openEmb.measurableEmbedding

def rho (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / z.im ^ 2)

def F (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / den g z

def D (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((g.val.det : ℂ) / den g z ^ 2)).restrictScalars ℝ

theorem hasDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (F g) ((g.val.det : ℂ) / den g z ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div
    ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)
  refine h.congr_deriv ?_
  simp only [den, id, mul_one]
  rw [det_eq]
  push_cast
  ring

theorem hasFDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : HasFDerivAt (F g) (D g z) z := by
  have := (hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ
  simpa [D] using this

theorem det_D (g : GL (Fin 2) ℝ) (z : ℂ) :
    (D g z).det = Complex.normSq ((g.val.det : ℂ) / den g z ^ 2) := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem F_eq (g : GL (Fin 2) ℝ) (z : P) : F g (val z) = val (g • z) := rfl

theorem injOn_F (g : GL (Fin 2) ℝ) : Set.InjOn (F g) U := by
  intro x hx y hy hxy
  have h : g • mk x hx = g • mk y hy := Subtype.ext hxy
  have := congrArg val (smul_left_cancel g h)
  exact this

theorem key (g : GL (Fin 2) ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫⁻ x in F g '' S, rho x = ∫⁻ x in S, rho x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]
  refine setLIntegral_congr_fun hS (fun x hx => ?_)
  have hx' : x.im ≠ 0 := hSU hx
  have hd := den_ne g hx'
  have hn : Complex.normSq (den g x) ≠ 0 := by simpa using hd
  have hdet := g.det_ne_zero
  rw [det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul
    (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, map_pow]
  field_simp

theorem vol_def : (volume : Measure P) = (Measure.comap val volume).withDensity fun z => rho (val z) := rfl

theorem vol_eq (s : Set P) (hs : MeasurableSet s) : volume s = ∫⁻ z in val '' s, rho z := by
  rw [vol_def, withDensity_apply _ hs, measEmb.restrict_comap,
    ← measEmb.lintegral_map, measEmb.map_comap,
    Measure.restrict_restrict (measEmb.measurableSet_range),
    Set.inter_eq_right.2 (Set.image_subset_range _ _)]

theorem image_pre (g : GL (Fin 2) ℝ) (s : Set P) :
    val '' ((fun z : P => g • z) ⁻¹' s) = F g⁻¹ '' (val '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩
    rw [F_eq g⁻¹ (g • p), inv_smul_smul]
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩
    rw [F_eq]

theorem cont (g : GL (Fin 2) ℝ) : Continuous (fun z : P => g • z) := by
  have hv : Continuous (fun z : P => z.1) := continuous_subtype_val
  have h : Continuous (fun z : P => (g • z).1) := by
    change Continuous (fun z : P => num g z.1 / den g z.1)
    refine Continuous.div ?_ ?_ (fun z => den_ne g z.2)
    · simp only [num]; fun_prop
    · simp only [den]; fun_prop
  exact continuous_induced_rng.2 h

theorem meas_rho : Measurable (fun z : P => rho (val z)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))

end UpperTheory.Esk.HalfPlaneMeasureLemmas

namespace UpperTheory.Esk

open HalfPlaneMeasureLemmas in
theorem half_plane_measure_invariant_proof : B1a := by
  have : LocallyCompactSpace P := openEmb.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts (Measure.comap val volume) := .comap' _ openEmb.continuous measEmb
  have : SigmaFinite (Measure.comap val volume) := inferInstance
  refine ⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩
  · rw [vol_def]
    exact SigmaFinite.withDensity_ofReal _
  · have : (Measure.comap val volume).IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ openEmb
    refine ⟨fun A hA hne => ?_⟩
    rw [vol_def, Ne, withDensity_apply_eq_zero meas_rho]
    have : {x : P | rho (val x) ≠ 0} ∩ A = A := by
      refine Set.inter_eq_right.2 (fun x _ => ?_)
      have := x.2
      simp only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [this]
    exact hA.measure_ne_zero _ hne
  · refine ⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs,
      image_pre, key _ (measEmb.measurableSet_image.2 hs)]
    rintro _ ⟨p, -, rfl⟩
    exact p.2

end UpperTheory.Esk
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicBallVolumeProof
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk

def F (y : ℝ) : ℝ := (1 + y ^ (-(1 / 2 : ℝ))) / (1 + y) ^ 2

theorem F_int : IntegrableOn F (Ioi 0) := by
  have hm : Measurable F := by unfold F; fun_prop
  have h1 : IntegrableOn F (Ioo 0 2) := by
    have hg : IntegrableOn (fun y : ℝ => 1 + y ^ (-(1 / 2 : ℝ))) (Ioo 0 2) :=
      (integrableOn_const (by simp)).add ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 (by norm_num))
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := hy.1
    have hp : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg y]
  have h2 : IntegrableOn F (Ioi 1) := by
    have hg : IntegrableOn (fun y : ℝ => 2 * y ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    have hp : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    have e : y ^ (-2 : ℝ) = 1 / y ^ 2 := by
      rw [Real.rpow_neg hy0.le, one_div]; norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity), e]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    have : 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2 := by
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  exact (h1.union h2).mono_set (fun y (hy : 0 < y) => by
    by_cases h : y < 2
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (show (1 : ℝ) < y by linarith))

def A : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹)

theorem A_lt : A < ∞ := integrable_inv_one_add_sq.lintegral_lt_top

theorem x_int {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹) = ENNReal.ofReal y⁻¹ * A := by
  have h := Real.map_volume_mul_left hy.ne'
  have hm : Measurable fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2)⁻¹) := by fun_prop
  calc ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹)
      = ∫⁻ x, ENNReal.ofReal ((1 + x ^ 2)⁻¹) ∂(Measure.map (y * ·) volume) :=
        (lintegral_map hm (measurable_const_mul y)).symm
    _ = ENNReal.ofReal y⁻¹ * A := by
        rw [h, lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hy), A]

theorem kap_pt {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') = 4 * y / ((y * x) ^ 2 + (1 + y) ^ 2) := by
  have hn : ‖iP.1 - conj (pt x y hy.ne').1‖ ^ 2 = (y * x) ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, pt]; ring
  have him : 0 < iP.1.im * (pt x y hy.ne').1.im := by simp [iP, pt, hy]
  rw [kap, if_pos him, hn]
  simp [iP, pt]

theorem kap_neg (w : P) (hw : w.1.im < 0) : kap iP w = 0 := by
  rw [kap, if_neg]
  simp [iP]; linarith

theorem kap_sq_le {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') ^ 2 ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ := by
  rw [kap_pt hy]
  set D := (y * x) ^ 2 + (1 + y) ^ 2
  have hD1 : 1 + (y * x) ^ 2 ≤ D := by simp only [D]; nlinarith
  have hD2 : (1 + y) ^ 2 ≤ D := by simp only [D]; nlinarith [sq_nonneg (y * x)]
  have hp : 0 < 1 + (y * x) ^ 2 := by positivity
  have hq : 0 < (1 + y) ^ 2 := by positivity
  have e : 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2) := by
    field_simp; ring
  rw [e, div_pow]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc (1 + (y * x) ^ 2) * (1 + y) ^ 2 ≤ D * D := mul_le_mul hD1 hD2 hq.le (by positivity)
    _ = D ^ 2 := by ring

def H (w : P) : ℝ≥0∞ := ENNReal.ofReal (kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))))

theorem H_meas (hc : Continuous fun p : P × P => kap p.1 p.2) : Measurable H := by
  have h1 : Measurable fun w : P => kap iP w :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  have h2 : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  unfold H
  exact ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_const.add (h2.pow_const _)))

def B (y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal (16 * y ^ 2 / ((1 + y) ^ 2) * (1 + y ^ (-(1 / 2 : ℝ)))) * (ENNReal.ofReal y⁻¹ * A) else 0

theorem inner_le (y : ℝ) (hy : y ≠ 0) :
    ∫⁻ x : ℝ, H (pt x y hy) ≤ B y := by
  rcases lt_or_gt_of_ne hy with hn | hp
  · have : ∀ x, H (pt x y hy) = 0 := by
      intro x
      rw [H, kap_neg _ (by simp [pt, hn])]
      simp
    simp [this]
  · rw [B, if_pos hp, ← x_int hp, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_mono fun x => ?_
    rw [H, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have him : |(pt x y hy).1.im| = y := by simp [pt, abs_of_pos hp]
    rw [him]
    have h := kap_sq_le (x := x) hp
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp.le _
    calc kap iP (pt x y hy) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))
        ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ * (1 + y ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring

theorem H_lt (h5 : UpperHalfPlaneMeasureCoordinates) (hc : Continuous fun p : P × P => kap p.1 p.2) : ∫⁻ w, H w < ∞ := by
  obtain ⟨hmp, -, hcont⟩ := h5
  have hHm := H_meas hc
  have hBm : Measurable B := by
    unfold B
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    fun_prop
  have hs : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have : SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure {y : ℝ // y ≠ 0}) := by
    refine SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_
    convert (inferInstance : SigmaFinite ((volume : Measure ℝ).restrict {y : ℝ | y ≠ 0})) using 1
    all_goals first | rfl | exact map_comap_subtype_coe hs _
  have e := lintegral_prod_symm (μ := volume)
    (ν := (Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
    (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp hcont.measurable).aemeasurable
  rw [← hmp.lintegral_comp hHm]
  refine lt_of_eq_of_lt e ?_
  calc ∫⁻ y : {y : ℝ // y ≠ 0}, ∫⁻ x : ℝ, H (pt x y.1 y.2) ∂volume
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|))
      ≤ ∫⁻ y : {y : ℝ // y ≠ 0}, B y.1
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|)) :=
        lintegral_mono fun y => inner_le y.1 y.2
    _ = ∫⁻ y : {y : ℝ // y ≠ 0}, ENNReal.ofReal (1 / |y.1|) * B y.1 ∂(Measure.comap Subtype.val volume) := by
        refine (lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hBm.comp measurable_subtype_coe)).trans ?_
        rfl
    _ = ∫⁻ y in {y : ℝ | y ≠ 0}, ENNReal.ofReal (1 / |y|) * B y :=
        lintegral_subtype_comap hs (fun y => ENNReal.ofReal (1 / |y|) * B y)
    _ ≤ ∫⁻ y, (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (16 * F y) * A) y := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
        by_cases hy : 0 < y
        · rw [indicator_of_mem (show y ∈ Ioi 0 from hy), B, if_pos hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine le_of_eq (congrArg (· * A) (congrArg ENNReal.ofReal ?_))
          unfold F
          field_simp
        · simp [B, hy]
    _ = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y) * A := lintegral_indicator measurableSet_Ioi _
    _ = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y)) * A :=
        lintegral_mul_const _ (by unfold F; fun_prop)
    _ < ∞ := ENNReal.mul_lt_top (F_int.const_mul 16).lintegral_lt_top A_lt

theorem rp_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) {k : ℕ} (hk : 4 ≤ k) : t ^ ((k : ℝ) / 2) ≤ t ^ 2 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases h0.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by linarith)]
    positivity
  · have := Real.rpow_le_rpow_of_exponent_ge h h1 hk2
    simpa using this

end UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk UpperTheory.Esk.HyperbolicBallVolume in
theorem UpperTheory.Esk.hyperbolic_ball_volume_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.B6 := by
  intro h1a h1b h1c h5 k hk
  have hc := h1c.2.2.2.2.1
  have hfin := H_lt h5 hc
  refine ⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩
  rw [ENNReal.coe_toNNReal hfin.ne]
  obtain ⟨g, hg0, hg1, hgz⟩ := h1c.2.2.2.2.2 z
  subst hgz
  have hmp := (h1a.2.2 g).2
  have him : ∀ w : P, (g • w).1.im = g.val.det * w.1.im := by
    intro w
    have hden : den g w.1 = 1 := by simp [den, hg0, hg1]
    rw [coe_smul, im_div, hden, Complex.normSq_one, div_one]
  have hdet : g.val.det ≠ 0 := g.det_ne_zero
  have hkc : ∀ z : P, Continuous fun w : P => kap z w := fun z =>
    hc.comp (continuous_const.prodMk continuous_id)
  have hima : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  have hb := h1c.1
  have hkinv := h1b.2.2.2.1 g iP
  constructor
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp ((hkc _).measurable.pow_const _))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          calc kap iP w ^ ((k : ℝ) / 2) ≤ kap iP w ^ 2 := rp_le h0 h1 hk
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2) * (|(g • iP).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2) *
            (|(g • iP).1.im| / |(g • w).1.im|) ^ ((1 : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp (((hkc _).measurable.pow_const _).mul
            ((measurable_const.div hima).pow_const _)))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w, him, him]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have e : |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹ := by
            rw [show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div, div_self (abs_ne_zero.2 hdet),
              one_div]
          rw [e, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          have hk' := rp_le h0 h1 hk
          have : (-((1 : ℝ) / 2)) = -(1 / 2 : ℝ) := rfl
          calc kap iP w ^ ((k : ℝ) / 2) * |w.1.im| ^ (-((1 : ℝ) / 2))
              ≤ kap iP w ^ 2 * |w.1.im| ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk' hp0
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end
end

