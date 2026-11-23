module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.CardAddB
section
noncomputable section

open MeasureTheory Filter Topology Metric

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

theorem cardAddB {m : ℕ} (ε : Fin m → Bool) :
    (Finset.univ.filter fun a => ε a = true).card + (Finset.univ.filter fun a => ε a = false).card = m := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun a => ε a = true)
  simpa using this

theorem nexpB (t r : ℝ) : ‖Complex.exp (-(Complex.I * t * r))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem contIpB {n : ℕ} (y : E n) : Continuous fun β : E n => ip β y := by
  unfold ip
  fun_prop

theorem dens_of (hA : AlgA) (hI : IntG) (hD : DerivF) (hM : MollId) (hG : Gauss) (hCG : ClsGain)
    (hInt : Integr) : Dens := by
  intro m n ε c t hc ht P N hN
  obtain ⟨hTr, hHq, hHinv, hDet, hQc⟩ := hA m n ε
  have ht0 : t ≠ 0 := by
    rcases ht with rfl | rfl
    · exact hc.ne'
    · exact neg_ne_zero.mpr hc.ne'
  have hIt : (Complex.I * (t : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht0)
  have hsec : ∀ (Q : PX m n) (y : E n), secN ε c t Q (herm y) = FP ε c t Q y := by
    intro Q y
    simp only [secN, FP, hTr]
  obtain ⟨P', hP'⟩ : ∃ P' : PX m n, P' = (MvPolynomial.C ((Complex.I * (t : ℂ)) ^ n) * detQ ε) ^ N * P := ⟨_, rfl⟩
  have hev : ∀ x : Fin m → Fin n → ℂ, evX P' x = ((Complex.I * (t : ℂ)) ^ n * (gramX ε x).det) ^ N * evX P x := by
    intro x
    rw [← hDet x, hP']
    simp only [evX, map_mul, map_pow, MvPolynomial.eval_C]
  have hDP' : Delta^[N] (FP ε c t P) = FP ε c t P' := by
    rw [hP']
    exact (hD m n ε c t hc P N).2
  have hFP'c : Continuous (FP ε c t P') := (hD m n ε c t hc P' N).1
  obtain ⟨R, hR⟩ := hG m n ε c t hc ht P
  have hpq := cardAddB ε
  generalize hp : (Finset.univ.filter fun i => ε i = true).card = p at hR hpq
  generalize hq : (Finset.univ.filter fun i => ε i = false).card = q at hR hpq
  have hs : ((t / c : ℝ) : ℂ) = 1 ∨ ((t / c : ℝ) : ℂ) = -1 := by
    rcases ht with rfl | rfl
    · left
      rw [div_self hc.ne']
      simp
    · right
      rw [neg_div, div_self hc.ne']
      simp
  obtain ⟨J, a, G, hGc, ⟨C, hC⟩, hGeq⟩ := hCG n _ hs p q N R
  have hFPcls : FP ε c t P = cls ((t / c : ℝ) : ℂ) 0 p q R := by
    funext y
    rw [← hsec]
    exact hR y
  have hFP'eq : ∀ y, FP ε c t P' y = ∑ j : Fin J, Polynomial.eval 0 (a j) * G j y := by
    intro y
    rw [← hDP', hFPcls, hGeq]
    simp
  have hbd : ∀ y, ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := by
    intro y
    rw [hFP'eq y, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC j y) (norm_nonneg _)
  have hσ : (n : ℝ) ^ 2 / 2 < ((p + q + N : ℕ) : ℝ) / 2 := by
    have h1 : ((n : ℝ)) ^ 2 < ((m + N : ℕ) : ℝ) := by exact_mod_cast hN
    rw [hpq]
    linarith
  have hFP'int : Integrable (FP ε c t P') volume := by
    refine Integrable.mono' (((hInt n).2 _ hσ).const_mul ((∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C)) hFP'c.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖FP ε c t P' y‖ ≤ (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * (C * dP y ^ (-((p + q + N : ℕ) : ℝ) / 2)) := hbd y
      _ = (∑ j : Fin J, ‖Polynomial.eval 0 (a j)‖) * C * dP y ^ (-(((p + q + N : ℕ) : ℝ) / 2)) := by
        rw [neg_div]
        ring
  have hipc : ∀ β y : E n, ip β y = ip y β := by
    intro β y
    simp only [ip]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hcy : ∀ β : E n, Continuous fun y : E n => ip β y := fun β => (contIpB β).congr (fun y => hipc y β)
  have hhc : Continuous fun β : E n => herm β := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hdc : Continuous fun β : E n => (herm β).det := hhc.matrix_det
  have hDc : Continuous fun β : E n => ((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N := (continuous_const.mul hdc).pow N
  have hF : Continuous fun β : E n => ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
    refine continuous_of_dominated (bound := fun y => ‖FP ε c t P' y‖) (fun β => ?_) (fun β => Filter.Eventually.of_forall fun y => ?_) hFP'int.norm (Filter.Eventually.of_forall fun y => ?_)
    · exact hFP'c.aestronglyMeasurable.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (hcy β))).neg)).aestronglyMeasurable
    · rw [norm_mul, nexpB, mul_one]
    · exact continuous_const.mul (Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp (contIpB y))).neg))
  obtain ⟨g, hg⟩ : ∃ g : E n → ℂ, g = fun β => (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹ * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) := ⟨_, rfl⟩
  have hgU : ContinuousOn g {y : E n | (herm y).det ≠ 0} := by
    rw [hg]
    refine ContinuousOn.mul ?_ (continuous_const.mul hF).continuousOn
    exact hDc.continuousOn.inv₀ (fun β hβ => pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβ))
  have hgm : Measurable g := by
    rw [hg]
    exact hDc.measurable.inv.mul (continuous_const.mul hF).measurable
  have hcan : ∀ u v w D : ℂ, D ≠ 0 → u * (v * w) = u * D⁻¹ * (D * v * w) := by
    intro u v w D hD
    rw [show u * D⁻¹ * (D * v * w) = u * (D⁻¹ * D) * (v * w) by ring, inv_mul_cancel₀ hD, mul_one]
  have hA' : ∀ φ : E n → ℂ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {y : E n | (herm y).det ≠ 0} →
      ∫ x, φ (qX ε x) * (evX P x * gs c x) = ∫ β, φ β * g β := by
    intro φ hφc hφs hφU
    have hψc : Continuous (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := by
      apply continuous_of_tsupport
      intro β hβ
      have hβU : (herm β).det ≠ 0 := hφU (tsupport_mul_subset_left hβ)
      exact hφc.continuousAt.mul (hDc.continuousAt.inv₀ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hβU)))
    have hψs : HasCompactSupport (fun β : E n => φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) := hφs.mul_right
    have key2 : (∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x)) = ∫ β, (φ β * (((Complex.I * (t : ℂ)) ^ n * (herm β).det) ^ N)⁻¹) * ((((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) :=
      hM n (Fin m → Fin n → ℂ) volume (fun x => evX P' x * gs c x) (qX ε) (hI m n c hc P') hQc.measurable t ht0 hFP'int _ hψc hψs
    calc (∫ x, φ (qX ε x) * (evX P x * gs c x)) = ∫ x, (φ (qX ε x) * (((Complex.I * (t : ℂ)) ^ n * (herm (qX ε x)).det) ^ N)⁻¹) * (evX P' x * gs c x) := by
          congr 1
          funext x
          rw [hev x]
          by_cases h0 : φ (qX ε x) = 0
          · simp [h0]
          · have hne : (herm (qX ε x)).det ≠ 0 := hφU (subset_tsupport _ (Function.mem_support.mpr h0))
            rw [hHq x] at hne
            rw [hHq x]
            exact hcan _ _ _ _ (pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hIt) hne))
      _ = _ := key2
      _ = ∫ β, φ β * g β := by
          congr 1
          funext β
          rw [hg]
          ring
  refine ⟨g, hgU, ?_, ?_⟩
  · intro S hS hSU
    have hpre : gramX ε ⁻¹' (herm '' S) = qX ε ⁻¹' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hyq : y = qX ε x := by
          calc y = hinv (herm y) := (hHinv y).symm
            _ = hinv (herm (qX ε x)) := by rw [hyx, hHq]
            _ = qX ε x := hHinv _
        rw [← hyq]
        exact hy
      · intro hx
        exact ⟨qX ε x, hx, hHq x⟩
    rw [hpre]
    have hUo : IsOpen {y : E n | (herm y).det ≠ 0} := isOpen_ne_fun hdc continuous_const
    obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open hUo hSU
    have hK : IsCompact (Metric.cthickening δ S) := hS.cthickening
    have hδk : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => div_pos hδ (Nat.cast_add_one_pos k)
    have hδt : Tendsto (fun k : ℕ => δ / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ)
    have hle : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k => div_le_self hδ.le (le_add_of_nonneg_left (Nat.cast_nonneg k))
    obtain ⟨φk, hφk⟩ : ∃ φk : ℕ → E n → ℂ, φk = fun k β => (((thickenedIndicator (hδk k) S β : NNReal) : ℝ) : ℂ) := ⟨_, rfl⟩
    have hφkc : ∀ k, Continuous (φk k) := by
      intro k
      rw [hφk]
      exact Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (thickenedIndicator (hδk k) S).continuous)
    have hφk0 : ∀ k β, β ∉ Metric.cthickening δ S → φk k β = 0 := by
      intro k β hβ
      rw [hφk]
      simp only
      rw [thickenedIndicator_zero (hδk k) S (fun h => hβ (Metric.cthickening_mono (hle k) S (Metric.thickening_subset_cthickening _ _ h)))]
      simp
    have hφk1 : ∀ k β, ‖φk k β‖ ≤ 1 := by
      intro k β
      rw [hφk]
      simp only
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast thickenedIndicator_le_one (hδk k) S β
    have hφks : ∀ k, HasCompactSupport (φk k) := fun k => HasCompactSupport.intro hK (hφk0 k)
    have hφkU : ∀ k, tsupport (φk k) ⊆ {y : E n | (herm y).det ≠ 0} := fun k =>
      (closure_minimal (Function.support_subset_iff'.2 (hφk0 k)) hK.isClosed).trans hδU
    have hlim : ∀ β : E n, Tendsto (fun k : ℕ => φk k β) atTop (𝓝 (S.indicator (fun _ => (1 : ℂ)) β)) := by
      intro β
      have h1 := tendsto_pi_nhds.1 (thickenedIndicator_tendsto_indicator_closure hδk hδt S) β
      rw [hS.isClosed.closure_eq] at h1
      have h2 := ((Complex.continuous_ofReal.comp NNReal.continuous_coe).tendsto _).comp h1
      rw [hφk]
      by_cases hβ : β ∈ S
      · simpa [hβ, Function.comp_def] using h2
      · simpa [hβ, Function.comp_def] using h2
    have hLt : Tendsto (fun k => ∫ x, φk k (qX ε x) * (evX P x * gs c x)) atTop (𝓝 (∫ x, S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x))) := by
      refine tendsto_integral_of_dominated_convergence (fun x => ‖evX P x * gs c x‖) (fun k => ?_) (hI m n c hc P).norm (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
      · exact ((hφkc k).comp hQc).aestronglyMeasurable.mul (hI m n c hc P).aestronglyMeasurable
      · rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
      · exact (hlim (qX ε x)).mul_const _
    have hgK : IntegrableOn g (Metric.cthickening δ S) volume := (hgU.mono hδU).integrableOn_compact hK
    have hRt : Tendsto (fun k => ∫ β, φk k β * g β) atTop (𝓝 (∫ β, S.indicator (fun _ => (1 : ℂ)) β * g β)) := by
      refine tendsto_integral_of_dominated_convergence ((Metric.cthickening δ S).indicator fun β => ‖g β‖) (fun k => ?_) (IntegrableOn.integrable_indicator hgK.norm hK.measurableSet) (fun k => Filter.Eventually.of_forall fun β => ?_) (Filter.Eventually.of_forall fun β => (hlim β).mul_const _)
      · exact (hφkc k).aestronglyMeasurable.mul hgm.aestronglyMeasurable
      · by_cases hβ : β ∈ Metric.cthickening δ S
        · rw [Set.indicator_of_mem hβ, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφk1 k _)
        · simp [hβ, hφk0 k β hβ]
    have heq := tendsto_nhds_unique hLt (Filter.Tendsto.congr (fun k => (hA' (φk k) (hφkc k) (hφks k) (hφkU k)).symm) hRt)
    rw [← integral_indicator (hQc.measurable hS.isClosed.measurableSet), ← integral_indicator hS.isClosed.measurableSet]
    have e1 : ∀ x, (qX ε ⁻¹' S).indicator (fun x => evX P x * gs c x) x = S.indicator (fun _ => (1 : ℂ)) (qX ε x) * (evX P x * gs c x) := by
      intro x
      by_cases h : qX ε x ∈ S <;> simp [h]
    have e2 : ∀ β, S.indicator g β = S.indicator (fun _ => (1 : ℂ)) β * g β := by
      intro β
      by_cases h : β ∈ S <;> simp [h]
    simp only [e1, e2]
    exact heq
  · intro β _
    have hint : (∫ y : E n, Delta^[N] (fun y : E n => secN ε c t P (herm y)) y * chr t β y) = ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ))) := by
      have hfun : (fun y : E n => secN ε c t P (herm y)) = FP ε c t P := funext (hsec P)
      rw [hfun, hDP']
      rfl
    rw [hint, hg]
    have h1 : ((-1 : ℂ) ^ n / (-(Complex.I * (t : ℂ))) ^ n) = ((Complex.I * (t : ℂ)) ^ n)⁻¹ := by
      rw [neg_pow (Complex.I * (t : ℂ)), div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num)), one_div]
    rw [h1]
    have hab : (((2 * Real.pi / |t|) ^ n ^ 2 : ℝ) : ℂ) * (((|t| / (2 * Real.pi)) ^ n ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← mul_pow, div_mul_div_comm, mul_comm (2 * Real.pi) |t|, div_self (mul_ne_zero (abs_ne_zero.mpr ht0) (by positivity)), one_pow, Complex.ofReal_one]
    linear_combination (((herm β).det ^ N)⁻¹ * (((Complex.I * (t : ℂ)) ^ n)⁻¹) ^ N * ∫ y : E n, FP ε c t P' y * Complex.exp (-(Complex.I * (t : ℂ) * (ip β y : ℂ)))) * hab

end PositivityTheory.Rg.Sw.WR.D
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousEvX
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.Sw.WR.D

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem gramX_star (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) (i j : Fin n) :
    star (gramX ε x i j) = gramX ε x j i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramX, Qp, Qb, evX, map_sub, map_sum, map_mul, MvPolynomial.eval_X, ↓reduceIte,
    Bool.false_eq_true, star_sub, star_sum, star_mul, star_star]

theorem herm_hinv (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, star (T i j) = T j i) : herm (hinv T) = T := by
  ext i j
  have h1 : (T j i).re = (T i j).re := by rw [← hT i j]; simp
  have h2 : (T j i).im = -(T i j).im := by rw [← hT i j]; simp
  apply Complex.ext
  · simp [herm, hinv, h1, h2]
    try ring
  · simp [herm, hinv, h1, h2]
    try ring

theorem hinv_herm' (y : E n) : hinv (herm y) = y := by
  funext i j
  simp [hinv, herm]
  ring

theorem herm_mul_apply (y y' : E n) (i j : Fin n) :
    herm y i j * herm y' j i =
      (((y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) + Complex.I * (((y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [herm] <;> ring

theorem trace_herm_mul (y y' : E n) : (herm y * herm y').trace = ((ip y y' : ℝ) : ℂ) := by
  have h1 : ∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 = 0 := by
    simp only [sub_div, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' i j / 2)]
    exact sub_self _
  have h2 : ∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 = ip y y' := by
    simp only [add_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => y j i * y' j i / 2)]
    simp only [ip, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  calc (herm y * herm y').trace = ∑ i, ∑ j, herm y i j * herm y' j i := by
        simp [Matrix.trace, Matrix.mul_apply]
    _ = ((∑ i, ∑ j, (y i j * y' i j + y j i * y' j i) / 2 : ℝ) : ℂ) +
          Complex.I * ((∑ i, ∑ j, (y i j * y' j i - y j i * y' i j) / 2 : ℝ) : ℂ) := by
        simp only [herm_mul_apply, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum]
    _ = ((ip y y' : ℝ) : ℂ) := by rw [h1, h2]; simp

theorem evX_detQ (ε : Fin m → Bool) (x : Fin m → Fin n → ℂ) : evX (detQ ε) x = (gramX ε x).det := by
  rw [evX, detQ, RingHom.map_det]
  rfl

theorem continuous_evX (P : PX m n) : Continuous fun x : Fin m → Fin n → ℂ => evX P x := by
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => ?_)
  split_ifs
  · exact continuous_star.comp ((continuous_apply _).comp (continuous_apply _))
  · exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_qX (ε : Fin m → Bool) : Continuous (qX (n := n) ε) := by
  unfold qX hinv gramX
  exact continuous_pi fun i => continuous_pi fun j =>
    (Complex.continuous_re.comp (continuous_evX _)).add (Complex.continuous_im.comp (continuous_evX _))

theorem algA : AlgA := by
  intro m n ε
  refine ⟨fun y x => ?_, fun x => herm_hinv _ (gramX_star ε x), hinv_herm', evX_detQ ε, continuous_qX ε⟩
  have h := trace_herm_mul y (qX ε x)
  rwa [show herm (qX ε x) = gramX ε x from herm_hinv _ (gramX_star ε x)] at h

end PositivityTheory.Rg.Sw.WR.D
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousHerm
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.WR.T

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem continuous_herm : Continuous (herm : E n → Matrix (Fin n) (Fin n) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold herm
  fun_prop

theorem continuous_dP : Continuous (dP : E n → ℝ) := by
  unfold dP
  exact Complex.continuous_re.comp ((continuous_const.add (continuous_herm.matrix_mul continuous_herm)).matrix_det)

theorem continuous_chr (t : ℝ) (β : E n) : Continuous (chr t β) := by
  unfold chr
  fun_prop

theorem norm_chr (t : ℝ) (β y : E n) : ‖chr t β y‖ = 1 := by
  unfold chr
  rw [Complex.norm_exp]
  simp

theorem abs_log_le (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) : |Real.log x| ≤ (x ^ δ + x ^ (-δ)) / δ := by
  have h1 : δ * Real.log x ≤ x ^ δ := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx δ)
    linarith
  have h2 : -δ * Real.log x ≤ x ^ (-δ) := by
    rw [← Real.log_rpow hx]
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (-δ))
    linarith
  have p1 := Real.rpow_pos_of_pos hx δ
  have p2 := Real.rpow_pos_of_pos hx (-δ)
  rcases abs_cases (Real.log x) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, le_div_iff₀ hδ] <;> nlinarith

theorem rpow_neg_le_add (x a a0 d : ℝ) (hx : 0 < x) (ha : |a - a0| ≤ d) :
    x ^ (-a) ≤ x ^ (-(a0 - d)) + x ^ (-(a0 + d)) := by
  obtain ⟨ha1, ha2⟩ := abs_le.1 ha
  have p1 := Real.rpow_pos_of_pos hx (-(a0 - d))
  have p2 := Real.rpow_pos_of_pos hx (-(a0 + d))
  rcases le_or_gt 1 x with h1 | h1
  · have : x ^ (-a) ≤ x ^ (-(a0 - d)) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    linarith
  · have : x ^ (-a) ≤ x ^ (-(a0 + d)) := Real.rpow_le_rpow_of_exponent_ge hx h1.le (by linarith)
    linarith

theorem rp3 {x : ℝ} (hx : 0 < x) (a b c : ℝ) : x ^ a * x ^ b * x ^ c = x ^ (a + b + c) := by
  rw [Real.rpow_add hx, Real.rpow_add hx]

theorem dP_pos (hI : Integr) (y : E n) : 0 < dP y := by
  obtain ⟨⟨c0, hc0, hc0le⟩, -⟩ := hI n
  exact lt_of_lt_of_le (mul_pos hc0 (by positivity)) (hc0le y)

theorem norm_term (hI : Integr) (t : ℝ) (β : E n) (h : E n → ℂ) (z : ℂ) (y : E n) :
    ‖((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y‖ = dP y ^ (-z.re) * ‖h y‖ := by
  rw [norm_mul, norm_mul, norm_chr, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (dP_pos hI y), Complex.neg_re]

theorem continuous_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (z : ℂ) :
    Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
  have : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z) :=
    (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
  exact (this.mul hh).mul (continuous_chr t β)

theorem integ_term (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) {κ C : ℝ}
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) {z : ℂ} (hz : (n : ℝ) ^ 2 / 2 < z.re + κ) :
    Integrable fun y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y := by
  obtain ⟨-, hint⟩ := hI n
  refine Integrable.mono' ((hint (z.re + κ) hz).const_mul C) (continuous_term hI t β hh z).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_term hI]
  have hp := dP_pos hI y
  calc dP y ^ (-z.re) * ‖h y‖ ≤ dP y ^ (-z.re) * (C * dP y ^ (-κ)) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.rpow_nonneg hp.le _)
    _ = C * dP y ^ (-(z.re + κ)) := by
        rw [neg_add, Real.rpow_add hp]; ring

theorem holo (hI : Integr) (t : ℝ) (β : E n) {h : E n → ℂ} (hh : Continuous h) (κ C : ℝ)
    (hb : ∀ y, ‖h y‖ ≤ C * dP y ^ (-κ)) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y)
      {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + κ} := by
  obtain ⟨-, hint⟩ := hI n
  intro z0 hz0
  simp only [Set.mem_ofPred_eq] at hz0
  set σs := z0.re + κ with hσs
  set δ := (σs - (n : ℝ) ^ 2 / 2) / 4 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hb' : ∀ y, ‖h y‖ ≤ C' * dP y ^ (-κ) := fun y =>
    (hb y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (dP_pos hI y).le _))
  let F : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * h y * chr t β y
  let F' : ℂ → E n → ℂ := fun z y => ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
  have hF'c : Continuous (F' z0) := by
    have hslit : ∀ y : E n, ((dP y : ℝ) : ℂ) ∈ Complex.slitPlane := fun y => Complex.ofReal_mem_slitPlane.2 (dP_pos hI y)
    have h1 : Continuous fun y => ((dP y : ℝ) : ℂ) ^ (-z0) :=
      (Complex.continuous_ofReal.comp continuous_dP).cpow continuous_const hslit
    have h2 : Continuous fun y : E n => ((Real.log (dP y) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_dP.log fun y => (dP_pos hI y).ne')
    exact ((h1.mul h2.neg).mul hh).mul (continuous_chr t β)
  let B : E n → ℝ := fun y => C' / δ * 2 * (dP y ^ (-(σs - 2 * δ)) + dP y ^ (-(σs + 2 * δ)))
  have hBint : Integrable B := by
    refine ((hint _ ?_).add (hint _ ?_)).const_mul (C' / δ * 2)
    · rw [hδ]; linarith
    · rw [hδ]; linarith
  have hbound : ∀ y, ∀ z ∈ Metric.ball z0 δ, ‖F' z y‖ ≤ B y := by
    intro y z hz
    have hp := dP_pos hI y
    have hre : |z.re - z0.re| < δ := by
      have := Complex.abs_re_le_norm (z - z0)
      rw [Complex.sub_re] at this
      exact lt_of_le_of_lt this (by simpa [dist_eq_norm] using hz)
    have hn : ‖F' z y‖ = dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖ := by
      simp only [F', norm_mul, norm_neg, norm_chr, mul_one, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
    rw [hn]
    have e1 := abs_log_le (dP y) δ hp hδpos
    have e2 := hb' y
    have q1 : dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ - δ)) := by
      rw [rp3 hp]; congr 1; ring
    have q2 : dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ) = dP y ^ (-(z.re + κ + δ)) := by
      rw [rp3 hp]; congr 1; ring
    have r1 := rpow_neg_le_add (dP y) (z.re + κ - δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have r2 := rpow_neg_le_add (dP y) (z.re + κ + δ) σs (2 * δ) hp (by rw [abs_le]; constructor <;>
      linarith [(abs_lt.1 hre).1, (abs_lt.1 hre).2])
    have a0 := Real.rpow_nonneg hp.le (-z.re)
    have a1 := Real.rpow_nonneg hp.le δ
    have a2 := Real.rpow_nonneg hp.le (-δ)
    have a3 := Real.rpow_nonneg hp.le (-κ)
    calc dP y ^ (-z.re) * |Real.log (dP y)| * ‖h y‖
        ≤ dP y ^ (-z.re) * ((dP y ^ δ + dP y ^ (-δ)) / δ) * (C' * dP y ^ (-κ)) := by
          gcongr
      _ = C' / δ * (dP y ^ δ * dP y ^ (-z.re) * dP y ^ (-κ) + dP y ^ (-δ) * dP y ^ (-z.re) * dP y ^ (-κ)) := by
          ring
      _ = C' / δ * (dP y ^ (-(z.re + κ - δ)) + dP y ^ (-(z.re + κ + δ))) := by rw [q1, q2]
      _ ≤ B y := by
          have : 0 ≤ C' / δ := div_nonneg hC'0 hδpos.le
          simp only [B]
          nlinarith
  have hdiff : ∀ y, ∀ z ∈ Metric.ball z0 δ, HasDerivAt (fun w => F w y) (F' z y) z := by
    intro y z _
    have hp := dP_pos hI y
    have hx : ((dP y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have h1 : HasDerivAt (fun w : ℂ => ((dP y : ℝ) : ℂ) ^ (-w))
        (((dP y : ℝ) : ℂ) ^ (-z) * Complex.log ((dP y : ℝ) : ℂ) * (-1)) z :=
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl hx)).hasDerivAt).comp z (hasDerivAt_neg z)
    have h2 := (h1.mul_const (h y)).mul_const (chr t β y)
    refine h2.congr_deriv ?_
    show _ = ((dP y : ℝ) : ℂ) ^ (-z) * (-((Real.log (dP y) : ℝ) : ℂ)) * h y * chr t β y
    rw [Complex.ofReal_log hp.le]
    ring
  have hF0 : Integrable (F z0) := integ_term hI t β hh hb' hz0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (x₀ := z0)
    (Metric.ball_mem_nhds z0 hδpos)
    (Eventually.of_forall fun z => (continuous_term hI t β hh z).aestronglyMeasurable) hF0
    hF'c.aestronglyMeasurable (ae_of_all _ hbound) hBint (ae_of_all _ hdiff)
  exact key.2.differentiableAt.differentiableWithinAt

end PositivityTheory.Rg.Sw.WR.T
end
end

