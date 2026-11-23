module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceTransposePow
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Density

theorem integral_norm_sq (f : ℝ → ℝ) :
    ∫ z : ℂ, f (‖z‖ ^ 2) = Real.pi * ∫ r in Set.Ioi (0 : ℝ), f r := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) (fun r => f (r ^ 2)),
    ← integral_comp_rpow_Ioi f (p := 2) two_ne_zero]
  have : ∫ x in Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • f (x ^ (2 : ℝ)) =
      2 * ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f (y ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    norm_num [mul_assoc]
  rw [this]
  simp [Measure.real, Complex.volume_ball]
  ring

def expAvg (G : ℝ → ℝ) (σ t : ℝ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), Real.exp (-r) * G (t - σ * r)

theorem hasDerivAt_expAvg_one {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) {t : ℝ}
    (hc : ContinuousAt G t) : HasDerivAt (expAvg G 1) (G t - expAvg G 1 t) t := by
  have hint : ∀ s : ℝ, IntegrableOn (fun u => Real.exp u * G u) (Set.Iic s) := fun s =>
    (integrableOn_exp_Iic s).mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hE : ∀ s : ℝ, expAvg G 1 s = Real.exp (-s) * ∫ u in Set.Iic s, Real.exp u * G u := by
    intro s
    have h1 := integral_comp_neg_Iic s (fun x => Real.exp (-x) * G (-x))
    have h2 := integral_sub_right_eq_self
      ((Set.Ioi (-s)).indicator fun x => Real.exp (-x) * G (-x)) s (μ := volume)
    simp only [neg_neg] at h1
    rw [h1, ← integral_indicator measurableSet_Ioi, ← h2, ← integral_const_mul, expAvg,
      ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : x - s ∈ Set.Ioi (-s) ↔ x ∈ Set.Ioi 0 := by
      simp only [Set.mem_Ioi]; constructor <;> intro h <;> linarith
    simp only [Set.indicator, this]
    split_ifs
    · rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    · simp
  have hI : HasDerivAt (fun s => ∫ u in Set.Iic s, Real.exp u * G u) (Real.exp t * G t) t := by
    have h1 : (fun s => ∫ u in Set.Iic s, Real.exp u * G u) =
        fun s => (∫ u in Set.Iic t, Real.exp u * G u) + ∫ u in t..s, Real.exp u * G u := by
      funext s
      rw [← intervalIntegral.integral_Iic_sub_Iic (hint t) (hint s)]; ring
    rw [h1]
    refine HasDerivAt.const_add _ (intervalIntegral.integral_hasDerivAt_right (by simp) ?_ ?_)
    · exact (Real.measurable_exp.mul hm).stronglyMeasurable.stronglyMeasurableAtFilter
    · exact Real.continuous_exp.continuousAt.mul hc
  have h := ((hasDerivAt_id t).neg.exp).mul hI
  rw [funext hE]
  refine HasDerivAt.congr_deriv h ?_
  simp only [Pi.neg_apply, id]
  rw [← mul_assoc, ← Real.exp_add]; simp; ring

theorem hasDerivAt_expAvg {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool) {t : ℝ}
    (hc : ContinuousAt G t) :
    HasDerivAt (expAvg G (sgn ℝ s)) (sgn ℝ s * (G t - expAvg G (sgn ℝ s) t)) t := by
  cases s
  · have h1 : ∀ u, expAvg G (-1) u = expAvg (fun x => G (-x)) 1 (-u) := by
      intro u; unfold expAvg; congr 1; funext r; congr 2; ring
    have hc' : ContinuousAt (fun x => G (-x)) (-t) :=
      ContinuousAt.comp (f := fun x : ℝ => -x) (by simpa using hc) continuous_neg.continuousAt
    have h := (hasDerivAt_expAvg_one (G := fun x => G (-x)) (hm.comp measurable_neg) (fun u => hb _) hc').comp t
      (hasDerivAt_neg t)
    have hs : sgn ℝ false = -1 := by simp [sgn]
    rw [hs, funext h1]
    refine HasDerivAt.congr_deriv h ?_
    simp
  · have hs : sgn ℝ true = 1 := by simp [sgn]
    rw [hs, one_mul]
    exact hasDerivAt_expAvg_one hm hb hc

theorem expAvg_pos {G : ℝ → ℝ} (hm : Monotone G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool)
    (h : G (-1) < G 1) : 0 < sgn ℝ s * (G (sgn ℝ s) - expAvg G (sgn ℝ s) (sgn ℝ s)) := by
  set σ := sgn ℝ s with hσ
  have he : IntegrableOn (fun r => Real.exp (-r)) (Set.Ioi (0 : ℝ)) := integrableOn_exp_neg_Ioi 0
  have h1 : IntegrableOn (fun r => Real.exp (-r) * G (σ - σ * r)) (Set.Ioi (0 : ℝ)) :=
    he.mul_bdd (hm.measurable.comp (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun _ => hb _)
  have h2 : σ * (G σ - expAvg G σ σ) =
      ∫ r in Set.Ioi (0 : ℝ), σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) := by
    rw [integral_const_mul, integral_sub (he.mul_const _) h1, integral_mul_const, integral_exp_neg_Ioi_zero,
      one_mul, expAvg]
  have hle : ∀ r, 0 ≤ r → 0 ≤ σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (-1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ 1 by linarith)
      linarith
  have hlt : ∀ r, 2 < r → 0 < σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ -1 by linarith)
      linarith
  have e : ∀ r, σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) =
      Real.exp (-r) * (σ * (G σ - G (σ - σ * r))) := fun r => by ring
  rw [h2, setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le (show 0 < volume (Set.Ioi (2 : ℝ)) by simp) (measure_mono fun r hr => ⟨?_, ?_⟩)
    · rw [Function.mem_support, e]
      exact (mul_pos (Real.exp_pos _) (hlt r hr)).ne'
    · exact (lt_trans two_pos (show (2 : ℝ) < r from hr) : (0 : ℝ) < r)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [e]
    exact mul_nonneg (Real.exp_pos _).le (hle r (le_of_lt hr))
  · exact ((he.mul_const _).sub h1).const_mul _

def cdf {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : ℝ := ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y

theorem continuous_qEps {n : ℕ} (ε : Fin n → Bool) : Continuous (qEps ε) := by
  unfold qEps; fun_prop

theorem measurableSet_qEps {n : ℕ} (ε : Fin n → Bool) (t : ℝ) :
    MeasurableSet {y : Fin n → ℂ | qEps ε y ≤ t} :=
  measurableSet_le (continuous_qEps ε).measurable measurable_const

theorem integrable_gauss (n : ℕ) : Integrable (gauss : (Fin n → ℂ) → ℝ) := by
  have h1 : Integrable fun z : ℂ => Real.exp (-‖z‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin n) (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) fun _ => h1
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [gauss, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem cdf_mono {n : ℕ} (ε : Fin n → Bool) : Monotone (cdf ε) := fun _ _ h =>
  setIntegral_mono_set (integrable_gauss n).integrableOn
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
    (Filter.EventuallySubset.of_subset fun _ hy => le_trans hy h)

theorem abs_cdf_le {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : |cdf ε t| ≤ ∫ y : Fin n → ℂ, gauss y := by
  rw [abs_of_nonneg (show 0 ≤ cdf ε t from integral_nonneg fun y => (gauss_pos y).le)]
  exact setIntegral_le_integral (integrable_gauss n) (Filter.Eventually.of_forall fun y => (gauss_pos y).le)

theorem cdf_lt {n : ℕ} (ε : Fin n → Bool) : cdf ε (-1) < cdf ε 1 := by
  have h := setIntegral_sdiff (measurableSet_qEps ε (-1))
    ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ 1}))
    (fun y (hy : qEps ε y ≤ -1) => show qEps ε y ≤ 1 by linarith)
  rw [← sub_pos, cdf, cdf, ← h, setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le) (integrable_gauss n).integrableOn]
  have ho : IsOpen (qEps ε ⁻¹' Set.Ioo (-1) 1) := isOpen_Ioo.preimage (continuous_qEps ε)
  refine lt_of_lt_of_le (ho.measure_pos volume ⟨0, by simp [qEps]⟩) (measure_mono fun y hy => ⟨?_, ?_, ?_⟩)
  · exact (gauss_pos y).ne'
  · exact hy.2.le
  · exact not_le.2 hy.1

theorem cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) (t : ℝ) :
    cdf ε t = Real.pi * expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) a).symm
  have hi := (integrable_gauss (n + 1)).indicator (measurableSet_qEps ε t)
  have hi' := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [cdf, ← integral_indicator (measurableSet_qEps ε t), ← hp.integral_comp', expAvg,
    ← integral_norm_sq fun r => Real.exp (-r) * cdf (fun i => ε (a.succAbove i)) (t - sgn ℝ (ε a) * r)]
  refine (integral_prod _ hi').trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [cdf]
  rw [← integral_indicator (measurableSet_qEps _ _), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp, Set.indicator, Set.mem_ofPred_eq, qEps, gauss, Fin.sum_univ_succAbove _ a,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, sgn, le_sub_iff_add_le']
  split_ifs <;> simp [Real.exp_add, mul_comm]

theorem hasDerivAt_cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) {t : ℝ}
    (hc : ContinuousAt (cdf fun i => ε (a.succAbove i)) t) :
    HasDerivAt (cdf ε) (Real.pi * (sgn ℝ (ε a) * (cdf (fun i => ε (a.succAbove i)) t -
      expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t))) t := by
  rw [funext (cdf_succ ε a)]
  exact (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε a) hc).const_mul _

theorem cdf_zero_eventually (ε : Fin 0 → Bool) {t : ℝ} (ht : t ≠ 0) : cdf ε =ᶠ[nhds t] fun _ => cdf ε t := by
  rcases ht.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with u (hu : u < 0)
    simp [cdf, qEps, not_le.2 h, not_le.2 hu]
  · filter_upwards [Ioi_mem_nhds h] with u (hu : 0 < u)
    simp [cdf, qEps, h.le, hu.le]

theorem differentiableAt_cdf : ∀ {n : ℕ} (ε : Fin n → Bool) {t : ℝ}, t ≠ 0 → DifferentiableAt ℝ (cdf ε) t
  | 0, ε, _, ht => (differentiableAt_const _).congr_of_eventuallyEq (cdf_zero_eventually ε ht)
  | _ + 1, ε, _, ht => (hasDerivAt_cdf_succ ε 0 (differentiableAt_cdf _ ht).continuousAt).differentiableAt

theorem continuousOn_gaussDens : ∀ {n : ℕ} (ε : Fin n → Bool), ContinuousOn (gaussDens ε) {β | β ≠ 0}
  | 0, ε => (continuousOn_const (c := (0 : ℝ))).congr fun t ht => by
      show deriv (cdf ε) t = 0
      rw [(cdf_zero_eventually ε ht).deriv_eq]; simp
  | n + 1, ε => by
      have hc : ∀ t : ℝ, t ≠ 0 → ContinuousAt (cdf fun i => ε ((0 : Fin (n + 1)).succAbove i)) t :=
        fun t ht => (differentiableAt_cdf _ ht).continuousAt
      refine ContinuousOn.congr (f := fun t => Real.pi * (sgn ℝ (ε 0) *
        (cdf (fun i => ε ((0 : Fin (n + 1)).succAbove i)) t -
          expAvg (cdf fun i => ε ((0 : Fin (n + 1)).succAbove i)) (sgn ℝ (ε 0)) t))) ?_ ?_
      · intro t ht
        exact (continuousAt_const.mul (continuousAt_const.mul ((hc t ht).sub
          (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε 0) (hc t ht)).continuousAt))).continuousWithinAt
      · intro t ht
        exact (hasDerivAt_cdf_succ ε 0 (hc t ht)).deriv

theorem gaussDens_spec (n : ℕ) (ε : Fin n → Bool) :
    (∀ β : ℝ, β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) (gaussDens ε β) β ∧
      0 ≤ gaussDens ε β) ∧ ContinuousOn (gaussDens ε) {β | β ≠ 0} ∧
      ∀ s : Bool, (∃ a, ε a = s) → 0 < gaussDens ε (sgn ℝ s) := by
  refine ⟨fun β hβ => ⟨(differentiableAt_cdf ε hβ).hasDerivAt, (cdf_mono ε).deriv_nonneg⟩,
    continuousOn_gaussDens ε, ?_⟩
  rintro s ⟨a, rfl⟩
  obtain _ | n := n
  · exact a.elim0
  have hs : sgn ℝ (ε a) ≠ 0 := by unfold sgn; split_ifs <;> simp
  show 0 < deriv (cdf ε) _
  rw [(hasDerivAt_cdf_succ ε a (differentiableAt_cdf _ hs).continuousAt).deriv]
  exact mul_pos Real.pi_pos (expAvg_pos (cdf_mono _) (abs_cdf_le _) _ (cdf_lt _))

end GlobalTheory.GaussMean.Density
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section
namespace GlobalTheory.Dec.GelfAd

variable {n : ℕ}

private lemma conj_apply_lemma {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a b = ∑ c, ∑ d, (P a c * Q d b) • X c d := by
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [Algebra.smul_def, map_mul, mul_assoc, ← Algebra.commutes (Q d b) (X c d), ← mul_assoc]

private lemma sum_diag_conj_eq_sum_diag {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) :
    ∑ a, (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) a a = ∑ a, X a a := by
  simp only [conj_apply_lemma]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have hd : ∀ d, ∑ a, P a c * Q d a = (1 : Matrix (Fin n) (Fin n) ℂ) d c := fun d => by
    rw [← hQP, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp [hd, Matrix.one_apply]

private lemma conj_pow_of_mul_eq_one' {A : Type} [Ring A] [Algebra ℂ A] (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (X : Matrix (Fin n) (Fin n) A) (m : ℕ) :
    (P.map (algebraMap ℂ A) * X * Q.map (algebraMap ℂ A)) ^ m =
      P.map (algebraMap ℂ A) * X ^ m * Q.map (algebraMap ℂ A) := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have h1 : Q.map (algebraMap ℂ A) * P.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hQP]
    simp
  have h2 : P.map (algebraMap ℂ A) * Q.map (algebraMap ℂ A) = 1 := by
    rw [← Matrix.map_mul, hPQ]
    simp
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, h2]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (Q.map (algebraMap ℂ A)) (P.map (algebraMap ℂ A)), h1, one_mul]

private lemma pow_apply_mul_eq_mul_pow_apply {A : Type} [Ring A] (M N : Matrix (Fin n) (Fin n) A) (R : A)
    (h : ∀ a b, M a b * R = R * N a b) (m : ℕ) :
    ∀ a b, (M ^ m) a b * R = R * (N ^ m) a b := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  | succ m ih =>
    intro a b
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_assoc, h c b, ← mul_assoc ((M ^ m) a c), ih a c, mul_assoc]

lemma trace_pow_comm {A : Type} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (R : A)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (h : ∀ a b, E a b * R = R * ∑ c, ∑ d, (P a c * Q d b) • E c d) (m : ℕ) :
    (∑ c, (Matrix.of E ^ m) c c) * R = R * ∑ c, (Matrix.of E ^ m) c c := by
  have hN : ∀ a b, Matrix.of E a b * R =
      R * (P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) a b := by
    intro a b
    rw [conj_apply_lemma]
    exact h a b
  calc (∑ c, (Matrix.of E ^ m) c c) * R
      = ∑ c, R * ((P.map (algebraMap ℂ A) * Matrix.of E * Q.map (algebraMap ℂ A)) ^ m) c c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => pow_apply_mul_eq_mul_pow_apply _ _ R hN m c c
    _ = R * ∑ c, (Matrix.of E ^ m) c c := by
        rw [← Finset.mul_sum, conj_pow_of_mul_eq_one' P Q hQP, sum_diag_conj_eq_sum_diag P Q hQP]

lemma inv_mul_of_UJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Jm ε * kᴴ * Jm ε * k = 1 := by
  unfold inUJ at hk
  rw [Matrix.mul_assoc (Jm ε * kᴴ), Matrix.mul_assoc (Jm ε), ← Matrix.mul_assoc kᴴ, hk,
    Formalism.REAL.Jm_mul_self]

lemma Rd_right (X k g : Matrix (Fin n) (Fin n) ℂ) (hk : IsUnit k) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Rd X (fun x => f (x * k)) g = Rd (k⁻¹ * X * k) f (g * k) := by
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp hk
  simp only [Rd]
  congr 1
  funext t
  congr 1
  rw [show ((t : ℂ) • (k⁻¹ * X * k)) = k⁻¹ * ((t : ℂ) • X) * k by
    rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' k _ hk]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc g k k⁻¹, Matrix.mul_nonsing_inv k hd, Matrix.mul_one]

private lemma isUnit_of_inUJ_flag_measures {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    IsUnit k :=
  (Matrix.isUnit_iff_isUnit_det k).mpr (Matrix.isUnit_det_of_left_inverse (inv_mul_of_UJ hk))

private lemma Jm_conjTranspose_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (k⁻¹ * Z * k)ᴴ * Jm ε = k⁻¹ * (Jm ε * Zᴴ * Jm ε) * k := by
  have hinv : k⁻¹ = Jm ε * kᴴ * Jm ε := Matrix.inv_eq_left_inv (inv_mul_of_UJ hk)
  have hL : Jm ε * kᴴ = k⁻¹ * Jm ε := by
    rw [hinv]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  have hR : (k⁻¹)ᴴ * Jm ε = Jm ε * k := by
    rw [hinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [hR, ← Matrix.mul_assoc (Jm ε) kᴴ, hL]
  simp only [Matrix.mul_assoc]

private lemma cpart1_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart1 ε (k⁻¹ * Z * k) = k⁻¹ * cpart1 ε Z * k := by
  rw [cpart1, cpart1, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_smul,
    Matrix.smul_mul]

private lemma cpart2_conj_of_inUJ {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z : Matrix (Fin n) (Fin n) ℂ) : cpart2 ε (k⁻¹ * Z * k) = k⁻¹ * cpart2 ε Z * k := by
  rw [cpart2, cpart2, Jm_conjTranspose_conj_of_inUJ hk, ← Matrix.add_mul, ← Matrix.mul_add, Matrix.mul_smul,
    Matrix.smul_mul]

lemma Ec_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (Z g : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Ec ε Z (fun x => f (x * k)) g = Ec ε (k⁻¹ * Z * k) f (g * k) := by
  have hu := isUnit_of_inUJ_flag_measures hk
  simp only [Ec]
  rw [Rd_right _ _ _ hu f, Rd_right _ _ _ hu f, cpart1_conj_of_inUJ hk, cpart2_conj_of_inUJ hk]

private lemma inUJ_mul_flag_measures' {ε : Fin n → Bool} {g k : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g)
    (hk : inUJ ε k) : inUJ ε (g * k) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc kᴴ * gᴴ * Jm ε * (g * k) = kᴴ * (gᴴ * Jm ε * g) * k := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hk]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
lemma smooth_right {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) : SmoothOnG ε (fun x => f (x * k)) := by
  have hc : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * k) :=
    (LinearMap.mulRight ℝ k).toContinuousLinearMap.contDiff
  unfold SmoothOnG at hf ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hmem, hF, hfF⟩ := hf (g₀ * k) (inUJ_mul_flag_measures' hg₀ hk)
  exact ⟨(fun x => x * k) ⁻¹' U, fun x => F (x * k), hU.preimage hc.continuous, hmem,
    hF.comp hc.contDiffOn (fun _ hx => hx), fun g hg hgJ => hfF (g * k) hg (inUJ_mul_flag_measures' hgJ hk)⟩


open GlobalTheory.CapelliCentral in
def rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) :
    Module.End ℂ (smoothSpace ε ℂ) where
  toFun F := mk (fun x => F.1 (x * k)) (smooth_right hk F.2.1)
  map_add' F F' := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (F + F').2.1) hg).trans
      (congrArg₂ (· + ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm
        (mk_apply _ (smooth_right hk F'.2.1) hg).symm)
  map_smul' c F := by
    apply ext_on
    intro g hg
    exact (mk_apply _ (smooth_right hk (c • F).2.1) hg).trans
      (congrArg (c • ·) (mk_apply _ (smooth_right hk F.2.1) hg).symm)

open GlobalTheory.CapelliCentral in
lemma rightEnd_apply {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    (F : smoothSpace ε ℂ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    (rightEnd hk F).1 g = F.1 (g * k) := by
  simp only [rightEnd, LinearMap.coe_mk, AddHom.coe_mk]
  exact mk_apply _ _ hg

private lemma Ec_eq_EcV (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Ec ε Z f g = EcV ε Z f g := by
  simp only [Ec, EcV, rdV_eq, smul_eq_mul]

private lemma mul_single_mul_apply' (M N : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    (M * Matrix.single a b (1 : ℂ) * N : Matrix (Fin n) (Fin n) ℂ) c d = M c a * N b d := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

open GlobalTheory.CapelliCentral in
lemma eabEnd_rightEnd {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k) (a b : Fin n) :
    eabEnd ε ℂ a b * rightEnd hk =
      rightEnd hk * ∑ c, ∑ d, ((k⁻¹)ᵀ a c * kᵀ d b) • eabEnd ε ℂ c d := by
  apply LinearMap.ext
  intro F
  apply ext_on
  intro g hg
  have hgk : inUJ ε (g * k) := inUJ_mul_flag_measures' hg hk
  rw [Module.End.mul_apply, Module.End.mul_apply, rightEnd_apply hk _ hg,
    eabEnd_apply (f := fun x => F.1 (x * k)) a b (rightEnd hk F) (fun x hx => rightEnd_apply hk F hx) hg,
    eabV_eq, Eab, Ec_right hk _ g F.1, Ec_eq_EcV, ecSumV n ε ℂ F.1 _ (g * k) F.2.1 hgk]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Submodule.coe_sum,
    Submodule.coe_smul, Pi.smul_apply, eabEnd_apply (f := F.1) _ _ F (fun _ _ => rfl) hgk,
    mul_single_mul_apply', Matrix.transpose_apply]

theorem gelf_right : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε →
    gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  intro n ε m f k g hf hk hg
  have hkU : inUJ ε k := hk
  have hgU : inUJ ε g := hg
  have hd : IsUnit k.det := (Matrix.isUnit_iff_isUnit_det k).mp (isUnit_of_inUJ_flag_measures hkU)
  have hQP : kᵀ * (k⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul k hd, Matrix.transpose_one]
  have hfV : SmoothOnGV ε f := (smoothOnGV_iff ε f).mpr hf
  let F : GlobalTheory.CapelliCentral.smoothSpace ε ℂ := GlobalTheory.CapelliCentral.mk f hfV
  have hFf : ∀ x, inUJ ε x → F.1 x = f x := fun x hx => GlobalTheory.CapelliCentral.mk_apply f hfV hx
  have hcomm := trace_pow_comm (GlobalTheory.CapelliCentral.eabEnd ε ℂ) (rightEnd hkU) (k⁻¹)ᵀ kᵀ hQP
    (eabEnd_rightEnd hkU) (m + 1)
  have h1 := congrArg (fun T : Module.End ℂ (GlobalTheory.CapelliCentral.smoothSpace ε ℂ) => (T F).1 g) hcomm
  simp only [Module.End.mul_apply] at h1
  rw [GlobalTheory.Dec.FormF.gelf_apply (f := fun x => f (x * k)) m (rightEnd hkU F)
      (fun x hx => (rightEnd_apply hkU F hx).trans (hFf _ (inUJ_mul_flag_measures' hx hkU))) hgU,
    rightEnd_apply hkU _ hgU,
    GlobalTheory.Dec.FormF.gelf_apply m F hFf (inUJ_mul_flag_measures' hgU hkU)] at h1
  exact h1

end GlobalTheory.Dec.GelfAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivatives
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem inMir_diag1_succ {g : ℕ} [Fact g.Prime] {k : ℕ} (h : Gn g k) :
    InMir ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) := by
  unfold InMir diag1 toG
  intro i j hi
  split_ifs with hu
  · have hk : ¬ ((i : ℕ) < k) := by omega
    refine (congrFun (congrFun hu.unit_spec i) j).trans ?_
    simp [hk]
  · rfl

theorem mirClass_diag1_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  intro g inst ψ hψ k F hF h
  rw [_root_.GlobalTheory.GLm.MirSum.eq_sum_indR_der g ψ hψ (k + 1) F (by omega) hF (diag1 h (k + 1)) (inMir_diag1_succ h)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev g ψ i k (der ψ i F) hik (_root_.GlobalTheory.GLm.DerClass.isClass_der g ψ i (k + 1) F (by omega) hF) h

end GlobalTheory.GLm
end

