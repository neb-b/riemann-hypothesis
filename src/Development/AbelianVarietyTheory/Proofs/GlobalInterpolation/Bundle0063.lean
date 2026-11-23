module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreIntegralPiProdEqProdFibreIntegral
section
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Set Topology
open scoped ENNReal

namespace GlobalTheory.FibreProd

theorem le_of_lintegral_ball_eq {X : Type} [PseudoMetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G H : X → ℝ≥0∞) (b : X) (hG : ContinuousAt G b) (hH : ContinuousAt H b)
    (h : ∀ r > 0, ∫⁻ x in Metric.ball b r, G x ∂ν = ∫⁻ x in Metric.ball b r, H x ∂ν) :
    H b ≤ G b := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨d, hd1, hd2⟩ := exists_between hc2
  have e : ∀ᶠ x in 𝓝 b, G x < c ∧ d < H x :=
    (hG.eventually (gt_mem_nhds hc1)).and (hH.eventually (lt_mem_nhds hd2))
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 e
  have h1 : ∫⁻ x in Metric.ball b r, G x ∂ν ≤ c * ν (Metric.ball b r) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).1.le
  have h2 : d * ν (Metric.ball b r) ≤ ∫⁻ x in Metric.ball b r, H x ∂ν := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' measurableSet_ball fun x hx => (hb x hx).2.le
  have h3 : c * ν (Metric.ball b r) < d * ν (Metric.ball b r) :=
    ENNReal.mul_lt_mul_left (Metric.measure_ball_pos ν b hr).ne' measure_ball_lt_top.ne hd1
  exact absurd (h2.trans ((h r hr).symm.le.trans h1)) h3.not_ge

theorem lintegral_preimage {V X : Type} [TopologicalSpace V] [MeasurableSpace V]
    [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → X} {U : Set V} {B : Set X} {fib : X → Measure V}
    (hf : Measurable f) (hU : IsOpen U) (h : IsFibreFamily μ f id U ν B fib)
    (φ : V → ℝ≥0∞) (hφ : Measurable φ) (hs : ∀ v, v ∉ U → φ v = 0)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  have e1 : ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ v in U, (f ⁻¹' S).indicator φ v ∂μ := by
    rw [← lintegral_indicator hU.measurableSet]
    congr 1
    funext v
    by_cases hv : v ∈ U
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]
      exact indicator_apply_eq_zero.2 fun _ => hs v hv
  rw [e1, h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ U := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_mem (by simpa [hv] using hbS) _
  · rw [indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact indicator_of_notMem (by simpa [hv] using hbS) _

theorem lintegral_fibre_prod : ∀ (T V : Type) [Fintype T] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ₀ : Measure V) [SigmaFinite μ₀] (q : V → ℝ), Continuous q → ∀ U : Set V, IsOpen U → ∀ fib : ℝ → Measure V, IsFibreFamily μ₀ q id U (volume : Measure ℝ) Set.univ fib → ∀ B : Set (T → ℝ), IsOpen B → ∀ Fib : (T → ℝ) → Measure (T → V), IsFibreFamily (Measure.pi fun _ : T => μ₀) (fun x ρ => q (x ρ)) id Set.univ (volume : Measure (T → ℝ)) B Fib → ∀ b ∈ B, ∀ φ : T → V → ℝ, (∀ ρ, Continuous (φ ρ) ∧ HasCompactSupport (φ ρ) ∧ tsupport (φ ρ) ⊆ U ∧ ∀ y, 0 ≤ φ ρ y) → ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b) = ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
  intro T V _ _ _ _ _ _ μ₀ _ q hq U hU fib hfib B hB Fib hFib b hb φ hφ
  classical
  haveI : ProperSpace V := FiniteDimensional.proper_real V
  have hΦc : Continuous fun x : T → V => ∏ ρ, φ ρ (x ρ) :=
    continuous_finsetProd _ fun ρ _ => (hφ ρ).1.comp (continuous_apply ρ)
  have hΦs : HasCompactSupport fun x : T → V => ∏ ρ, φ ρ (x ρ) := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun ρ => (hφ ρ).2.1) fun x hx => ?_
    rw [mem_univ_pi, not_forall] at hx
    obtain ⟨ρ, hρ⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ ρ) (image_eq_zero_of_notMem_tsupport hρ)
  obtain ⟨hI, hC⟩ := hFib.2.2 _ hΦc hΦs (subset_univ _)
  have hm : ∀ ρ, Measurable fun y => ENNReal.ofReal (φ ρ y) := fun ρ =>
    ENNReal.measurable_ofReal.comp (hφ ρ).1.measurable
  have hGc : ContinuousOn (fun b => ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib b)) B := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn hC).congr fun b hb => ?_
    have := ofReal_integral_eq_lintegral_ofReal (hI b hb)
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun ρ _ => (hφ ρ).2.2.2 _)
    simp only [Function.comp_apply]
    rw [this]
    congr 1
    funext x
    rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => (hφ ρ).2.2.2 _]
  have hg : ∀ ρ t, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) = ENNReal.ofReal (∫ y, φ ρ y ∂(fib t)) :=
    fun ρ t => (ofReal_integral_eq_lintegral_ofReal
      ((hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).1 t (mem_univ _))
      (Filter.Eventually.of_forall (hφ ρ).2.2.2)).symm
  have hgc : ∀ ρ, Continuous fun t => ∫ y, φ ρ y ∂(fib t) := fun ρ =>
    continuousOn_univ.1 (hfib.2.2 _ (hφ ρ).1 (hφ ρ).2.1 (hφ ρ).2.2.1).2
  have hgm : ∀ ρ, Measurable fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t) := fun ρ => by
    simp only [hg]
    exact ENNReal.measurable_ofReal.comp (hgc ρ).measurable
  have hHc : Continuous fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ)) := by
    have : (fun b : T → ℝ => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (b ρ))) =
        fun b => ENNReal.ofReal (∏ ρ, ∫ y, φ ρ y ∂(fib (b ρ))) := by
      funext b
      rw [ENNReal.ofReal_prod_of_nonneg fun ρ _ => integral_nonneg (hφ ρ).2.2.2]
      simp only [hg]
    rw [this]
    exact ENNReal.continuous_ofReal.comp
      (continuous_finsetProd _ fun ρ _ => (hgc ρ).comp (continuous_apply ρ))
  have key : ∀ r > 0, ∫⁻ c in Metric.ball b r, ∫⁻ x, ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)) ∂(Fib c) =
      ∫⁻ c in Metric.ball b r, ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ)) := by
    intro r hr
    have hQ : Measurable fun (x : T → V) ρ => q (x ρ) :=
      (continuous_pi fun ρ => hq.comp (continuous_apply ρ)).measurable
    rw [← lintegral_preimage hQ isOpen_univ hFib (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ)))
      (Finset.measurable_prod _ fun ρ _ => (hm ρ).comp (measurable_pi_apply ρ))
      (fun v hv => absurd (mem_univ v) hv) _ measurableSet_ball,
      ← lintegral_indicator measurableSet_ball, ball_pi b hr]
    have e1 : ∀ x : T → V, ((fun (x : T → V) ρ => q (x ρ)) ⁻¹'
        (Set.pi univ fun ρ => Metric.ball (b ρ) r)).indicator
        (fun x => ∏ ρ, ENNReal.ofReal (φ ρ (x ρ))) x =
        ∏ ρ, (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)) (x ρ) := by
      intro x
      by_cases hx : ∀ ρ, x ρ ∈ q ⁻¹' Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    have e2 : ∀ c : T → ℝ, (Set.pi univ fun ρ => Metric.ball (b ρ) r).indicator
        (fun c => ∏ ρ, ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib (c ρ))) c =
        ∏ ρ, (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)) (c ρ) := by
      intro c
      by_cases hx : ∀ ρ, c ρ ∈ Metric.ball (b ρ) r
      · rw [indicator_of_mem (by simpa using hx)]
        exact Finset.prod_congr rfl fun ρ _ => by rw [indicator_of_mem (hx ρ)]
      · rw [indicator_of_notMem (by simpa using hx)]
        obtain ⟨ρ, hρ⟩ := not_forall.1 hx
        exact (Finset.prod_eq_zero (Finset.mem_univ ρ) (indicator_of_notMem hρ _)).symm
    simp only [e1, e2]
    rw [volume_pi, GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (q ⁻¹' Metric.ball (b ρ) r).indicator (fun y => ENNReal.ofReal (φ ρ y)))
        (fun ρ => (hm ρ).indicator (hq.measurable measurableSet_ball)),
      GlobalTheory.SnMass.Push.lintegral_fintype_prod
        (fun ρ => (Metric.ball (b ρ) r).indicator
          (fun t => ∫⁻ y, ENNReal.ofReal (φ ρ y) ∂(fib t)))
        (fun ρ => (hgm ρ).indicator measurableSet_ball)]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    rw [lintegral_indicator (s := Metric.ball (b ρ) r) measurableSet_ball]
    refine lintegral_preimage hq.measurable hU hfib _ (hm ρ) (fun v hv => ?_) _ measurableSet_ball
    rw [image_eq_zero_of_notMem_tsupport fun h => hv ((hφ ρ).2.2.1 h), ENNReal.ofReal_zero]
  have hGb := hGc.continuousAt (hB.mem_nhds hb)
  exact le_antisymm
    (le_of_lintegral_ball_eq volume _ _ b hHc.continuousAt hGb fun r hr => (key r hr).symm)
    (le_of_lintegral_ball_eq volume _ _ b hGb hHc.continuousAt key)

end GlobalTheory.FibreProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem goodTopCount_le_const_mul_log (r : ℕ) (de h x : ℝ) (hde : 0 < de) (hde1 : de ≤ 1)
    (hh : 0 ≤ h) (hL : 1 ≤ Real.log x) :
    (G.orbitWindowCount r de h x : ℝ) ≤
      (6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2) * Real.log x := by
  set L := Real.log x with hLdef
  have hu : (G.goodU de : ℝ) * de ≤ 2 := by
    unfold G.goodU
    have h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de := mul_le_mul_of_nonneg_right h1.le hde.le
    have h3 : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hT : (0 : ℝ) < 10 ^ (6 * r + 1) := by positivity
  have hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L := by
    unfold G.orbitSmallMultiplicity
    have he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        (h + 3) * 10 ^ (6 * r + 1) * L := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]; ring
    rw [he]
    have h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hG : (G.goodG' r de h x : ℝ) * de ≤
      (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L := by
    unfold G.goodG' G.goodEll
    have he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de =
        ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de)) := by
      push_cast; ring
    rw [he]
    calc _ ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * L) * (((6 * r + 1 : ℕ) : ℝ) * 2) := by
          apply mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
          positivity
      _ = _ := by ring
  have hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.logb 2 x ≤ 2 * L := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  unfold G.orbitWindowCount
  set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE : 0 < 6 * Real.exp 1 := by positivity
  have h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L := by
    rw [mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hG hE.le
  have h1' : 0 ≤ 6 * Real.exp 1 * A * L := by positivity
  have h2' : 0 ≤ (h + 3) * 2 * L := by positivity
  have hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤
      6 * Real.exp 1 * A * L + (h + 3) * 2 * L := max_le (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de)
    ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem topCount_and_lambda_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CN x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → 1 ≤ G.N1 s ∧ (G.N1 s : ℝ) ≤ CN * Real.log s.x ∧
      ∀ K : G.Consts, 1 ≤ K.La → s.x ^ s.eps ≤ G.La K s ∧
        G.La K s ≤ K.La * CN ^ 2 * Real.log s.x ^ 2 * (2 * s.x ^ s.eps) := by
  intro eps he _
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)
  set h : ℝ := 2 + 8 * eps with hh
  set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr
  refine ⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩
  intro s hs hx
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hL : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have hP : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log s.x ≤ s.x ^ s.eps := by
    have := hx1 s.x (le_trans (le_max_left _ _) hx)
    rw [one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le] at this
    exact this
  have hhG : G.hG s = h := by unfold G.hG; rw [hs]
  have hrG : G.rG s = r := by unfold G.rG G.KG; rw [hhG, hs]
  have hN1 : 1 ≤ G.N1 s := by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _
  have hN := goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith))
    (by positivity) hL
  have hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x := by unfold G.N1; rw [hhG, hrG]
  rw [← hNe] at hN
  generalize 6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2 = CN at hN ⊢
  refine ⟨hN1, hN, fun K hK => ?_⟩
  have ha : Real.log s.a = Real.log s.x + s.x ^ s.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ) := by exact_mod_cast hN1
  have hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2 := one_le_pow₀ hN1'
  have hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2 := pow_le_pow_left₀ (by linarith) hN 2
  unfold G.La
  rw [ha]
  constructor
  · have h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hK hsq
    nlinarith
  · calc K.La * (G.N1 s : ℝ) ^ 2 * (Real.log s.x + s.x ^ s.eps)
        ≤ K.La * (CN * Real.log s.x) ^ 2 * (2 * s.x ^ s.eps) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)
          have : 0 ≤ K.La := by linarith
          positivity
      _ = _ := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemIff
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare.StabPart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}
  {s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F} {k : ℕ}

theorem prP_symm (a b : v.adicCompletion F) : prP s (s.symm (a, b)) = a := by
  show (s (s.symm (a, b))).1 = a
  rw [s.apply_symm_apply]

theorem prPbar_symm (a b : v.adicCompletion F) : prPbar s (s.symm (a, b)) = b := by
  show (s (s.symm (a, b))).2 = b
  rw [s.apply_symm_apply]

theorem map_mulVec_bc {A K : Type} [CommRing A] [CommRing K] (p : A →+* K) (g : GL (Fin k) A)
    (x : Fin k → A) :
    (fun i => p (((g : Matrix (Fin k) (Fin k) A) *ᵥ x) i)) =
      ((bc p g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) *ᵥ fun j => p (x j) :=
  funext fun _ => RingHom.map_mulVec p _ _ _

theorem mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (x : Fin k → E ⊗[F] v.adicCompletion F) :
    x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧
      (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ := by
  rw [mem_partOf _ (sur_prP hs), mem_partOf _ (sur_prPbar hs)]
  refine ⟨fun hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩, ?_⟩
  rintro ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩
  have h1 : s.symm (1, 0) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩)
  have h2 : s.symm (0, 1) ∈ intV E v :=
    (hs.2.2 _).2 (by rw [s.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩)
  have hx : x = (⟨_, h1⟩ : intV E v) • a + (⟨_, h2⟩ : intV E v) • b := by
    funext i
    show x i = s.symm (1, 0) * a i + s.symm (0, 1) * b i
    apply s.injective
    have e1 : (s (a i)).1 = (s (x i)).1 := congrFun ha' i
    have e2 : (s (b i)).2 = (s (x i)).2 := congrFun hb' i
    rw [map_add (f := _), map_mul, map_mul, s.apply_symm_apply, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_mul, Prod.fst_mul, one_mul, zero_mul, add_zero, e1]
    · rw [Prod.snd_add, Prod.snd_mul, Prod.snd_mul, one_mul, zero_mul, zero_add, e2]
  rw [hx]
  exact Λ.add_mem (Λ.smul_mem _ ha) (Λ.smul_mem _ hb)

theorem mulVec_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (y z : Fin k → v.adicCompletion F) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ (fun i => s.symm (y i, z i)) ∈ Λ ↔
      ((bc (prP s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ y ∈ partOf (prP s) Λ ∧
      ((bc (prPbar s) g : GL (Fin k) _) : Matrix (Fin k) (Fin k) _) *ᵥ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs, map_mulVec_bc, map_mulVec_bc]
  simp only [prP_symm, prPbar_symm]

theorem symm_mem_iff (hs : IsSplitting σ v s)
    (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F))
    (y z : Fin k → v.adicCompletion F) :
    (fun i => s.symm (y i, z i)) ∈ Λ ↔ y ∈ partOf (prP s) Λ ∧ z ∈ partOf (prPbar s) Λ := by
  rw [mem_iff hs]
  simp only [prP_symm, prPbar_symm]

theorem stabPart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (Λ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ x, x ∈ Λ ↔ (fun i => prP s (x i)) ∈ partOf (prP s) Λ ∧ (fun i => prPbar s (x i)) ∈ partOf (prPbar s) Λ) ∧ (∀ g : GL (Fin k) (E ⊗[F] v.adicCompletion F), g ∈ stabGL Λ ↔ bc (prP s) g ∈ stabGL (partOf (prP s) Λ) ∧ bc (prPbar s) g ∈ stabGL (partOf (prPbar s) Λ)) ∧ ∀ B : GL (Fin k) (E ⊗[F] v.adicCompletion F), (∀ y : Fin k → E ⊗[F] v.adicCompletion F, (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ Λ ↔ ∀ i, y i ∈ intV E v) → GlobalTheory.OverCompare.IsFrame (partOf (prP s) Λ) (bc (prP s) B) ∧ GlobalTheory.OverCompare.IsFrame (partOf (prPbar s) Λ) (bc (prPbar s) B) := by
  intro F E _ _ _ _ _ σ v s hs k Λ
  refine ⟨mem_iff hs Λ, fun g => ⟨fun hg => ⟨fun y => ?_, fun z => ?_⟩, fun hg x => ?_⟩,
    fun B hB => ⟨fun y => ?_, fun z => ?_⟩⟩
  · have h : _ ↔ _ := hg (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true] using h
  · have h : _ ↔ _ := hg (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, symm_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and] using h
  · rw [mem_iff hs Λ x, mem_iff hs Λ (_ *ᵥ x), map_mulVec_bc, map_mulVec_bc]
    exact and_congr (hg.1 _) (hg.2 _)
  · have h := hB (fun i => s.symm (y i, (0 : Fin k → v.adicCompletion F) i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, and_true, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h
  · have h := hB (fun i => s.symm ((0 : Fin k → v.adicCompletion F) i, z i))
    rw [mulVec_mem_iff hs, Matrix.mulVec_zero] at h
    simpa only [zero_mem, true_and, hs.2.2, RingEquiv.apply_symm_apply, Pi.zero_apply] using h

end GlobalTheory.OverCompare.StabPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairing
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomFin

theorem pairing_scaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  intro D cc δ δ₀ B N N' g S e p _ lam Ω r b y a hq _ _ hb
  have hphi : ∀ z : D.host.E, D.host.φ₀ z ∈ Qbar := fun z => by
    have hx : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
    exact (mem_algebraicClosure_iff).2 (hx.algHom D.host.φ₀.toRatAlgHom)

  have hlin : ∀ (c : ℂ) (z w : Fin g → ℂ), JMB.beta S.d S.Hm (c • z) w = c * JMB.beta S.d S.Hm z w := by
    intro c z w
    simp only [JMB.beta, JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set n := Ideal.absNorm cc
  have key : ∀ i, JMB.lamA lam (JMB.beta S.d S.Hm ((δ₀ / δ) • e (δ • embV D B.tor y)) (e (δ • embV D B.tor (b i))))
      = (lamC lam (δ / δ₀))⁻¹ * ((n : ℂ_[p]))⁻¹ * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
    intro i
    rw [hlin, hb]
    set z := D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)
    have hz := hphi ((hYY D y (b i) : D.host.K) : D.host.E)
    have heq : δ₀ / δ * (z / (n : ℂ)) = (((⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ : Qbar) : ℂ) := by
      have hc : (((n : Qbar)) : ℂ) = (n : ℂ) := by norm_cast
      simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, hc]
      rw [inv_div]; ring
    have hmem : δ₀ / δ * (z / (n : ℂ)) ∈ Qbar := by rw [heq]; exact SetLike.coe_mem _
    unfold JMB.lamA lamC
    rw [dite_eq_left hmem, dite_eq_left hq, dite_eq_left hz]
    have : (⟨δ₀ / δ * (z / (n : ℂ)), hmem⟩ : Qbar) = (⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ := Subtype.ext heq
    rw [this, map_mul, map_mul, map_inv₀, map_inv₀, map_natCast]
  unfold JMB.pairD pairN
  simp only [key]
  have hzc : ∀ i, JMB.zc (a i) = zc (a i) := fun i => rfl
  simp only [hzc, mul_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.MomFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLattice
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOne
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
end

