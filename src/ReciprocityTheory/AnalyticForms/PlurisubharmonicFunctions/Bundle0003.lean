module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMean
section
open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshMean

noncomputable section

variable {D : ℕ}

lemma mul_mp (c : ℂ) (hc : ‖c‖ = 1) : MeasurePreserving (fun ζ : ℂ => c * ζ) volume volume := by
  let f : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ c
  have hf : (fun ζ : ℂ => c * ζ) = ⇑f := rfl
  have hdet : LinearMap.det f = 1 := by
    have : LinearMap.det f = Algebra.norm ℝ c := (Algebra.norm_apply ℝ c).symm
    rw [this, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hc]
    norm_num
  refine ⟨(continuous_const.mul continuous_id).measurable, ?_⟩
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

lemma smul_mp (c : ℂ) (hc : ‖c‖ = 1) :
    MeasurePreserving (fun v : Fin D → ℂ => c • v) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume) (fun _ => mul_mp c hc)

lemma isOpen_inter_preimage {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) (y : ℝ) : IsOpen (φ ⁻¹' Iio y ∩ U) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨hx, hxU⟩
  have h := hφ x hxU y hx
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at h
  filter_upwards [h, hU.mem_nhds hxU] with x' h1 h2
  exact ⟨h1, h2⟩

lemma measurable_piecewise {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (hU : IsOpen U)
    (hφ : UpperSemicontinuousOn φ U) : Measurable (U.indicator φ) := by
  refine measurable_of_Iio fun y => ?_
  rw [Set.indicator_preimage]
  exact (isOpen_inter_preimage hU hφ y).measurableSet.union
    ((measurable_zero measurableSet_Iio).diff hU.measurableSet)

theorem subMeanValuePolydisc_holds : SubMeanPolydiscStatement := by
  intro D U φ z t hU hφ ht hK
  set K := closedBall z t with hKdef
  have hKc : IsCompact K := isCompact_closedBall z t
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hzK : z ∈ K := mem_closedBall_self ht.le
  obtain ⟨x0, -, hx0⟩ := (hφ.1.mono hK).exists_isMaxOn ⟨z, hzK⟩ hKc
  set M := φ x0 with hMdef
  have hM : ∀ x ∈ K, φ x ≤ M := fun x hx => hx0 hx
  set φU := U.indicator φ with hφUdef
  have hφUm : Measurable φU := measurable_piecewise hU hφ.1
  have hφU : ∀ x ∈ K, φU x = φ x := fun x hx => Set.indicator_of_mem (hK hx) φ
  set Φ : (Fin D → ℂ) → ENNReal := fun x => ENNReal.ofReal (M - φU x) with hΦdef
  have hΦm : Measurable Φ := ENNReal.measurable_ofReal.comp (measurable_const.sub hφUm)
  set k : (Fin D → ℂ) → ENNReal := fun v => K.indicator Φ (z + v) with hkdef
  have hkm : Measurable k := (hΦm.indicator hKm).comp (measurable_const_add z)
  have hk : ∫⁻ v, k v = ∫⁻ x in K, Φ x := by
    rw [lintegral_add_left_eq_self (fun x => K.indicator Φ x) z, lintegral_indicator hKm]
  have memK : ∀ (c : ℂ) (v : Fin D → ℂ), ‖c‖ = 1 → (z + c • v ∈ K ↔ z + v ∈ K) := by
    intro c v hc
    simp [K, mem_closedBall, dist_eq_norm, norm_smul, hc]
  have hrot : ∀ θ : ℝ, ∫⁻ v, k (circleMap 0 1 θ • v) = ∫⁻ v, k v := fun θ =>
    (smul_mp _ (by simp)).lintegral_comp hkm
  have hθ : ∀ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) ≤
      K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) := by
    intro v
    by_cases hv : z + v ∈ K
    · rw [Set.indicator_of_mem hv]
      have hvt : ‖v‖ ≤ t := by simpa [K, mem_closedBall, dist_eq_norm] using hv
      have hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • v ∈ U := by
        intro ζ hζ
        apply hK
        simp only [K, mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
        nlinarith [norm_nonneg ζ, norm_nonneg v]
      obtain ⟨hci, hsub⟩ := hφ.2 z v hdisc
      have hmemθ : ∀ θ : ℝ, z + circleMap 0 1 θ • v ∈ K := fun θ => (memK _ v (by simp)).2 hv
      have hkθ : ∀ θ : ℝ, k (circleMap 0 1 θ • v) =
          ENNReal.ofReal (M - φ (z + circleMap 0 1 θ • v)) := by
        intro θ
        simp only [k, Φ]
        rw [Set.indicator_of_mem (hmemθ θ), hφU _ (hmemθ θ)]
      have hci' : IntegrableOn (fun θ : ℝ => φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hci.1
      have hconst : IntegrableOn (fun _ : ℝ => M) (Ioc 0 (2 * π)) :=
        continuous_const.integrableOn_Ioc
      have hint : IntegrableOn (fun θ : ℝ => M - φ (z + circleMap 0 1 θ • v)) (Ioc 0 (2 * π)) :=
        hconst.sub hci'
      rw [lintegral_congr (fun θ => hkθ θ), ← ofReal_integral_eq_lintegral_ofReal hint
        (ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => sub_nonneg.2 (hM _ (hmemθ θ)))]
      apply ENNReal.ofReal_le_ofReal
      rw [integral_sub hconst hci', setIntegral_const]
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul] at hsub
      have hvol : volume.real (Ioc (0:ℝ) (2 * π)) = 2 * π := by
        simp [Real.volume_real_Ioc, two_pi_pos.le]
      rw [hvol, smul_eq_mul]
      have h2 : 0 < 2 * π := two_pi_pos
      have h3 := (le_inv_mul_iff₀ h2).1 hsub
      nlinarith
    · rw [Set.indicator_of_notMem hv]
      have h0 : ∀ θ : ℝ, k (circleMap 0 1 θ • v) = 0 := fun θ =>
        Set.indicator_of_notMem (fun h => hv ((memK _ v (by simp)).1 h)) _
      simp [h0]
  have hswap : ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) =
      ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) :=
    lintegral_lintegral_swap ((hkm.comp (by fun_prop :
      Continuous fun p : ℝ × (Fin D → ℂ) => circleMap 0 1 p.1 • p.2).measurable).aemeasurable)
  have hmain : ENNReal.ofReal (2 * π) * ∫⁻ v, k v ≤
      ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
    calc ENNReal.ofReal (2 * π) * ∫⁻ v, k v
        = ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ v, k (circleMap 0 1 θ • v) := by
          simp_rw [hrot]
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]
      _ = ∫⁻ v, ∫⁻ θ in Ioc 0 (2 * π), k (circleMap 0 1 θ • v) := hswap
      _ ≤ ∫⁻ v, K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) (z + v) :=
          lintegral_mono hθ
      _ = ENNReal.ofReal (2 * π * (M - φ z)) * volume K := by
          rw [lintegral_add_left_eq_self
            (fun x => K.indicator (fun _ => ENNReal.ofReal (2 * π * (M - φ z))) x) z,
            lintegral_indicator_const hKm]
  have hbound : ∫⁻ x in K, Φ x ≤ ENNReal.ofReal (M - φ z) * volume K := by
    rw [← hk]
    rw [ENNReal.ofReal_mul two_pi_pos.le, mul_assoc] at hmain
    rw [mul_comm (ENNReal.ofReal (2 * π)), mul_comm (ENNReal.ofReal (2 * π))] at hmain
    exact (ENNReal.mul_le_mul_iff_left (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 hmain
  have hKfin : volume K < ⊤ := measure_closedBall_lt_top
  have hKpos : 0 < volume K := measure_closedBall_pos volume z ht
  have hconstK : IntegrableOn (fun _ : Fin D → ℂ => M) K := continuous_const.continuousOn.integrableOn_compact hKc
  have hψint : IntegrableOn (fun x => M - φU x) K := by
    refine ⟨(measurable_const.sub hφUm).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ x in K, ‖M - φU x‖ₑ = ∫⁻ x in K, Φ x := by
          refine setLIntegral_congr_fun hKm (fun x hx => ?_)
          rw [Real.enorm_of_nonneg (sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))]
      _ ≤ _ := hbound
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin
  have hφint : IntegrableOn φ K := by
    refine (hconstK.sub hψint).congr_fun (fun x hx => ?_) hKm
    simp [hφU x hx]
  refine ⟨hφint, ?_⟩
  have hreal : ∫ x in K, (M - φU x) ≤ (M - φ z) * volume.real K := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hKm
      (fun x hx => sub_nonneg.2 ((hφU x hx).symm ▸ hM x hx))) hψint.aestronglyMeasurable]
    calc _ ≤ (ENNReal.ofReal (M - φ z) * volume K).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKfin).ne hbound
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 (hM z hzK))]
          rfl
  have hsplit : ∫ x in K, (M - φU x) = M * volume.real K - ∫ x in K, φ x := by
    rw [integral_sub hconstK (hφint.congr_fun (fun x hx => (hφU x hx).symm) hKm),
      setIntegral_const, smul_eq_mul, mul_comm]
    congr 1
    exact setIntegral_congr_fun hKm (fun x hx => hφU x hx)
  have hKr : 0 < volume.real K := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  rw [setAverage_eq, smul_eq_mul, le_inv_mul_iff₀ hKr]
  nlinarith [hreal, hsplit]

theorem plurisubharmonicLocallyIntegrable_holds : IsPsh_locallyIntegrableStatement := by
  intro D U φ hU hφ x hx
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)),
    (subMeanValuePolydisc_holds D U φ x (r / 2) hU hφ (half_pos hr)
      ((closedBall_subset_ball (by linarith)).trans hrU)).1⟩

end

end ReciprocityTheory.AnForm.A.PshMean

open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff

namespace ReciprocityTheory.AnForm.A.PshMol

noncomputable section

def b0 : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def g0 (D : ℕ) (w : Fin D → ℂ) : ℝ := b0 (∑ i, ‖w i‖ ^ 2)

lemma radialBump_contDiff (D : ℕ) : ContDiff ℝ ∞ (g0 D) :=
  b0.contDiff.comp (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i))

lemma radialBump_nonneg (D : ℕ) (w : Fin D → ℂ) : 0 ≤ g0 D w := b0.nonneg

lemma radialBump_support (D : ℕ) : Function.support (g0 D) ⊆ ball 0 1 := by
  intro w hw
  have h : (∑ i, ‖w i‖ ^ 2) ∈ ball (0:ℝ) (1 / 4) := by
    have := b0.support_eq ▸ (show (∑ i, ‖w i‖ ^ 2) ∈ Function.support b0 from hw)
    simpa [b0] using this
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at h
  rw [mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := le_abs_self (∑ j, ‖w j‖ ^ 2)
  nlinarith [norm_nonneg (w i)]

lemma radialBump_smul (D : ℕ) (c : ℂ) (w : Fin D → ℂ) (hc : ‖c‖ = 1) : g0 D (c • w) = g0 D w := by
  simp [g0, norm_mul, hc]

lemma radialBump_hasCompactSupport (D : ℕ) : HasCompactSupport (g0 D) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) 1) fun w hw => by
    by_contra h
    exact hw (ball_subset_closedBall (radialBump_support D h))

lemma integral_radialBump_pos (D : ℕ) : 0 < ∫ w, g0 D w :=
  (radialBump_contDiff D).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (radialBump_hasCompactSupport D)
    (radialBump_nonneg D) (by
      rw [g0, b0.one_of_mem_closedBall]
      · norm_num
      · simp [b0])

theorem circleInvariantMollifierExists_holds : MollifierInhabitStatement := fun D =>
  ⟨{ toFun := fun w => (∫ v, g0 D v)⁻¹ * g0 D w
     contDiff := contDiff_const.mul (radialBump_contDiff D)
     nonneg := fun w => mul_nonneg (inv_nonneg.2 (integral_radialBump_pos D).le) (radialBump_nonneg D w)
     support_subset := fun w hw => radialBump_support D (fun h => hw (by simp [h]))
     integral_eq_one := by
       rw [integral_const_mul, inv_mul_cancel₀ (integral_radialBump_pos D).ne']
     circle_inv := fun c w hc => by simp only [radialBump_smul D c w hc] }⟩

end

end ReciprocityTheory.AnForm.A.PshMol
end

-- bundled from ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMollA
section
namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff Convolution

noncomputable section

variable {D : ℕ}

lemma finrank_fin_complex : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex, mul_comm]

section Scaled

variable (ρ : Mollifier D)

lemma scaled_nonneg {ε : ℝ} (hε : 0 < ε) (w : Fin D → ℂ) : 0 ≤ ρ.scaled ε w :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le _)) (ρ.nonneg _)

lemma scaled_eq_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ε ≤ ‖w‖) :
    ρ.scaled ε w = 0 := by
  have : ρ.toFun (ε⁻¹ • w) = 0 := by
    by_contra h
    have h1 := ρ.support_subset h
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h1
    have h2 : ε⁻¹ * ε ≤ ε⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (inv_pos.2 hε).le
    rw [inv_mul_cancel₀ hε.ne'] at h2
    linarith
  simp [Mollifier.scaled, this]

lemma norm_lt_of_scaled_ne_zero {ε : ℝ} (hε : 0 < ε) {w : Fin D → ℂ} (hw : ρ.scaled ε w ≠ 0) :
    ‖w‖ < ε :=
  lt_of_not_ge fun h => hw (scaled_eq_zero ρ hε h)

lemma scaled_contDiff (ε : ℝ) : ContDiff ℝ ∞ (ρ.scaled ε) :=
  contDiff_const.mul (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹))

lemma scaled_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (ρ.scaled ε) :=
  HasCompactSupport.intro (isCompact_closedBall 0 ε) fun _ hw =>
    scaled_eq_zero ρ hε (le_of_lt (not_le.1 fun h => hw (mem_closedBall_zero_iff.2 h)))

lemma integral_scaled {ε : ℝ} (hε : 0 < ε) : ∫ w, ρ.scaled ε w = 1 := by
  simp only [Mollifier.scaled]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume ρ.toFun hε.le,
    finrank_fin_complex, ρ.integral_eq_one, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_pos hε _).ne']

lemma integrable_scaled {ε : ℝ} (hε : 0 < ε) : Integrable (ρ.scaled ε) :=
  (scaled_contDiff ρ ε).continuous.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε)

lemma molli_congr {ε : ℝ} (hε : 0 < ε) {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ}
    {z : Fin D → ℂ} (hz : z ∈ shrink U ε) (h : EqOn φ ψ U) :
    molli ρ ε φ z = molli ρ ε ψ z := by
  unfold molli
  congr 1
  funext w
  by_cases hw : ρ.scaled ε w = 0
  · simp [hw]
  · rw [h (hz ?_)]
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
    exact (norm_lt_of_scaled_ne_zero ρ hε hw).le

lemma conv_lip {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} {L : NNReal} (hg : LipschitzWith L g)
    (z : Fin D → ℂ) : ‖(∫ w, ρ.scaled ε w • g (z - w)) - g z‖ ≤ L * ε := by
  have hc : Continuous fun w => ρ.scaled ε w • g (z - w) :=
    (scaled_contDiff ρ ε).continuous.smul (hg.continuous.comp (continuous_const.sub continuous_id))
  have hi : Integrable fun w => ρ.scaled ε w • g (z - w) :=
    hc.integrable_of_hasCompactSupport (scaled_hasCompactSupport ρ hε).smul_right
  have hi2 : Integrable fun w => ρ.scaled ε w • g z := (integrable_scaled ρ hε).smul_const _
  have e1 : g z = ∫ w, ρ.scaled ε w • g z := by
    rw [integral_smul_const, integral_scaled ρ hε, one_smul]
  rw [e1, ← integral_sub hi hi2]
  have hb : Integrable fun w => ρ.scaled ε w * (L * ε) := (integrable_scaled ρ hε).mul_const _
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun w => ?_)).trans ?_
  · rw [← smul_sub, norm_smul, Real.norm_of_nonneg (scaled_nonneg ρ hε w)]
    by_cases hw : ρ.scaled ε w = 0
    · simp [hw]
    · refine mul_le_mul_of_nonneg_left ?_ (scaled_nonneg ρ hε w)
      have h1 := hg.dist_le_mul (z - w) z
      rw [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at h1
      calc ‖g (z - w) - g z‖ ≤ L * ‖w‖ := h1
        _ ≤ L * ε := mul_le_mul_of_nonneg_left (norm_lt_of_scaled_ne_zero ρ hε hw).le L.coe_nonneg
  · rw [integral_mul_const, integral_scaled ρ hε, one_mul]

lemma hasFDerivAt_conv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ε : ℝ} (hε : 0 < ε) {g : (Fin D → ℂ) → F} (hcg : HasCompactSupport g) (hg : ContDiff ℝ 1 g)
    (x : Fin D → ℂ) :
    HasFDerivAt (fun x => ∫ t, ρ.scaled ε t • g (x - t))
      (∫ t, ρ.scaled ε t • fderiv ℝ g (x - t)) x := by
  have h := hcg.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (integrable_scaled ρ hε).locallyIntegrable hg x
  have e1 : (ρ.scaled ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
      fun x => ∫ t, ρ.scaled ε t • g (x - t) := by
    funext y
    rw [convolution_def]
    rfl
  have e2 : (ρ.scaled ε ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin D → ℂ), volume]
      fderiv ℝ g) x = ∫ t, ρ.scaled ε t • fderiv ℝ g (x - t) := by
    rw [convolution_def]
    congr 1
  rw [e1, e2] at h
  exact h

end Scaled

lemma exists_cutoff {K U : Set (Fin D → ℂ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, ∃ χ : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      cthickening δ K ⊆ U ∧ EqOn χ 1 (cthickening (δ / 2) K) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨f, hfs, hf, hfr⟩ :=
    (isOpen_thickening (δ := δ) (E := K)).exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hg, hgr⟩ :=
    (isClosed_cthickening (δ := δ / 2) (E := K)).isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have hts : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  have hpos : ∀ x, 0 < f x + g x := by
    intro x
    have hf0 : 0 ≤ f x := (hfr (mem_range_self x)).1
    have hg0 : 0 ≤ g x := (hgr (mem_range_self x)).1
    by_cases hx : x ∈ cthickening (δ / 2) K
    · have : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hf0 (Ne.symm this)) hg0
    · have : g x ≠ 0 := by rw [← Function.mem_support, hgs]; exact hx
      exact add_pos_of_nonneg_of_pos hf0 (lt_of_le_of_ne hg0 (Ne.symm this))
  have hsupp : tsupport (fun x => f x / (f x + g x)) ⊆ cthickening δ K := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    rw [← hfs]
    intro h
    apply hx
    simp [h]
  refine ⟨δ, hδ, fun x => f x / (f x + g x), hf.div (hf.add hg) (fun x => (hpos x).ne'),
    (hK.cthickening).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hδU, hδU, ?_⟩
  intro x hx
  have hg0 : g x = 0 := Function.notMem_support.1 (by rw [hgs]; exact fun h => h hx)
  have hf0 : f x ≠ 0 := by rw [← Function.mem_support, hfs]; exact hts hx
  simp [hg0, hf0]

lemma cutoff_mul {χ φ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hts : tsupport χ ⊆ U) (hφ : ContDiffOn ℝ 3 φ U) :
    ContDiff ℝ 3 (fun x => χ x * φ x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact (contDiff_infty.1 hχ 3).contDiffAt.mul (hφ.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hts h)
    have h0 : (fun x => χ x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma mollificationSecondOrder_holds : MollificationSecondOrder := by
  intro D ρ U K φ hU hφ hK hKU
  obtain ⟨δ, hδ, χ, hχ, hχc, hχU, hδU, hχ1⟩ := exists_cutoff hK hU hKU
  set ψ : (Fin D → ℂ) → ℝ := fun x => χ x * φ x with hψ
  have hψd : ContDiff ℝ 3 ψ := cutoff_mul hU hχ hχU hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hd1 : ContDiff ℝ 2 (fderiv ℝ ψ) := hψd.fderiv_right (by norm_num)
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ ψ)) := hd1.fderiv_right (by norm_num)
  obtain ⟨L0, hL0⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψc hψd (by norm_num)
  obtain ⟨L1, hL1⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hψc.fderiv ℝ) hd1 (by norm_num)
  obtain ⟨L2, hL2⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport ((hψc.fderiv ℝ).fderiv ℝ) hd2 (by norm_num)
  have hD1 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε hψc (hψd.of_le (by norm_num)) x).fderiv
  have hD2 : ∀ ε, 0 < ε → fderiv ℝ (fun x => ∫ t, ρ.scaled ε t • fderiv ℝ ψ (x - t)) =
      fun x => ∫ t, ρ.scaled ε t • fderiv ℝ (fderiv ℝ ψ) (x - t) := fun ε hε =>
    funext fun x => (hasFDerivAt_conv ρ hε (hψc.fderiv ℝ) (hd1.of_le (by norm_num)) x).fderiv
  set C : ℝ := max (max (L0 : ℝ) L1) L2 with hC
  refine ⟨C, δ / 4, by positivity, fun ε hε hεδ z hz => ?_⟩
  have hzU : z ∈ shrink U ε :=
    ((closedBall_subset_closedBall (by linarith : ε ≤ δ)).trans
      (closedBall_subset_cthickening hz δ)).trans hδU
  have hEq : EqOn φ ψ (cthickening (δ / 2) K) := fun y hy => by
    have : χ y = 1 := hχ1 hy
    simp [hψ, this]
  have hball : ∀ y ∈ ball z (δ / 4), closedBall y ε ⊆ cthickening (δ / 2) K := by
    intro y hy x hx
    apply closedBall_subset_cthickening hz (δ / 2)
    rw [mem_closedBall] at hx ⊢
    rw [mem_ball] at hy
    linarith [dist_triangle x y z]
  have hmol : molli ρ ε φ =ᶠ[𝓝 z] fun x => ∫ t, ρ.scaled ε t • ψ (x - t) := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 4)] with y hy
    rw [molli_congr ρ hε (hball y hy) hEq]
    simp only [molli, smul_eq_mul]
  have hφψ : φ =ᶠ[𝓝 z] ψ := by
    filter_upwards [ball_mem_nhds z (by positivity : (0 : ℝ) < δ / 2)] with y hy
    exact hEq (closedBall_subset_cthickening hz _ (ball_subset_closedBall hy))
  have hle : ∀ L : NNReal, (L : ℝ) ≤ C → (L : ℝ) * ε ≤ C * ε := fun L hL =>
    mul_le_mul_of_nonneg_right hL hε.le
  refine ⟨hzU, ?_, ?_, ?_⟩
  · rw [hmol.eq_of_nhds, hφψ.eq_of_nhds]
    have := conv_lip ρ hε hL0 z
    rw [Real.norm_eq_abs] at this
    exact this.trans (hle L0 (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rw [hmol.fderiv_eq, hφψ.fderiv_eq, hD1 ε hε]
    exact (conv_lip ρ hε hL1 z).trans (hle L1 (le_trans (le_max_right _ _) (le_max_left _ _)))
  · rw [hmol.fderiv.fderiv_eq, hφψ.fderiv.fderiv_eq, hD1 ε hε, hD2 ε hε]
    exact (conv_lip ρ hε hL2 z).trans (hle L2 (le_max_right _ _))

end

end ReciprocityTheory.AnForm.A
end

