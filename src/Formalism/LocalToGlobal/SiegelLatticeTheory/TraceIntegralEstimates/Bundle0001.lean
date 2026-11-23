module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.EnergyAbsLower
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

variable {G : Type} [Group G] [MeasurableSpace G]

theorem lintegral_ge_rect {μS μS' : Measure G} [SFinite μS'] (f : G → G → ℝ≥0∞)
    (hf : Measurable (fun p : G × G => f p.1 p.2)) (E E' : Set G) (c : ℝ≥0∞)
    (h : ∀ s ∈ E, ∀ s' ∈ E', c ≤ f s s') : c * μS' E' * μS E ≤ ∫⁻ s, ∫⁻ s', f s s' ∂μS' ∂μS := by
  have hsec : ∀ s, Measurable (f s) := fun s =>
    hf.comp (by fun_prop : Measurable (fun s' : G => (s, s')))
  have hin : ∀ s ∈ E, c * μS' E' ≤ ∫⁻ s', f s s' ∂μS' := by
    intro s hs
    calc c * μS' E' ≤ c * μS' {s' | c ≤ f s s'} :=
          mul_le_mul' le_rfl (measure_mono fun s' hs' => h s hs s' hs')
      _ ≤ _ := mul_meas_ge_le_lintegral₀ (hsec s).aemeasurable c
  have hg : Measurable (fun s => ∫⁻ s', f s s' ∂μS') := hf.lintegral_prod_right'
  calc c * μS' E' * μS E ≤ c * μS' E' * μS {s | c * μS' E' ≤ ∫⁻ s', f s s' ∂μS'} :=
        mul_le_mul' le_rfl (measure_mono fun s hs => hin s hs)
    _ ≤ _ := mul_meas_ge_le_lintegral₀ hg.aemeasurable _

def folInt (Ω K : Set G) : Set G := {t | t ∈ Ω ∧ ∀ k ∈ K, k * t ∈ Ω}

theorem measure_inv_preimage {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm

theorem tendsto_ratio_ennreal {a b : ℕ → ℝ≥0∞} (hb0 : ∀ n, 0 < b n) (hbt : ∀ n, b n < ⊤)
    (hab : ∀ n, a n ≤ b n) (h : Tendsto (fun n => (a n).toReal / (b n).toReal) atTop (𝓝 1)) :
    Tendsto (fun n => a n / b n) atTop (𝓝 1) := by
  have hfin : ∀ n, a n / b n ≠ ⊤ := fun n =>
    ENNReal.div_ne_top (ne_top_of_le_ne_top (hbt n).ne (hab n)) (hb0 n).ne'
  have hfun : (fun n => a n / b n) = fun n => ENNReal.ofReal ((a n).toReal / (b n).toReal) := by
    funext n
    rw [← ENNReal.toReal_div, ENNReal.ofReal_toReal (hfin n)]
  rw [hfun, ← ENNReal.ofReal_one]
  exact ENNReal.tendsto_ofReal h

theorem liminf_lower {μS μS' : Measure G} [SFinite μS'] [MeasurableInv G]
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (Ω Ω' : ℕ → Set G) (hΩ0 : ∀ n, 0 < μS (Ω n)) (hΩt : ∀ n, μS (Ω n) < ⊤)
    (hΩ0' : ∀ n, 0 < μS' (Ω' n)) (hΩt' : ∀ n, μS' (Ω' n) < ⊤)
    (f : ℕ → G → G → ℝ≥0∞) (hf : ∀ n, Measurable (fun p : G × G => f n p.1 p.2)) (h : ℝ) (hh : 0 ≤ h)
    (key : ∀ ε : ℝ, 0 < ε → ∃ K K' : Set G,
      Tendsto (fun n => μS (folInt (Ω n) K) / μS (Ω n)) atTop (𝓝 1) ∧
      Tendsto (fun n => μS' (folInt (Ω' n) K') / μS' (Ω' n)) atTop (𝓝 1) ∧
      ∀ n s s', s⁻¹ ∈ folInt (Ω n) K → s'⁻¹ ∈ folInt (Ω' n) K' →
        ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ f n s s') :
    ENNReal.ofReal h ≤
      liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop := by
  set L := liminf (fun n => (μS (Ω n) * μS' (Ω' n))⁻¹ * ∫⁻ s, ∫⁻ s', f n s s' ∂μS' ∂μS) atTop
    with hL
  have step : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) ≤ L := by
    intro ε hε
    obtain ⟨K, K', hK, hK', hf'⟩ := key ε hε
    set c := ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2) with hc
    have hlim : Tendsto (fun n => c * ((μS (folInt (Ω n) K) / μS (Ω n)) *
        (μS' (folInt (Ω' n) K') / μS' (Ω' n)))) atTop (𝓝 c) := by
      have h1 := ENNReal.Tendsto.mul hK (Or.inl one_ne_zero) hK' (Or.inl one_ne_zero)
      have h2 := ENNReal.Tendsto.const_mul h1 (a := c) (Or.inr ENNReal.ofReal_ne_top)
      rw [mul_one, mul_one] at h2
      exact h2
    rw [hL, ← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    have hA0 := (hΩ0 n).ne'
    have hAt := (hΩt n).ne
    have hmain := lintegral_ge_rect (μS := μS) (μS' := μS') (f n) (hf n)
      {s | s⁻¹ ∈ folInt (Ω n) K} {s' | s'⁻¹ ∈ folInt (Ω' n) K'} c
      (fun s hs s' hs' => hf' n s s' hs hs')
    rw [measure_inv_preimage hinv, measure_inv_preimage hinv'] at hmain
    rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), div_eq_mul_inv, div_eq_mul_inv]
    calc c * (μS (folInt (Ω n) K) * (μS (Ω n))⁻¹ *
          (μS' (folInt (Ω' n) K') * (μS' (Ω' n))⁻¹))
        = (μS (Ω n))⁻¹ * (μS' (Ω' n))⁻¹ *
          (c * μS' (folInt (Ω' n) K') * μS (folInt (Ω n) K)) := by ring
      _ ≤ _ := mul_le_mul' le_rfl hmain
  have hcont : Continuous (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) :=
    ENNReal.continuous_ofReal.comp (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have h0 : ENNReal.ofReal ((max (Real.sqrt h - 0) 0) ^ 2) = ENNReal.ofReal h := by
    rw [sub_zero, max_eq_left (Real.sqrt_nonneg h), Real.sq_sqrt hh]
  have hg : Tendsto (fun ε : ℝ => ENNReal.ofReal ((max (Real.sqrt h - ε) 0) ^ 2)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal h)) := by
    rw [← h0]
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hg (eventually_nhdsWithin_of_forall fun ε hε => step ε hε)

end Formalism.L2.S.Pv.EnergyAbs
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.LimitMemLpAndIntegralEq
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ComplexConjugate

namespace Formalism.L2.S.Pv.SchurTens

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem enorm_sq_eq (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm]

private theorem aestronglyMeasurable_norm_sq {u : X → ℂ} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun x => ‖u x‖ ^ 2) μ := by
  exact hu.norm.pow 2

theorem memLp_two_of_lintegral {u : X → ℂ} (hu : AEStronglyMeasurable u μ) (h : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ < ⊤) :
    MemLp u 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm hu).2 ⟨aestronglyMeasurable_norm_sq hu, ?_⟩
  have e : ∀ x, ‖‖u x‖ ^ 2‖ₑ = ‖u x‖ₑ ^ 2 := fun x => by
    rw [Real.enorm_of_nonneg (by positivity), enorm_sq_eq]
  rw [hasFiniteIntegral_iff_enorm]
  simp only [e]
  exact h

theorem lintegral_sq_eq {u : X → ℂ} (hu : MemLp u 2 μ) :
    ∫ x, ‖u x‖ ^ 2 ∂μ = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h0 : 0 ≤ᵐ[μ] fun x => ‖u x‖ ^ 2 := ae_of_all _ fun x => by
    exact sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae h0 (aestronglyMeasurable_norm_sq hu.aestronglyMeasurable)]
  congr 1
  exact lintegral_congr fun x => (enorm_sq_eq (u x)).symm

private theorem norm_conj_complex (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z

theorem integrable_mul_conj {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * conj (v x)) μ := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hm : AEStronglyMeasurable (fun x => u x * conj (v x)) μ :=
    hu.aestronglyMeasurable.mul (Complex.continuous_conj.comp_aestronglyMeasurable hv.aestronglyMeasurable)
  refine (hu2.add hv2).mono hm (ae_of_all _ fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ ‖‖u x‖ ^ 2 + ‖v x‖ ^ 2‖
  rw [norm_mul, norm_conj_complex, Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖u x‖ - ‖v x‖), norm_nonneg (u x), norm_nonneg (v x),
    mul_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))]

private theorem mul_le_weighted_sq_add_half {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have ht1 : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have e : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * (a * b) + b ^ 2 / t := by
    linear_combination (t * a ^ 2 - 2 * a * b) * ht1
  linarith

theorem norm_integral_mul_conj_le {u v : X → ℂ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) {t : ℝ} (ht : 0 < t) :
    ‖∫ x, u x * conj (v x) ∂μ‖ ≤ (t * ∫ x, ‖u x‖ ^ 2 ∂μ + (∫ x, ‖v x‖ ^ 2 ∂μ) / t) / 2 := by
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).1 hv
  have hR : Integrable (fun x => (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2) μ :=
    ((hu2.const_mul t).add (hv2.div_const t)).div_const 2
  have h1 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2 ∂μ
      = (∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ) / 2 := integral_div _ _
  have h2 : ∫ x, (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) ∂μ
      = ∫ x, t * ‖u x‖ ^ 2 ∂μ + ∫ x, ‖v x‖ ^ 2 / t ∂μ :=
    integral_add (hu2.const_mul t) (hv2.div_const t)
  have h3 : ∫ x, t * ‖u x‖ ^ 2 ∂μ = t * ∫ x, ‖u x‖ ^ 2 ∂μ := integral_const_mul _ _
  have h4 : ∫ x, ‖v x‖ ^ 2 / t ∂μ = (∫ x, ‖v x‖ ^ 2 ∂μ) / t := integral_div _ _
  rw [← h4, ← h3, ← h2, ← h1]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_conj hu hv).norm hR fun x => ?_)
  show ‖u x * conj (v x)‖ ≤ (t * ‖u x‖ ^ 2 + ‖v x‖ ^ 2 / t) / 2
  rw [norm_mul, norm_conj_complex]
  exact mul_le_weighted_sq_add_half ht

private theorem lintegral_enorm_sub_limit_sq_le {f : ℕ → X → ℂ} {F : X → ℂ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) (n N : ℕ) {ε : ℝ≥0∞}
    (h : ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε) :
    ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ ≤ ε := by
  have hlim : ∀ x, Tendsto (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop (𝓝 (‖F x - f n x‖ₑ ^ 2)) := by
    intro x
    have h1 : Tendsto (fun m => f m x - f n x) atTop (𝓝 (F x - f n x)) := (hpt x).sub_const _
    have h2 : Tendsto (fun m => ‖f m x - f n x‖ₑ) atTop (𝓝 ‖F x - f n x‖ₑ) :=
      (continuous_enorm.tendsto _).comp h1
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h2
  have hmeas : ∀ m, AEMeasurable (fun x => ‖f m x - f n x‖ₑ ^ 2) μ := fun m =>
    (((hf m).sub (hf n)).enorm).pow_const 2
  have hfreq : ∃ᶠ m in atTop, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε :=
    (eventually_atTop.2 ⟨N, h⟩).frequently
  calc ∫⁻ x, ‖F x - f n x‖ₑ ^ 2 ∂μ
      = ∫⁻ x, liminf (fun m => ‖f m x - f n x‖ₑ ^ 2) atTop ∂μ :=
        lintegral_congr fun x => ((hlim x).liminf_eq).symm
    _ ≤ liminf (fun m => ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ) atTop :=
        lintegral_liminf_le' (f := fun m x => ‖f m x - f n x‖ₑ ^ 2) hmeas
    _ ≤ ε := liminf_le_of_frequently_le' hfreq

theorem limit_memLp_and_integral_eq (f : ℕ → X → ℂ) (F g : X → ℂ) (hf2 : ∀ n, MemLp (f n) 2 μ) (hFm : AEStronglyMeasurable F μ)
    (hg : MemLp g 2 μ) (hpt : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hC : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∫⁻ x, ‖f m x - f n x‖ₑ ^ 2 ∂μ ≤ ε)
    {L : ℂ} (hL : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 L)) :
    MemLp F 2 μ ∧ Integrable (fun x => F x * conj (g x)) μ ∧ ∫ x, F x * conj (g x) ∂μ = L := by
  have hfm : ∀ n, AEStronglyMeasurable (f n) μ := fun n => (hf2 n).aestronglyMeasurable
  obtain ⟨N₀, hN₀⟩ := hC 1 one_pos
  have h0 := lintegral_enorm_sub_limit_sq_le hfm hpt N₀ N₀ (hN₀ N₀ le_rfl)
  have hsub0 : MemLp (fun x => F x - f N₀ x) 2 μ :=
    memLp_two_of_lintegral (hFm.sub (hf2 N₀).aestronglyMeasurable) (lt_of_le_of_lt h0 ENNReal.one_lt_top)
  have hF : MemLp F 2 μ := by
    have hadd := hsub0.add (hf2 N₀)
    convert hadd using 1
    ext x
    simp
  have hFg : Integrable (fun x => F x * conj (g x)) μ := integrable_mul_conj hF hg
  refine ⟨hF, hFg, ?_⟩
  have hlim : Tendsto (fun n => ∫ x, f n x * conj (g x) ∂μ) atTop (𝓝 (∫ x, F x * conj (g x) ∂μ)) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨G, hGe⟩ : ∃ G, ∫ x, ‖g x‖ ^ 2 ∂μ = G := ⟨_, rfl⟩
    have hG : 0 ≤ G := by
      rw [← hGe]
      exact integral_nonneg fun x => sq_nonneg _
    have hc : 0 < G + 1 := by linarith
    have hB : 0 < δ ^ 2 / (2 * (G + 1)) := div_pos (pow_pos hδ 2) (mul_pos two_pos hc)
    obtain ⟨N, hN⟩ := hC (ENNReal.ofReal (δ ^ 2 / (2 * (G + 1)))) (ENNReal.ofReal_pos.2 hB)
    refine ⟨N, fun n hn => ?_⟩
    show dist (∫ x, f n x * conj (g x) ∂μ) (∫ x, F x * conj (g x) ∂μ) < δ
    have hsub : MemLp (fun x => F x - f n x) 2 μ := hF.sub (hf2 n)
    have hlin := lintegral_enorm_sub_limit_sq_le hfm hpt n N (hN n hn)
    have hA : ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ ^ 2 / (2 * (G + 1)) := by
      rw [lintegral_sq_eq hsub]
      exact ENNReal.toReal_le_of_le_ofReal hB.le hlin
    have ht : 0 < (G + 1) / δ := div_pos hc hδ
    have hbound := norm_integral_mul_conj_le hsub hg ht
    rw [hGe] at hbound
    have hdiff : ∫ x, F x * conj (g x) ∂μ - ∫ x, f n x * conj (g x) ∂μ
        = ∫ x, (F x - f n x) * conj (g x) ∂μ := by
      rw [← integral_sub hFg (integrable_mul_conj (hf2 n) hg)]
      congr 1
      funext x
      ring
    rw [dist_eq_norm, norm_sub_rev, hdiff]
    have hδ0 : δ ≠ 0 := hδ.ne'
    have hc0 : G + 1 ≠ 0 := hc.ne'
    have h1 : (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ ≤ δ / 2 := by
      calc (G + 1) / δ * ∫ x, ‖F x - f n x‖ ^ 2 ∂μ
          ≤ (G + 1) / δ * (δ ^ 2 / (2 * (G + 1))) := mul_le_mul_of_nonneg_left hA ht.le
        _ = δ / 2 := by field_simp
    have h2 : G / ((G + 1) / δ) < δ := by
      rw [div_div_eq_mul_div]
      rw [div_lt_iff₀ hc]
      nlinarith
    linarith
  exact tendsto_nhds_unique hlim hL

end Formalism.L2.S.Pv.SchurTens
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.PsiTrCoreApprox
section
noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.L2.S.Pv.PsiTrCore

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  valuedAdicCompletion_eq_valuation' v k

theorem valued_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = v.intValuation r := by
  rw [valued_algebraMap]
  exact valuation_of_algebraMap v r

private theorem exists_integer_approx_valuation (v : HeightOneSpectrum (𝓞 F)) (k : F) (hk : v.valuation F k ≤ 1)
    (N : ℕ) : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) k
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hY : algebraMap (𝓞 F) F y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hm
  have hvy : v.intValuation y = WithZero.exp (-(m : ℤ)) := v.intValuation_if_neg hy0
  have hX : v.intValuation x =
      v.valuation F (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) * v.intValuation y := by
    rw [← valuation_of_algebraMap (K := F) v x, ← valuation_of_algebraMap (K := F) v y, ← map_mul,
      div_mul_cancel₀ _ hY]
  have hxm : x ∈ v.asIdeal ^ m := by
    rw [← intValuation_le_pow_iff_mem, hX, ← hvy]
    exact mul_le_of_le_one_left' hk
  have hdvd : v.asIdeal ^ m ∣ Ideal.span {y} := (intValuation_le_pow_iff_dvd v y m).mp hvy.le
  obtain ⟨J, hJ⟩ := hdvd
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hJv
    have hy1 : y ∈ v.asIdeal ^ m * J := hJ ▸ Ideal.mem_span_singleton_self y
    have hy2 : y ∈ v.asIdeal ^ (m + 1) := by
      rw [pow_succ]; exact Ideal.mul_mono_right hJv hy1
    have := (intValuation_le_pow_iff_mem v y (m + 1)).mpr hy2
    rw [hvy, WithZero.exp_le_exp] at this
    omega
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJv
  have hxt : x * t ∈ Ideal.span {y} := hJ ▸ Ideal.mul_mem_mul hxm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  obtain ⟨s, i, hi, hsi⟩ := v.isMaximal.exists_inv htv
  have htt : t * (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - i ^ N := by
    have h1 : s * t = 1 - i := by linear_combination hsi
    calc t * (s * ∑ j ∈ Finset.range N, i ^ j) = (s * t) * ∑ j ∈ Finset.range N, i ^ j := by ring
      _ = 1 - i ^ N := by rw [h1, mul_neg_geom_sum]
  refine ⟨z * (s * ∑ j ∈ Finset.range N, i ^ j), ?_⟩
  set X := algebraMap (𝓞 F) F x
  set Y := algebraMap (𝓞 F) F y
  have hzF : algebraMap (𝓞 F) F z * Y = X * algebraMap (𝓞 F) F t := by
    simp only [X, Y, ← map_mul, hz]
  have httF : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F (s * ∑ j ∈ Finset.range N, i ^ j) =
      1 - algebraMap (𝓞 F) F (i ^ N) := by
    rw [← map_mul, htt, map_sub, map_one]
  have hZ : algebraMap (𝓞 F) F z = X * algebraMap (𝓞 F) F t / Y := eq_div_of_mul_eq hY hzF
  have key : X / Y - algebraMap (𝓞 F) F (z * (s * ∑ j ∈ Finset.range N, i ^ j)) =
      X / Y * algebraMap (𝓞 F) F (i ^ N) := by
    rw [map_mul, hZ]
    linear_combination (-(X / Y)) * httF
  rw [key, map_mul, valuation_of_algebraMap]
  have hIN : v.intValuation (i ^ N) ≤ WithZero.exp (-(N : ℤ)) :=
    (intValuation_le_pow_iff_mem v _ N).mpr (Ideal.pow_mem_pow hi N)
  exact (mul_le_of_le_one_left' hk).trans hIN

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a w : v.adicCompletion F)
    (ha : Valued.v a ≤ 1) (hw : w ≠ 0) (hw1 : Valued.v w ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v w := by
  have hw0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw
  obtain ⟨N, hN⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) < Valued.v w := by
    refine ⟨(-(Valued.v w).log).toNat + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hw0]
    rw [WithZero.exp_lt_exp]
    omega
  have hU : IsOpen {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} := by
    have h := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict w)).preimage
      (continuous_id.sub continuous_const : Continuous fun y : v.adicCompletion F ↦ y - a)
    have e : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} =
        (fun y : v.adicCompletion F ↦ y - a) ⁻¹'
          {x | Valued.v.restrict x < Valued.v.restrict w} := by
      ext y
      exact (Valuation.restrict_lt_iff (R := v.adicCompletion F) Valued.v).symm
    rw [e]
    exact h
  have hs : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} ∈ nhds a := by
    refine hU.mem_nhds ?_
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr hw0
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).mem_nhds hs
  simp only [Set.mem_setOf_eq] at hk
  have hak : Valued.v (a - algebraMap F (v.adicCompletion F) k) < Valued.v w := by
    rwa [Valuation.map_sub_swap]
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = a - (a - algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hak.le.trans hw1))
  obtain ⟨r, hr⟩ := exists_integer_approx_valuation v k hk1 N
  refine ⟨r, ?_⟩
  have e : a - algebraMap F (v.adicCompletion F) (r : F) =
      (a - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
    rw [map_sub, ← hr']
    ring
  rw [e]
  refine Valuation.map_add_lt _ hak ?_
  rw [valued_algebraMap]
  exact lt_of_le_of_lt hr hN

theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∀ v, Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
  classical
  have hspan : Ideal.span {n} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn
  set T := (Ideal.finite_factors hspan).toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ n ∈ v.asIdeal := fun v ↦ by
    simp [T, Set.Finite.mem_toFinset, Ideal.dvd_span_singleton]
  have hw : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (n : F) ≠ 0 := by
    intro v h
    have := valued_algebraMap_int v n
    rw [h, map_zero, intValuation_if_neg v hn] at this
    exact WithZero.exp_ne_zero this.symm
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      Valued.v (a v - algebraMap F (v.adicCompletion F) (r : F)) <
        Valued.v (algebraMap F (v.adicCompletion F) (n : F)) := fun v ↦
    exists_int_near v (a v) _ ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) (hw v)
      (by rw [valued_algebraMap_int]; exact intValuation_le_one v n)
  choose r hr using hr
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal)
    (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors)
    (fun v _ ↦ v.prime) (fun i _ j _ hij h ↦ hij (HeightOneSpectrum.ext h)) (fun i ↦ r i.1)
  refine ⟨b, fun v ↦ ?_⟩
  have hb1 : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1 := by
    rw [valued_algebraMap_int]; exact intValuation_le_one v b
  by_cases hv : v ∈ T
  · have h1 := (hr v).le
    rw [valued_algebraMap_int] at h1
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (r v : F) -
        algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
      rw [← map_sub, show (r v : F) - (b : F) = ((r v - b : 𝓞 F) : F) from
        (map_sub (algebraMap (𝓞 F) F) _ _).symm, valued_algebraMap_int, ← Valuation.map_neg,
        neg_sub, intValuation_if_neg v hn]
      exact (intValuation_le_pow_iff_mem v _ _).mpr (hb v hv)
    have e : a v - algebraMap F (v.adicCompletion F) (b : F) =
        (a v - algebraMap F (v.adicCompletion F) (r v : F)) +
          (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
  · have hn1 : v.intValuation n = 1 := le_antisymm (intValuation_le_one v n)
      (not_lt.mp fun h ↦ hv ((hmemT v).mpr ((intValuation_lt_one_iff_mem v n).mp h)))
    rw [hn1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) hb1)

theorem exists_decomp (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (n : F) * c := by
  obtain ⟨b, hb⟩ := exists_approx a ha n hn
  have hnF : (n : F) ≠ 0 := by
    have := (IsFractionRing.injective (𝓞 F) F).ne hn
    rwa [map_zero] at this
  have hA : ∀ (k : F) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k :=
    fun k v ↦ rfl
  refine ⟨b, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹) *
    (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)), fun v ↦ ?_, ?_⟩
  · rw [mem_adicCompletionIntegers]
    change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹)) v *
      (a v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)) v)) ≤ 1
    rw [hA, hA, map_mul, map_inv₀, map_inv₀, valued_algebraMap_int]
    have hne : v.intValuation n ≠ 0 := by
      rw [intValuation_if_neg v hn]; exact WithZero.exp_ne_zero
    calc (v.intValuation n)⁻¹ * Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F))
        ≤ (v.intValuation n)⁻¹ * v.intValuation n := by
          have hbv := hb v
          gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hnF, map_one, one_mul]
    ring

end Formalism.L2.S.Pv.PsiTrCore
end
end

