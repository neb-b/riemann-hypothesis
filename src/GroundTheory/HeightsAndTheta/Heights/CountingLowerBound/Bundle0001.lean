module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem CuspWeightBound.proof : CuspWeightBound.Statement := by
  intro f j' ρ rd lam NI covol h
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast h.one_le_ρ
  have hρj : (ρ : ℝ) ≤ j' := by exact_mod_cast h.ρ_le_j'
  have hrd := h.one_le_rd
  have hlam := h.lam_pos
  have hNI := h.NI_pos
  have h2fρ : (0 : ℝ) < 2 * f * ρ := by positivity
  have hsq : 0 < √(2 * f * ρ : ℝ) := Real.sqrt_pos.mpr h2fρ

  have hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ) :=
    h.covol_eq ▸ h.minkowski
  have hrdp : (0 : ℝ) < rd ^ (f * ρ) := by positivity
  have hlog := Real.log_le_log (by positivity) hmk
  rw [Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow,
    Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le] at hlog
  push_cast at hlog

  have hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := by
    have hrd0 : rd ≠ 0 := by positivity
    rw [one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]
    nlinarith

  have hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have : 0 ≤ log (2 * f * j' * rd) := by
      have h1 : (1 : ℝ) ≤ f * j' := one_le_mul_of_one_le_of_one_le hf hj
      have h2 : (1 : ℝ) ≤ f * j' * rd := one_le_mul_of_one_le_of_one_le h1 hrd
      exact Real.log_nonneg (by linarith)
    have : 0 ≤ max 0 (log (1 / lam)) := le_max_left _ _
    linarith
  have hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤
      2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have h1 : log (1 / lam) ≤ max 0 (log (1 / lam)) := le_max_right _ _
    have h2 : log (2 * f * ρ * rd) ≤ log (2 * f * j' * rd) :=
      Real.log_le_log (by positivity) (by gcongr)
    linarith
  calc -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := hρbound
    _ ≤ f * ρ * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr
    _ ≤ f * j' * (2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd)) := by
        gcongr

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem InteriorDichotomy.proof : InteriorDichotomy.Statement := by
  intro C0 C1 C2 hC0 hC1 hC2
  refine ⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩
  intro h hmu g fj La H
  obtain ⟨hg, hfj, hgexp, hLa, hlow, hup⟩ := H
  have hLa0 : 0 < La := by linarith
  have hfj0 : 0 < fj := by linarith
  have hlog3 : 0 ≤ log (3 + C2) := Real.log_nonneg (by linarith)
  have hCnn : 0 ≤ C0 * (log (3 + C2) + 2) + C1 := by positivity
  by_cases hmu0 : 0 ≤ hmu
  · have : 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La := by positivity
    linarith
  replace hmu0 : hmu < 0 := lt_of_not_ge hmu0

  have hgLa : 0 ≤ C2 * g * La := by positivity
  have hmax : max h 0 ≤ C2 * g * La := max_le (by linarith) hgLa
  have hpos : 0 < 2 + g + max h 0 := by have := le_max_right h 0; linarith
  have hgLa1 : 1 ≤ g * La := one_le_mul_of_one_le_of_one_le hg hLa
  have hstep1 : 2 + g + max h 0 ≤ (3 + C2) * (g * La) := by
    have : g ≤ g * La := le_mul_of_one_le_right (by linarith) hLa
    nlinarith
  have hLaexp : La ≤ exp La := by have := Real.add_one_le_exp La; linarith
  have hstep2 : g * La ≤ exp (2 * La) := by
    rw [show 2 * La = La + La by ring, Real.exp_add]
    exact mul_le_mul hgexp hLaexp hLa0.le (exp_pos La).le
  have hstep3 : 2 + g + max h 0 ≤ (3 + C2) * exp (2 * La) :=
    hstep1.trans (mul_le_mul_of_nonneg_left hstep2 (by linarith))
  have hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La := by
    calc log (2 + g + max h 0) ≤ log ((3 + C2) * exp (2 * La)) := Real.log_le_log hpos hstep3
      _ = log (3 + C2) + 2 * La := by
          rw [Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]
      _ ≤ (log (3 + C2) + 2) * La := by nlinarith
  have hC0log : C0 * log (2 + g + max h 0) ≤ C0 * ((log (3 + C2) + 2) * La) :=
    mul_le_mul_of_nonneg_left hlog hC0
  have hin : C0 * log (2 + g + max h 0) + C1 * La ≤ (C0 * (log (3 + C2) + 2) + C1) * La := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hin hfj0.le
  nlinarith

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Finset

noncomputable section

universe u

theorem MeanCountBound.proof : MeanCountBound.Statement := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 1 / 12 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; norm_num
  have hθ1 : θ ≤ 1 := by rw [hθ]; norm_num
  have hθ12 : 12 * θ = 1 := by rw [hθ]; norm_num
  have hr := h.r_pos
  have ha0 : a ≠ 0 := by have := h.one_le_a; omega
  set m := meanCount μ cnt r with hm
  have hm0 : 0 ≤ m := integral_nonneg (h.cnt_nonneg r)
  have hprod : ∀ j : ℕ, (12 : ℝ) ^ j * θ ^ j = 1 := fun j => by
    rw [← mul_pow, hθ12, one_pow]

  have hpt : ∀ (j : ℕ) (z : X), lam z < r → θ ^ (j + 1) * r ≤ lam z →
      cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := by
    intro j z hlt hle
    have hl := h.lam_pos z
    calc cnt r z ≤ (3 * r / lam z) ^ a := h.count r hr le_rfl z hlt
      _ ≤ (3 * 12 ^ (j + 1)) ^ a := by
        gcongr
        rw [div_le_iff₀ hl]
        calc 3 * r = 3 * 12 ^ (j + 1) * (θ ^ (j + 1) * r) := by
              linear_combination (-(3 * r)) * hprod (j + 1)
          _ ≤ 3 * 12 ^ (j + 1) * lam z := by gcongr

  have hterm : ∀ k : ℕ, (36 * 12 ^ (k + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (k + 1) * r)
      ≤ 1 / 4 * (1 / 2) ^ k * m := by
    intro k
    have hy0 : 0 < θ ^ (k + 1) := pow_pos hθ0 _
    have hy1 : θ ^ (k + 1) ≤ 1 := pow_le_one₀ hθ0.le hθ1
    rw [h.scaling _ _ hy0 hr, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hm0
    have hka : (θ ^ (k + 1)) ^ ka ≤ (θ ^ (k + 1)) ^ (3 * a) := by
      rw [← Real.rpow_natCast (θ ^ (k + 1)) (3 * a)]
      apply Real.rpow_le_rpow_of_exponent_ge hy0 hy1
      have := h.three_a_le_ka
      push_cast
      linarith
    have heq : (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a)
        = (36 * (θ ^ (k + 1)) ^ 2) ^ a := by
      rw [pow_mul, ← mul_pow]
      congr 1
      linear_combination (36 * (θ ^ (k + 1)) ^ 2) * hprod (k + 1)
    have hsq : 36 * (θ ^ (k + 1)) ^ 2 = 1 / 4 * (θ ^ 2) ^ k := by
      have : θ ^ 2 = 1 / 144 := by rw [hθ]; norm_num
      rw [← pow_mul, show (k + 1) * 2 = 2 + 2 * k by ring, pow_add, pow_mul, this]
      ring
    have hθ2 : θ ^ 2 ≤ 1 / 2 := by rw [hθ]; norm_num
    have hs1 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * (1 / 2) ^ k := by gcongr
    have hs2 : 1 / 4 * (θ ^ 2) ^ k ≤ 1 := by
      calc 1 / 4 * (θ ^ 2) ^ k ≤ 1 / 4 * 1 := by
            gcongr; exact pow_le_one₀ (by positivity) (by linarith)
        _ ≤ 1 := by norm_num
    calc (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ ka
        ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * (θ ^ (k + 1)) ^ (3 * a) := by gcongr
      _ = (1 / 4 * (θ ^ 2) ^ k) ^ a := by rw [heq, hsq]
      _ ≤ 1 / 4 * (θ ^ 2) ^ k := pow_le_of_le_one (by positivity) hs2 ha0
      _ ≤ 1 / 4 * (1 / 2) ^ k := hs1

  let S : ℕ → Set X := fun N => {z | θ ^ (N + 1) * r ≤ lam z}
  have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
    measurableSet_le measurable_const h.lam_meas
  have hSmono : Monotone S := by
    intro N M hNM z hz
    simp only [S, Set.mem_ofPred_eq] at hz ⊢
    have : θ ^ (M + 1) ≤ θ ^ (N + 1) := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    nlinarith
  have hSunion : ⋃ N, S N = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (h.lam_pos z) hr)
      (show θ < 1 by rw [hθ]; norm_num)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [S, Set.mem_ofPred_eq]
    have h1 : θ ^ (n + 1) ≤ θ ^ n := pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
    rw [lt_div_iff₀ hr] at hn
    nlinarith

  have hbound : ∀ N, ∫ z in S N, cnt r z ∂μ ≤ 36 ^ a + m / 2 := by
    intro N
    set G : X → ℝ := fun z => 36 ^ a +
      ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z with hG
    have hint : ∀ i : ℕ, Integrable (cnt (θ ^ (i + 1) * r)) μ := fun i =>
      h.integrable _ (mul_pos (pow_pos hθ0 _) hr)
    have hGi : Integrable G μ :=
      (integrable_const _).add (integrable_finsetSum _ fun i _ => (hint i).const_mul _)
    have hsum_nonneg : ∀ z, 0 ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        cnt (θ ^ (i + 1) * r) z := fun z =>
      sum_nonneg fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _)
    have hG0 : ∀ z, 0 ≤ G z := fun z => add_nonneg (by positivity) (hsum_nonneg z)
    have hle : ∀ z ∈ S N, cnt r z ≤ G z := by
      intro z hz
      simp only [S, Set.mem_ofPred_eq] at hz
      rcases le_or_gt r (lam z) with hrl | hlr
      · rw [h.zero r hr z hrl]; exact hG0 z
      classical
      have hex : ∃ j, θ ^ (j + 1) * r ≤ lam z := ⟨N, hz⟩
      set j := Nat.find hex with hj
      have hjle : j ≤ N := Nat.find_min' hex hz
      have hjspec : θ ^ (j + 1) * r ≤ lam z := Nat.find_spec hex
      rcases Nat.eq_zero_or_eq_succ_pred j with hj0 | hjs
      · calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = 36 ^ a := by rw [hj0]; norm_num
          _ ≤ G z := le_add_of_nonneg_right (hsum_nonneg z)
      · set k := j.pred
        have hk : k < N := by omega
        have hnot : ¬ θ ^ (k + 1) * r ≤ lam z := Nat.find_min hex (by omega)
        have hone : 1 ≤ cnt (θ ^ (k + 1) * r) z :=
          h.one _ (mul_pos (pow_pos hθ0 _) hr)
            (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ0.le hθ1)) z (lt_of_not_ge hnot)
        calc cnt r z ≤ (3 * 12 ^ (j + 1)) ^ a := hpt j z hlr hjspec
          _ = (36 * 12 ^ (k + 1) : ℝ) ^ a := by
              rw [hjs, Nat.succ_eq_add_one]; congr 1; ring
          _ ≤ (36 * 12 ^ (k + 1) : ℝ) ^ a * cnt (θ ^ (k + 1) * r) z :=
              le_mul_of_one_le_right (by positivity) hone
          _ ≤ ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a * cnt (θ ^ (i + 1) * r) z :=
              single_le_sum (f := fun i => (36 * 12 ^ (i + 1) : ℝ) ^ a *
                cnt (θ ^ (i + 1) * r) z)
                (fun i _ => mul_nonneg (by positivity) (h.cnt_nonneg _ _))
                (mem_range.2 hk)
          _ ≤ G z := le_add_of_nonneg_left (by positivity)
    have hGint : ∫ z, G z ∂μ = 36 ^ a + ∑ i ∈ range N,
        (36 * 12 ^ (i + 1) : ℝ) ^ a * meanCount μ cnt (θ ^ (i + 1) * r) := by
      rw [hG, integral_add (integrable_const _)
        (integrable_finsetSum _ fun i _ => (hint i).const_mul _),
        integral_finsetSum _ fun i _ => (hint i).const_mul _]
      simp [integral_const_mul, meanCount]
    have hgeo : ∑ i ∈ range N, (36 * 12 ^ (i + 1) : ℝ) ^ a *
        meanCount μ cnt (θ ^ (i + 1) * r) ≤ m / 2 := by
      calc _ ≤ ∑ i ∈ range N, 1 / 4 * (1 / 2 : ℝ) ^ i * m := sum_le_sum fun i _ => hterm i
        _ = 1 / 4 * m * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by
            rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
        _ ≤ 1 / 4 * m * 2 := by gcongr; exact sum_geometric_two_le N
        _ = m / 2 := by ring
    calc ∫ z in S N, cnt r z ∂μ ≤ ∫ z in S N, G z ∂μ :=
          setIntegral_mono_on (h.integrable r hr).integrableOn hGi.integrableOn (hSmeas N) hle
      _ ≤ ∫ z, G z ∂μ := setIntegral_le_integral hGi (ae_of_all _ hG0)
      _ ≤ 36 ^ a + m / 2 := by rw [hGint]; linarith
  have ht := tendsto_setIntegral_of_monotone hSmeas hSmono
    (by rw [hSunion]; exact (h.integrable r hr).integrableOn)
  rw [hSunion, Measure.restrict_univ] at ht
  have hfin : m ≤ 36 ^ a + m / 2 := le_of_tendsto' ht hbound
  linarith

end

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology

noncomputable section

theorem max_zero_add_le_of_nonneg {a b : ℝ} (hb : 0 ≤ b) : max 0 (a + b) ≤ max 0 a + b :=
  max_le (add_nonneg (le_max_left 0 a) hb) (by linarith [le_max_right 0 a])

theorem MeanCuspWeight.proof : MeanCuspWeight.Statement := by
  intro X _ μ U lam f j' vr rd h
  have := h.isProbability
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hfj : 0 ≤ (f : ℝ) * j' := by positivity
  have hvr0 : 0 < vr := lt_of_lt_of_le one_pos h.one_le_vr
  have hlogvr : 0 ≤ log vr := Real.log_nonneg h.one_le_vr
  have hr0 : 0 < vr ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hvr0 _
  have hlogr : log (vr ^ (-(1 / 2 : ℝ))) = -(1 / 2) * log vr := Real.log_rpow hvr0 _

  have key : ∀ z, max 0 (log (1 / lam z)) ≤
      max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr := by
    intro z
    have hl := h.lam_pos z
    have e : log (1 / lam z) = log (vr ^ (-(1 / 2 : ℝ)) / lam z) + 1 / 2 * log vr := by
      rw [Real.log_div one_ne_zero hl.ne', Real.log_div hr0.ne' hl.ne', hlogr, Real.log_one]
      ring
    rw [e]
    exact max_zero_add_le_of_nonneg (by positivity)
  set L : ℝ := log (2 * f * j' * rd) with hL
  set g : X → ℝ := fun z =>
    (f : ℝ) * j' * (2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) + L) with hg
  have hUg : ∀ z, U z ≤ g z := by
    intro z
    refine (h.U_le z).trans (mul_le_mul_of_nonneg_left ?_ hfj)
    linarith [key z]
  have hint_h := h.logPlus_integrable
  have hint : Integrable g μ :=
    (((hint_h.add (integrable_const (1 / 2 * log vr))).const_mul 2).add
      (integrable_const L)).const_mul _
  have hmono : ∫ z, U z ∂μ ≤ ∫ z, g z ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ h.U_nonneg) hint (ae_of_all _ hUg)
  have hval : ∫ z, g z ∂μ = (f : ℝ) * j' *
      (2 * ((∫ z, max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) ∂μ) + 1 / 2 * log vr) + L) := by
    have h1 : Integrable (fun z => max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr) μ :=
      hint_h.add (integrable_const _)
    have h2 : Integrable
        (fun z => 2 * (max 0 (log (vr ^ (-(1 / 2 : ℝ)) / lam z)) + 1 / 2 * log vr)) μ :=
      h1.const_mul 2
    rw [hg, integral_const_mul, integral_add h2 (integrable_const L), integral_const_mul,
      integral_add hint_h (integrable_const _), integral_const, integral_const, probReal_univ,
      one_smul, one_smul]
  rw [hval] at hmono
  refine hmono.trans (mul_le_mul_of_nonneg_left ?_ hfj)
  linarith [h.logPlus_mean]

end

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory Filter Topology Set

noncomputable section

universe u

theorem lt_max_zero_log_div_iff {t r l : ℝ} (ht : 0 < t) (hr : 0 < r) (hl : 0 < l) :
    t < max 0 (log (r / l)) ↔ l < exp (-t) * r := by
  rw [lt_max_iff, lt_log_iff_exp_lt (div_pos hr hl), lt_div_iff₀ hl, exp_neg,
    ← div_eq_inv_mul, lt_div_iff₀ (exp_pos t), mul_comm l]
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.2 ht.le)
    · exact h
  · exact Or.inr

theorem log_two_mul_pow_div_add_le {a : ℕ} {k : ℝ} (ha : 1 ≤ a) (hk : 3 * (a : ℝ) ≤ k) :
    log (2 * 36 ^ a) / k + 1 / k ≤ 3 := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hk0 : 0 < k := by linarith
  have h2 : log 2 < 1 := by have := log_two_lt_d9; norm_num at this; linarith
  have h36 : log 36 < 4 := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    have he : exp 4 = exp 1 ^ 4 := by rw [← exp_nat_mul]; norm_num
    have h := pow_lt_pow_left₀ exp_one_gt_d9 (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    rw [he]; norm_num at h ⊢; linarith
  have hlog : log (2 * 36 ^ a) = log 2 + a * log 36 := by
    rw [log_mul (by norm_num) (by positivity), log_pow]
  rw [← add_div, div_le_iff₀ hk0, hlog]
  nlinarith

theorem MeanLogPlus.proof (h1 : TailBound.Statement.{u}) : MeanLogPlus.Statement.{u} := by
  intro X _ μ lam cnt a ka r h
  have := h.isProbability
  have hk0 : 0 < ka := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast h.one_le_a
    linarith [h.three_a_le_ka]
  set F : X → ℝ := fun z => max 0 (log (r / lam z)) with hF
  have hFm : Measurable F :=
    measurable_const.max (measurable_log.comp (measurable_const.div h.lam_meas))
  have hF0 : ∀ z, 0 ≤ F z := fun z => le_max_left _ _
  set C : ℝ := 2 * 36 ^ a with hC
  have hC1 : 1 ≤ C := by rw [hC]; have : (1 : ℝ) ≤ 36 ^ a := one_le_pow₀ (by norm_num); linarith
  set x0 : ℝ := log C / ka with hx0
  have hx00 : 0 ≤ x0 := div_nonneg (log_nonneg hC1) hk0.le
  set g : ℝ → ℝ := fun t => min 1 (C * exp (-ka * t)) with hg

  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {z | t < F z} ≤ ENNReal.ofReal (g t) := by
    intro t ht
    have hset : {z | t < F z} = {z | lam z < exp (-t) * r} := by
      ext z; exact lt_max_zero_log_div_iff ht h.r_pos (h.lam_pos z)
    rw [hset, ← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    have := h1 X μ lam cnt a ka r h t (le_of_lt ht)
    simpa [hg, neg_mul] using this

  have hexp : IntegrableOn (fun t => C * exp (-ka * t)) (Ioi x0) :=
    (exp_neg_integrableOn_Ioi x0 hk0).const_mul C
  have hint : ∫ t in Ioi x0, C * exp (-ka * t) = 1 / ka := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x0]
    have : exp (-ka * x0) = C⁻¹ := by
      rw [hx0, show -ka * (log C / ka) = -log C by field_simp, exp_neg,
        exp_log (by linarith)]
    rw [this]; field_simp
  have hL : ∫⁻ z, ENNReal.ofReal (F z) ∂μ ≤ ENNReal.ofReal 3 := by
    rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hF0) hFm.aemeasurable]
    calc ∫⁻ t in Ioi 0, μ {z | t < F z}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (g t) := setLIntegral_mono' measurableSet_Ioi hpt
      _ ≤ ∫⁻ t in Ioc 0 x0 ∪ Ioi x0, ENNReal.ofReal (g t) := by
          rw [Ioc_union_Ioi_eq_Ioi hx00]
      _ ≤ (∫⁻ t in Ioc 0 x0, ENNReal.ofReal (g t)) + ∫⁻ t in Ioi x0, ENNReal.ofReal (g t) :=
          lintegral_union_le _ _ _
      _ ≤ (∫⁻ t in Ioc 0 x0, 1) + ∫⁻ t in Ioi x0, ENNReal.ofReal (C * exp (-ka * t)) :=
          add_le_add (lintegral_mono fun t => ENNReal.ofReal_le_one.2 (min_le_left _ _))
            (lintegral_mono fun t => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      _ = ENNReal.ofReal x0 + ENNReal.ofReal (1 / ka) := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero, ← hint,
            ofReal_integral_eq_lintegral_ofReal hexp
              (ae_of_all _ fun t => by positivity)]
      _ = ENNReal.ofReal (x0 + 1 / ka) := (ENNReal.ofReal_add hx00 (by positivity)).symm
      _ ≤ ENNReal.ofReal 3 :=
          ENNReal.ofReal_le_ofReal (log_two_mul_pow_div_add_le h.one_le_a h.three_a_le_ka)
  have hInt : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  refine ⟨hInt, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hL

end

end GroundTheory.Heights₂.Heights.LowerBound
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

noncomputable section

universe u

theorem ShortVectorsOrthogonal.rpow_neg_half_mul_self {vr : ℝ} (hvr : 0 < vr) :
    vr ^ (-(1 / 2 : ℝ)) * vr ^ (-(1 / 2 : ℝ)) = vr⁻¹ := by
  rw [← Real.rpow_add hvr]
  norm_num [Real.rpow_neg_one]

end

end GroundTheory.Heights₂.Heights.LowerBound
end

