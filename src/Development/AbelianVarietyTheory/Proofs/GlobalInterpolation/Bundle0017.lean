module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZetaLocal

lemma zeta₁_eq {s : ℂ} (hs : s ≠ 1) : riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs, mul_inv_cancel_left₀ (sub_ne_zero.2 hs)]

lemma zeta₁_eq_zero_iff (w : ℂ) : riemannZeta₁ w = 0 ↔ w ≠ 1 ∧ riemannZeta w = 0 := by
  by_cases h : w = 1
  · simp [h]
  · simp [zeta₁_eq h, sub_ne_zero.2 h, h]

lemma order_zeta₁ {w : ℂ} (hw : w ≠ 1) :
    analyticOrderNatAt riemannZeta₁ w = analyticOrderNatAt riemannZeta w := by
  have h1 : riemannZeta₁ =ᶠ[nhds w] (fun s => s - 1) * riemannZeta := by
    filter_upwards [compl_singleton_mem_nhds hw] with s hs using zeta₁_eq hs
  have h2 : AnalyticAt ℂ riemannZeta w :=
    differentiableOn_riemannZeta.analyticAt (compl_singleton_mem_nhds hw)
  have h3 : AnalyticAt ℂ (fun s : ℂ => s - 1) w := by fun_prop
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr h1, analyticOrderAt_mul h3 h2,
    h3.analyticOrderAt_eq_zero.2 (sub_ne_zero.2 hw), zero_add]

lemma order_shift (c w : ℂ) :
    analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w
      = analyticOrderNatAt riemannZeta₁ (c + w) := by
  unfold analyticOrderNatAt
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta₁) (g := fun z => c + z)
    (z₀ := w) (by fun_prop) (by simp)
  exact congrArg _ this

lemma logDeriv_zeta₁ {s : ℂ} (hs : s ≠ 1) (h0 : riemannZeta s ≠ 0) :
    deriv riemannZeta₁ s / riemannZeta₁ s = deriv riemannZeta s / riemannZeta s + 1 / (s - 1) := by
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs, zeta₁_eq hs]
  have := sub_ne_zero.2 hs
  field_simp
  ring

lemma norm_zeta₁_le (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖riemannZeta₁ (3/2 + t * I + z)‖ ≤ 5 * (|t| + 2) ^ 2 := by
  have ht := abs_nonneg t
  set w : ℂ := 3/2 + t * I + z with hw
  by_cases h : w = 1
  · rw [h, riemannZeta₁_one, norm_one]; nlinarith
  have hre : 1 / 2 ≤ w.re := by
    have := (abs_le.1 ((abs_re_le_norm z).trans hz)).1
    simp [hw]; linarith
  have htI : ‖(t : ℂ) * I‖ = |t| := by simp
  have h1 : ‖w - 1‖ ≤ |t| + 2 := by
    have : w - 1 = 1/2 + t * I + z := by rw [hw]; ring
    rw [this]
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h2 : ‖w‖ ≤ 2 * (|t| + 2) := by
    refine norm_add₃_le.trans ?_
    rw [htI]; norm_num; linarith
  have h3 := GlobalTheory.ZetaHalfPlane.norm_zeta_sub_le w (by linarith) h
  have h4 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg w]
  have e : riemannZeta₁ w = (w - 1) * (riemannZeta w - w / (w - 1)) + w := by
    have := sub_ne_zero.2 h
    rw [zeta₁_eq h]; field_simp; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have h5 : ‖w - 1‖ * ‖riemannZeta w - w / (w - 1)‖ ≤ (|t| + 2) * (4 * (|t| + 2)) :=
    mul_le_mul h1 (by linarith) (norm_nonneg _) (by linarith)
  nlinarith

lemma le_norm_zeta₁ (t : ℝ) : 1 / 6 ≤ ‖riemannZeta₁ (3/2 + t * I)‖ := by
  set w : ℂ := 3/2 + t * I with hw
  have hre : w.re = 3 / 2 := by simp [hw]
  have h : w ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have h1 := GlobalTheory.LLower.norm_LFunction_ge 1 (1 : DirichletCharacter ℂ 1) w (by rw [hre]; norm_num)
  rw [LFunction_modOne_eq, hre] at h1
  have h2 : 1 / 2 ≤ ‖w - 1‖ := by
    refine le_trans ?_ (re_le_norm _)
    rw [sub_re, hre]; norm_num
  rw [zeta₁_eq h, norm_mul]
  nlinarith

theorem logDeriv_riemannZeta_local : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → s ≠ 1 → riemannZeta s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}.Finite ∧ ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨9 * C, by positivity, fun t s hs hs1 hs0 => ?_⟩
  have hlow := le_norm_zeta₁ t
  have hup := fun z => norm_zeta₁_le t (z := z)
  set c : ℂ := 3/2 + t * I with hc
  have hd : Differentiable ℂ fun z => riemannZeta₁ (c + z) := by fun_prop
  obtain ⟨⟨hfin, -⟩, H2⟩ := H (fun z => riemannZeta₁ (c + z)) (5 * (|t| + 2) ^ 2)
    (fun z _ => hd.analyticAt z) (by
      simp only [add_zero]
      intro h; rw [h, norm_zero] at hlow; norm_num at hlow)
    (fun z hz => hup z (by simpa using hz))
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ w ≠ 1 ∧ riemannZeta w = 0}
      = (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by rw [add_sub_cancel]; exact (zeta₁_eq_zero_iff w).2 h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, (zeta₁_eq_zero_iff _).1 h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  have H3 := H2 (s - c) hs (by
    simp only [add_sub_cancel]
    exact fun h => hs0 ((zeta₁_eq_zero_iff s).1 h).2)
  rw [finsum_mem_image (add_right_injective c).injOn, ← logDeriv_zeta₁ hs1 hs0]
  have e : (∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt riemannZeta (c + w) : ℂ) / (s - (c + w)))
      = ∑ᶠ w ∈ {w : ℂ | ‖w‖ ≤ 5/6 ∧ riemannZeta₁ (c + w) = 0},
      (analyticOrderNatAt (fun z => riemannZeta₁ (c + z)) w : ℂ) / (s - c - w) := by
    refine finsum_mem_congr rfl fun w hw => ?_
    rw [order_shift, order_zeta₁ ((zeta₁_eq_zero_iff _).1 hw.2).1, sub_sub]
  rw [e]
  rw [deriv_comp_const_add] at H3
  simp only [add_sub_cancel, add_zero] at H3
  refine H3.trans ?_
  have ht := abs_nonneg t
  have hT : 2 ≤ |t| + 2 := by linarith
  set T := |t| + 2
  have hl2 : Real.log 2 ≤ Real.log T := Real.log_le_log two_pos hT
  have hl := Real.log_two_gt_d9
  have hn : 0 < ‖riemannZeta₁ c‖ := by linarith
  have h1 : 5 * T ^ 2 / ‖riemannZeta₁ c‖ ≤ T ^ 7 := by
    rw [div_le_iff₀ hn]
    have h5 : (2 : ℝ) ^ 5 ≤ T ^ 5 := by gcongr
    have h6 : 5 ≤ T ^ 5 * ‖riemannZeta₁ c‖ := by nlinarith
    calc 5 * T ^ 2 ≤ (T ^ 5 * ‖riemannZeta₁ c‖) * T ^ 2 := by gcongr
      _ = _ := by ring
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  push_cast at h2
  have : 1 + Real.log (5 * T ^ 2 / ‖riemannZeta₁ c‖) ≤ 9 * Real.log T := by linarith
  nlinarith

end GlobalTheory.ZetaLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronOfLeTwoVonMangoldt
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.PerronCoeff
open GlobalTheory.PerronPsi

theorem truncated_perron_of_le_two_vonMangoldt : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (u T : ℝ), (∀ n, ‖c n‖ ≤ 2 * Λ n) → 2 ≤ T → T ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, LSeries c (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C, hC, hK⟩ := kernel_bound
  refine ⟨480 * C, by positivity, ?_⟩
  intro c u T hc hT hTu
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log u := half_le_log hu
  have hL0 : 0 < Real.log u := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by positivity
    linarith
  have hσ0 : 0 < 1 + 1 / Real.log u := by linarith
  have hc0 : c 0 = 0 := by simpa using hc 0
  have hs : LSeriesSummable c ((1 + 1 / Real.log u : ℝ) : ℂ) := by
    have hΛ : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + 1 / Real.log u : ℝ) : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ1)
    refine Summable.of_norm_bounded (hΛ.norm.mul_left 2) (fun n => ?_)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · simp
    · have hpow : 0 < (n : ℝ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ)).re := by
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (hc n) hpow.le
  have hI := interchange c hc0 T hσ0 hu0 hs
  have hS : HasSum (fun n : ℕ => c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) := by
    have e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n
        = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have : 1 ≤ u / n := by
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.le_floor_iff hu0.le).mp h2
      simp [this]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hc0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have : ¬ (1 ≤ u / n) := by
        intro h
        apply hn
        rw [le_div_iff₀ hn0, one_mul] at h
        exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor h⟩
      simp [this]
  have hD := hS.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hfac : ∀ x y z v : ℂ, x * y - z * (x * v) = x * (y - z * v) := fun _ _ _ _ => by ring
  have hp : 1 < 1 + 1 / (2 * Real.log u) := by
    have : 0 < 1 / (2 * Real.log u) := by positivity
    linarith
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hB : 0 ≤ 2 * u / T := by positivity
  have hnear : HasSum (fun n : ℕ =>
        if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)
      (∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n) := by
    have e : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
        = ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)),
          (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [hn]
  have hg := (hsumm.hasSum.mul_left (2 * C * (12 * u * Real.log u / T))).add
    (hnear.mul_left (2 * C * (16 * Real.log u)))
  have hA0 : 0 ≤ 2 * C * (12 * u * Real.log u / T) := by positivity
  have hBc0 : 0 ≤ 2 * C * (16 * Real.log u) := by positivity
  have hbound := hD.norm_le_of_bounded hg (fun n => by
    rw [hfac]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [hc0, zero_mul, norm_zero]
      refine add_nonneg (mul_nonneg hA0 (by positivity)) (mul_nonneg hBc0 ?_)
      split_ifs
      · exact w_nonneg _ hB _
      · exact le_rfl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hy : 0 < u / n := div_pos hu0 hn0
    obtain ⟨hK1, hK2⟩ := hK (u / n) (1 + 1 / Real.log u) T hy hσ0 (by linarith)
    have hE0 := norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)
          / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) - (if 1 ≤ u / n then 1 else 0))
    rw [norm_mul, norm_sub_rev]
    have hcn : ‖c n‖ ≤ 2 * Real.log n :=
      (hc n).trans (by linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)])
    have hmain := mul_le_mul_of_nonneg_right hcn hE0
    have hfar0 : 0 ≤ 2 * C * (12 * u * Real.log u / T)
        * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) := mul_nonneg hA0 (by positivity)
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have h := far_term hu hT0 hpos hC.le hE0 hK2 hfar
      have hnr : 0 ≤ 2 * C * (16 * Real.log u)
          * (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) := by
        refine mul_nonneg hBc0 ?_
        split_ifs
        · exact w_nonneg _ hB _
        · exact le_rfl
      nlinarith
    · push Not at hfar
      have h := near_term hu hT0 hC.le hE0 hK1 hK2 hfar.1 hfar.2
      have hmem : n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) := by
        rw [Finset.mem_range]
        have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
        have h2 : (n : ℝ) < ((⌊u⌋₊ + 1 + (⌊u⌋₊ + 1) : ℕ) : ℝ) := by
          push_cast
          linarith [hfar.2]
        exact_mod_cast h2
      rw [if_pos hmem]
      nlinarith)
  refine hbound.trans ?_
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)) ≤ 1 + 2 * Real.log u := by
    have h := zeta_bound hp
    have e : 1 / (1 + 1 / (2 * Real.log u) - 1) = 2 * Real.log u := by
      rw [add_sub_cancel_left, one_div_one_div]
    rwa [e] at h
  have hN : Real.log ⌊u⌋₊ ≤ Real.log u := by
    have hpos : (0 : ℝ) < ⌊u⌋₊ := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    exact Real.log_le_log hpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 + 2 * u / T * (2 * (1 + Real.log u)) := by
    have h := sum_w ⌊u⌋₊ hB
    have : 2 * u / T * (2 * (1 + Real.log ⌊u⌋₊)) ≤ 2 * u / T * (2 * (1 + Real.log u)) := by
      gcongr
    linarith
  have hX : 0 ≤ u / T := by positivity
  have hint : 0 ≤ (u / T) * Real.log u * (2 * Real.log u - 1) :=
    mul_nonneg (mul_nonneg hX hL0.le) (by linarith)
  have key : 2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
      + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))
      ≤ 480 * ((u / T) * Real.log u ^ 2 + Real.log u) := by
    nlinarith
  calc 2 * C * (12 * u * Real.log u / T) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))
        + 2 * C * (16 * Real.log u)
          * ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 * C * (12 * u * Real.log u / T) * (1 + 2 * Real.log u)
        + 2 * C * (16 * Real.log u) * (2 + 2 * u / T * (2 * (1 + Real.log u))) := by
        gcongr
    _ = C * (2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
        + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))) := by ring
    _ ≤ C * (480 * ((u / T) * Real.log u ^ 2 + Real.log u)) :=
        mul_le_mul_of_nonneg_left key hC.le
    _ = 480 * C * (u * Real.log u ^ 2 / T + Real.log u) := by ring

end GlobalTheory.PerronCoeff
end

