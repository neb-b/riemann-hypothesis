module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
section
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace AnalyticIdentityTheoremsZetaFacts

lemma term_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ) (h : 2 * r ≤ ‖l‖) :
    ‖1 / (s - l) + 1 / l + s / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hd : ‖l‖ / 2 ≤ ‖s - l‖ := by
    have h1 := norm_sub_norm_le l s
    rw [norm_sub_rev] at h1
    linarith
  have hdpos : 0 < ‖s - l‖ := by linarith
  have hl : l ≠ 0 := norm_pos_iff.mp hl0
  have hsl : s - l ≠ 0 := norm_pos_iff.mp hdpos
  have key : 1 / (s - l) + 1 / l + s / l ^ 2 = s ^ 2 / (l ^ 2 * (s - l)) := by
    field_simp
    ring
  rw [key, norm_div, norm_mul, norm_pow, norm_pow,
    show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hl0.le, Real.rpow_natCast]
  have hden : 0 < ‖l‖ ^ 2 * (‖l‖ / 2) := mul_pos (pow_pos hl0 2) (half_pos hl0)
  calc ‖s‖ ^ 2 / (‖l‖ ^ 2 * ‖s - l‖) ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by
        apply div_le_div₀ (by positivity) _ hden
        · exact mul_le_mul_of_nonneg_left hd (by positivity)
        · exact pow_le_pow_left₀ (norm_nonneg s) hs.le 2
    _ = 2 * r ^ 2 * (‖l‖ ^ 3)⁻¹ := by
        field_simp

def zetaExcept (L : PeriodPair) (l₀ z : ℂ) : ℂ :=
  ∑' l : L.lattice, if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)

lemma hasSumLU_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦
        if l.1 = l₀ then 0 else (1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2))
      (zetaExcept L l₀) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  split_ifs
  · rw [norm_zero]
    positivity
  · exact term_bound r hr x hx l (by rw [hl]; exact hR)

lemma hasSumLU_wZeta (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ 1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (wZeta L) := by
  have hs3 : Summable fun l : L.lattice => ‖(l : ℂ)‖ ^ (-3 : ℝ) :=
    ZLattice.summable_norm_rpow L.lattice (-3) (by rw [L.finrank_lattice]; norm_num)
  refine L.hasSumLocallyUniformly_aux _ (fun r l => 2 * r ^ 2 * ‖(l : ℂ)‖ ^ (-3 : ℝ))
    (fun r _ => hs3.mul_left (2 * r ^ 2)) fun r hr => ?_
  filter_upwards [Filter.eventually_ge_atTop (2 * r)] with R hR x hx l hl
  exact term_bound r hr x hx l (by rw [hl]; exact hR)

private lemma differentiableOn_of_hasSumLocallyUniformlyOn' {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U) :
    DifferentiableOn ℂ g U := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  exact h'.differentiableOn
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU

private lemma hasDerivAt_inv_sub_add_inv_add_div_sq (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  have h2 : HasDerivAt (fun w : ℂ => (w - l)⁻¹) (-((z - l) ^ 2)⁻¹ * 1) z :=
    (hasDerivAt_inv h).comp z ((hasDerivAt_id' z).sub_const l)
  have h4 := (h2.add_const (1 / l)).add ((hasDerivAt_id' z).div_const (l ^ 2))
  have e : (fun w : ℂ => 1 / (w - l) + 1 / l + w / l ^ 2) =
      fun w => (w - l)⁻¹ + 1 / l + w / l ^ 2 := by
    funext w
    rw [one_div]
  rw [e]
  exact h4.congr_deriv (by ring)

lemma differentiableOn_zetaExcept (L : PeriodPair) (l₀ : ℂ) :
    DifferentiableOn ℂ (zetaExcept L l₀) (L.lattice \ {l₀})ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_zetaExcept L l₀).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isOpen_compl_lattice_diff
  by_cases h : (l : ℂ) = l₀
  · simp only [h, ↓reduceIte]
    exact differentiableOn_const 0
  · simp only [h, ↓reduceIte]
    intro z hz
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact ⟨l.2, h⟩
    exact (hasDerivAt_inv_sub_add_inv_add_div_sq l z hzl).differentiableAt.differentiableWithinAt

lemma zetaExcept_zero_add (L : PeriodPair) (z : ℂ) : zetaExcept L 0 z + 1 / z = wZeta L z := by
  have h1 := (hasSumLU_zetaExcept L 0).hasSum (x := z)
  have h2 := hasSum_ite_eq (0 : L.lattice) (1 / z)
  have h3 := (hasSumLU_wZeta L).hasSum (x := z)
  refine (h1.add h2).unique ?_
  convert h3 using 1
  funext l
  by_cases hl : l = 0
  · subst hl
    simp
  · have hl' : (l : ℂ) ≠ 0 := by
      intro h
      apply hl
      exact Subtype.ext h
    simp [hl, hl']

lemma zetaExcept_zero_zero (L : PeriodPair) : zetaExcept L 0 0 = 0 := by
  have h : ∀ l : L.lattice, (if (l : ℂ) = 0 then 0 else
      (1 / (0 - (l : ℂ)) + 1 / (l : ℂ) + 0 / (l : ℂ) ^ 2)) = 0 := by
    intro l
    split_ifs
    · rfl
    · rw [zero_sub, zero_div, add_zero, one_div_neg_eq_neg_one_div, neg_add_cancel]
  simp only [zetaExcept, h, tsum_zero]

lemma hasDerivAt_term (l z : ℂ) (h : z - l ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ 1 / (z - l) + 1 / l + z / l ^ 2)
      (-(1 / (z - l) ^ 2 - 1 / l ^ 2)) z := by
  exact hasDerivAt_inv_sub_add_inv_add_div_sq l z h

private lemma hasSum_deriv_of_hasSumLocallyUniformlyOn {ι : Type*} {F : ι → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ}
    (h : HasSumLocallyUniformlyOn F g U) (hF : ∀ i, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U) : HasSum (fun i => deriv (F i) z) (deriv g z) := by
  have h' : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, F i x) g Filter.atTop U := h
  have hd := h'.deriv
    (Filter.Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hF i) hU
  have hD : TendstoLocallyUniformlyOn (fun s x => ∑ i ∈ s, deriv (F i) x) (deriv g)
      Filter.atTop U := by
    refine hd.congr fun s x hx => ?_
    have he : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
      funext y
      simp [Finset.sum_apply]
    simp only [Function.comp_apply]
    rw [he, deriv_sum fun i _ => (hF i).differentiableAt (hU.mem_nhds hx)]
  exact HasSumLocallyUniformlyOn.hasSum hD hz

lemma eqOn_deriv_wZeta (L : PeriodPair) :
    Set.EqOn (deriv (wZeta L)) (fun z ↦ -(L.weierstrassP z)) (L.lattice : Set ℂ)ᶜ := by
  intro z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hF : ∀ l : L.lattice, DifferentiableOn ℂ
      (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) (L.lattice : Set ℂ)ᶜ := by
    intro l w hw
    have hwl : w - l ≠ 0 := by
      intro e
      apply hw
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt
  have hs := hasSum_deriv_of_hasSumLocallyUniformlyOn (hasSumLU_wZeta L).hasSumLocallyUniformlyOn hF hU hz
  have hder : (fun l : L.lattice =>
      deriv (fun w : ℂ => 1 / (w - (l : ℂ)) + 1 / (l : ℂ) + w / (l : ℂ) ^ 2) z) =
      fun l : L.lattice => -(1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    have hzl : z - l ≠ 0 := by
      intro e
      apply hz
      rw [sub_eq_zero.mp e]
      exact l.2
    exact (hasDerivAt_term l z hzl).deriv
  rw [hder] at hs
  exact hs.unique (L.hasSum_weierstrassP z).neg

lemma differentiableOn_wZeta (L : PeriodPair) :
    DifferentiableOn ℂ (wZeta L) (L.lattice : Set ℂ)ᶜ := by
  refine differentiableOn_of_hasSumLocallyUniformlyOn' (hasSumLU_wZeta L).hasSumLocallyUniformlyOn (fun l => ?_)
    L.isClosed_lattice.isOpen_compl
  intro w hw
  have hwl : w - l ≠ 0 := by
    intro e
    apply hw
    rw [sub_eq_zero.mp e]
    exact l.2
  exact (hasDerivAt_term l w hwl).differentiableAt.differentiableWithinAt

end AnalyticIdentityTheoremsZetaFacts

open AnalyticIdentityTheoremsZetaFacts

theorem zeta_summable : ZetaSummable := by
  intro L z
  exact (hasSumLU_wZeta L).hasSum.summable

theorem zeta_has_deriv : ZetaHasDeriv := by
  intro L z hz
  have hU : IsOpen ((L.lattice : Set ℂ)ᶜ) := L.isClosed_lattice.isOpen_compl
  have hd := (differentiableOn_wZeta L).differentiableAt (hU.mem_nhds hz)
  have := hd.hasDerivAt
  rwa [eqOn_deriv_wZeta L hz] at this

theorem zeta_odd : ZetaOdd := by
  intro L z
  unfold wZeta
  rw [← (Equiv.neg L.lattice).tsum_eq, ← tsum_neg]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, Submodule.coe_neg]
  have h1 : -z - -(l : ℂ) = -(z - l) := by ring
  rw [h1, neg_sq, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div, neg_div]
  ring

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EtaEis
section
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace Formalism.L2.Th1.F

namespace EtaEis

lemma tsum_int_telescope (a : ℤ → ℂ) (hs : Summable fun m : ℤ => a m - a (m + 1))
    (h1 : Tendsto (fun N : ℕ => a (N : ℤ)) atTop (𝓝 0))
    (h2 : Tendsto (fun N : ℕ => a (-(N : ℤ))) atTop (𝓝 0)) :
    ∑' m : ℤ, (a m - a (m + 1)) = 0 := by
  have hH : HasSum (fun N : ℕ => (a (N : ℤ) - a ((N : ℤ) + 1))
      + (a (-((N : ℤ) + 1)) - a (-((N : ℤ) + 1) + 1))) (∑' m : ℤ, (a m - a (m + 1))) := by
    exact hs.hasSum.nat_add_neg_add_one
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((a (i : ℤ) - a ((i : ℤ) + 1))
      + (a (-((i : ℤ) + 1)) - a (-((i : ℤ) + 1) + 1))) = a (-(N : ℤ)) - a (N : ℤ) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 : -((k : ℤ) + 1) + 1 = -(k : ℤ) := by ring
      rw [e1]
      push_cast
      ring
  have hlim := (h2.sub h1).congr (fun N => (hpart N).symm)
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hH.tendsto_sum_nat hlim

lemma tendsto_one_div_linear (c w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => 1 / (c + (N : ℂ) * w)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := by
    first
    | exact RCLike.tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
    | (have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
       simpa using h)
    | (rw [Metric.tendsto_atTop]
       intro ε hε
       obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
       refine ⟨K, fun n hn => ?_⟩
       have hKpos : (0 : ℝ) < 1 / ε := by positivity
       have hn' : (1 / ε : ℝ) < n := lt_of_lt_of_le hK (by exact_mod_cast hn)
       have hnpos : (0 : ℝ) < n := lt_trans hKpos hn'
       have hnorm : ‖((n : ℂ))⁻¹‖ = ((n : ℝ))⁻¹ := by simp
       rw [dist_zero_right, hnorm, inv_eq_one_div, div_lt_iff₀ hnpos]
       rw [div_lt_iff₀ hε] at hn'
       linarith)
  have h2 : Tendsto (fun N : ℕ => c * ((N : ℂ))⁻¹ + w) atTop (𝓝 (c * 0 + w)) :=
    (hinv.const_mul c).add_const w
  rw [mul_zero, zero_add] at h2
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * (c * ((N : ℂ))⁻¹ + w)⁻¹) atTop (𝓝 (0 * w⁻¹)) :=
    hinv.mul (h2.inv₀ hw)
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, ← mul_inv]
  congr 1
  linear_combination c * mul_inv_cancel₀ hN0

def tm (l x : ℂ) : ℂ := 1 / (x - l) + 1 / l + x / l ^ 2

private theorem summable_inv_sq_nat_mul_add (c w : ℂ) (hw : w ≠ 0) :
    Summable fun N : ℕ => 1 / ((N : ℂ) * w + c) ^ 2 := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ‖c‖ / ‖w‖)
  have hg : Summable fun N : ℕ => 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2) := by
    have h0 : Summable fun N : ℕ => 1 / (N : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact ((summable_nat_add_iff K).mpr h0).mul_left _
  refine (summable_nat_add_iff K).mp
    (Summable.of_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)))
  show ‖1 / (((N + K : ℕ) : ℂ) * w + c) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2)
  have hMK : K ≤ N + K := Nat.le_add_left K N
  generalize N + K = M at hMK ⊢
  have h1 : 2 * ‖c‖ / ‖w‖ < (M : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hMK)
  have h2 : 2 * ‖c‖ < (M : ℝ) * ‖w‖ := by
    exact (div_lt_iff₀ hw').mp h1
  have e : ‖(M : ℂ) * w‖ = (M : ℝ) * ‖w‖ := by
    simp
  have h4 : ‖(M : ℂ) * w‖ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := by
    calc ‖(M : ℂ) * w‖ = ‖((M : ℂ) * w + c) - c‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := norm_sub_le _ _
  rw [e] at h4
  have h3 : (M : ℝ) * ‖w‖ / 2 ≤ ‖(M : ℂ) * w + c‖ := by linarith [norm_nonneg c]
  have h5 : 0 < (M : ℝ) * ‖w‖ / 2 := by linarith [norm_nonneg c]
  have h6 : ((M : ℝ) * ‖w‖ / 2) ^ 2 ≤ ‖(M : ℂ) * w + c‖ ^ 2 := by
    rw [sq, sq]; exact mul_le_mul h3 h3 h5.le (norm_nonneg _)
  rw [norm_div, norm_one, norm_pow]
  calc 1 / ‖(M : ℂ) * w + c‖ ^ 2 ≤ 1 / ((M : ℝ) * ‖w‖ / 2) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos h5 2) h6
    _ = 4 / ‖w‖ ^ 2 * (1 / (M : ℝ) ^ 2) := by ring

lemma summable_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ) :
    Summable fun m : ℤ => 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hp : Summable fun N : ℕ => 1 / (((N : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) u hu).congr (fun N => ?_)
    simp only [Int.cast_natCast]
  have hm : Summable fun N : ℕ => 1 / (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr (fun N => ?_)
    rw [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg]
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨hp, hm⟩

private theorem tm_half_sub_tm_neg_half (u l : ℂ) :
    tm l (u / 2) - tm l (-(u / 2))
      = 1 / (u / 2 - l) - 1 / (u / 2 - (l + u)) + u * (1 / l ^ 2) := by
  unfold tm
  rw [show -(u / 2) - l = u / 2 - (l + u) by ring]
  ring

private theorem tsum_zeta_half_diff_eq_mul_tsum_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ)
    (hfib : Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) :
    ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)))
      = u * ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hq := summable_inv_sq u v hu n
  have hsplit : ∀ m : ℤ, tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))
      = (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) := by
    intro m
    rw [tm_half_sub_tm_neg_half, Int.cast_add, Int.cast_one,
      show ((m : ℂ) + 1) * u + (n : ℂ) * v = (m : ℂ) * u + (n : ℂ) * v + u by ring]
  have htel : Summable fun m : ℤ => 1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
      - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)) := by
    refine (hfib.sub (hq.mul_left u)).congr (fun m => ?_)
    rw [hsplit m]; ring
  have hlim1 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((N : ℤ) : ℂ) * u + (n : ℂ) * v)))
      atTop (𝓝 0) := by
    refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr
      (fun N => ?_)
    push_cast; congr 1; ring
  have hlim2 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v)))
      atTop (𝓝 0) := by
    refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) u hu).congr (fun N => ?_)
    push_cast; congr 1; ring
  have ht : ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
      - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) = 0 :=
    tsum_int_telescope (fun k : ℤ => 1 / (u / 2 - ((k : ℂ) * u + (n : ℂ) * v))) htel hlim1 hlim2
  have hadd : ∑' m : ℤ, ((1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2))
      = ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + ∑' m : ℤ, u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) := by
    exact htel.tsum_add (hq.mul_left u)
  rw [tsum_congr hsplit, hadd, ht, zero_add, tsum_mul_left]

lemma core (u v : ℂ) (hu : u ≠ 0)
    (hS : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) x) :
    (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2))
      - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))
      = u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hsum : Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
      - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)) := (hS _).sub (hS _)
  have hfib : ∀ n : ℤ, Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)) := by
    intro n
    exact hsum.prod_factor n
  have h1 : (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2))
      - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))
      = ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
          - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))) := by
    exact ((hS _).tsum_sub (hS _)).symm
  have h2 : ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
          - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)))
      = ∑' n : ℤ, ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
          - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) := by
    exact hsum.tsum_prod' hfib
  rw [h1, h2, ← tsum_mul_left]
  exact tsum_congr (fun n => tsum_zeta_half_diff_eq_mul_tsum_inv_sq u v hu n (hfib n))

end EtaEis

open EtaEis in
theorem etaEisenstein_of (hs : ZetaSummable) (ho : ZetaOdd) : EtaEisenstein := by
  intro L
  have hu1 : L.ω₁ ≠ 0 := by
    intro h; exact L.ω₁_div_two_notMem_lattice (by rw [h]; simp)
  have hu2 : L.ω₂ ≠ 0 := by
    intro h; exact L.ω₂_div_two_notMem_lattice (by rw [h]; simp)

  have hS2 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    refine ((L.latticeEquivProd.symm.toEquiv.summable_iff).mpr (hs L x)).congr fun p => ?_
    simp only [Function.comp, LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hZ2 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    rw [wZeta, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hS1 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    refine (((Equiv.prodComm ℤ ℤ).summable_iff).mpr (hS2 x)).congr fun p => ?_
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hZ1 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    rw [hZ2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hE1 : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
    simpa [wEta] using this
  have hE2 : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
    simpa [wEta] using this
  constructor
  · rw [hE1, ← core L.ω₁ L.ω₂ hu1 hS1, ← hZ1, ← hZ1, ho]; ring
  · have h := core L.ω₂ L.ω₁ hu2 hS2
    rw [← hZ2, ← hZ2, ho] at h
    rw [hE2]
    calc 2 * wZeta L (L.ω₂ / 2) = wZeta L (L.ω₂ / 2) - -wZeta L (L.ω₂ / 2) := by ring
      _ = _ := h
      _ = _ := by
        congr 1
        refine tsum_congr fun m => tsum_congr fun n => ?_
        rw [add_comm]

end Formalism.L2.Th1.F
end
end

