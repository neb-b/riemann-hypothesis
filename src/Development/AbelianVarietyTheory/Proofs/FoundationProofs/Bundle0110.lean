module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory

theorem norm_root_monic_le (n : ℕ) (s : Fin n → ℂ) (y : ℂ)
    (hy : y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0) : ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  have hS : 0 ≤ ∑ j, ‖s j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  by_cases h1 : ‖y‖ ≤ 1
  · linarith
  push_neg at h1
  cases n with
  | zero => simp at hy
  | succ m =>
    have hyn : y ^ (m + 1) = -∑ j, s j * y ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hy
    have hle : ‖y‖ ^ (m + 1) ≤ (∑ j, ‖s j‖) * ‖y‖ ^ m := by
      calc ‖y‖ ^ (m + 1) = ‖y ^ (m + 1)‖ := (norm_pow _ _).symm
        _ = ‖∑ j, s j * y ^ (j : ℕ)‖ := by rw [hyn, norm_neg]
        _ ≤ ∑ j, ‖s j * y ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin (m + 1), ‖s j‖ * ‖y‖ ^ m := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          gcongr
          · exact h1.le
          · exact Nat.lt_succ_iff.1 j.isLt
        _ = (∑ j, ‖s j‖) * ‖y‖ ^ m := by rw [Finset.sum_mul]
    have hpos : 0 < ‖y‖ ^ m := pow_pos (by linarith) _
    rw [pow_succ] at hle
    have : ‖y‖ ≤ ∑ j, ‖s j‖ := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hpos
      nlinarith
    linarith

end GlobalTheory

namespace GlobalTheory

theorem quotient_integral_holomorphic : ∀ (U : Set ℂ) (n : ℕ) (A D : ℂ → ℂ) (s : Fin n → ℂ → ℂ), IsOpen U → IsPreconnected U → DifferentiableOn ℂ A U → DifferentiableOn ℂ D U → (∀ j, DifferentiableOn ℂ (s j) U) → (∃ z ∈ U, D z ≠ 0) → (∀ z ∈ U, A z ^ n + ∑ j, s j z * A z ^ (j : ℕ) * D z ^ (n - j) = 0) → ∃ h : ℂ → ℂ, DifferentiableOn ℂ h U ∧ (∀ z ∈ U, A z = h z * D z) ∧ ∀ z ∈ U, h z ^ n + ∑ j, s j z * h z ^ (j : ℕ) = 0 := by
  intro U n A D s hU hUc hA hD hs ⟨z₁, hz₁U, hz₁⟩ heq
  classical
  have hiso : ∀ z₀ ∈ U, ∀ᶠ w in 𝓝[≠] z₀, D w ≠ 0 := by
    intro z₀ hz₀
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    simp only [not_not] at hcon
    have := (hD.analyticOnNhd hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hUc hz₀ hcon
    exact hz₁ (this hz₁U)
  have hroot : ∀ w ∈ U, D w ≠ 0 → (A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ) = 0 := by
    intro w hw hDw
    have hDn : D w ^ n ≠ 0 := pow_ne_zero _ hDw
    have key : D w ^ n * ((A w / D w) ^ n + ∑ j, s j w * (A w / D w) ^ (j : ℕ))
        = A w ^ n + ∑ j, s j w * A w ^ (j : ℕ) * D w ^ (n - j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      · rw [div_pow, mul_div_cancel₀ _ hDn]
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (j : ℕ) ≤ n := j.isLt.le
        have hsplit : D w ^ n = D w ^ (j : ℕ) * D w ^ (n - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hj]
        rw [hsplit, div_pow]
        field_simp
    have := heq w hw
    rw [← key] at this
    exact (mul_eq_zero.1 this).resolve_left hDn
  have hAz : ∀ w ∈ U, D w = 0 → A w = 0 := by
    intro w hw hDw
    have := heq w hw
    have hsum : ∑ j : Fin n, s j w * A w ^ (j : ℕ) * D w ^ (n - j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      rw [hDw, zero_pow (by omega : n - (j : ℕ) ≠ 0), mul_zero]
    rw [hsum, add_zero] at this
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp at this
    · exact (pow_eq_zero_iff hn.ne').1 this
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ, ∀ z, h z =
      if D z = 0 then limUnder (𝓝[≠] z) (fun w => A w / D w) else A z / D z := ⟨_, fun z => rfl⟩
  have hdiffAt : ∀ z₀ ∈ U, DifferentiableAt ℂ h z₀ := by
    intro z₀ hz₀
    have hUn : U ∈ 𝓝 z₀ := hU.mem_nhds hz₀
    by_cases hDz : D z₀ = 0
    · have h1 : ∀ᶠ w in 𝓝 z₀, w ∈ U := hUn
      have h2 : ∀ᶠ w in 𝓝 z₀, w ≠ z₀ → D w ≠ 0 := eventually_nhdsWithin_iff.1 (hiso z₀ hz₀)
      have h3 : ∀ᶠ w in 𝓝 z₀, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := by
        rw [Filter.eventually_all]
        intro j
        have hc : ContinuousAt (fun w => ‖s j w‖) z₀ :=
          ((hs j).differentiableAt hUn).continuousAt.norm
        exact hc.eventually (Iio_mem_nhds (lt_add_one _))
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and h3))
      have hsub : ∀ w ∈ Metric.ball z₀ r, w ∈ U := fun w hw => (hball w hw).1
      have hne : ∀ w ∈ Metric.ball z₀ r, w ≠ z₀ → D w ≠ 0 := fun w hw => (hball w hw).2.1
      have hsb : ∀ w ∈ Metric.ball z₀ r, ∀ j, ‖s j w‖ < ‖s j z₀‖ + 1 := fun w hw => (hball w hw).2.2
      have hfd : DifferentiableOn ℂ (fun w => A w / D w) (Metric.ball z₀ r \ {z₀}) := by
        intro w hw
        have hwU : U ∈ 𝓝 w := hU.mem_nhds (hsub w hw.1)
        exact ((hA.differentiableAt hwU).div (hD.differentiableAt hwU)
          (hne w hw.1 hw.2)).differentiableWithinAt
      have hbd : BddAbove (norm ∘ (fun w => A w / D w) '' (Metric.ball z₀ r \ {z₀})) := by
        refine ⟨1 + ∑ j, (‖s j z₀‖ + 1), ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have := GlobalTheory.norm_root_monic_le n (fun j => s j w) (A w / D w) (hroot w (hsub w hw.1) (hne w hw.1 hw.2))
        show ‖A w / D w‖ ≤ _
        refine this.trans ?_
        gcongr with j
        exact (hsb w hw.1 j).le
      have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds z₀ hr) hfd hbd
      have heqg : h =ᶠ[𝓝 z₀] Function.update (fun w => A w / D w) z₀
          (limUnder (𝓝[≠] z₀) (fun w => A w / D w)) := by
        filter_upwards [Metric.ball_mem_nhds z₀ hr] with w hw
        by_cases hw0 : w = z₀
        · subst hw0; rw [hh, if_pos hDz, Function.update_self]
        · rw [hh, if_neg (hne w hw hw0), Function.update_of_ne hw0]
      exact (hg.differentiableAt (Metric.ball_mem_nhds z₀ hr)).congr_of_eventuallyEq heqg
    · have hDc : ContinuousAt D z₀ := (hD.differentiableAt hUn).continuousAt
      have heqf : h =ᶠ[𝓝 z₀] fun w => A w / D w := by
        filter_upwards [hDc.eventually_ne hDz] with w hw
        rw [hh, if_neg hw]
      exact ((hA.differentiableAt hUn).div (hD.differentiableAt hUn) hDz).congr_of_eventuallyEq heqf
  refine ⟨h, fun z hz => (hdiffAt z hz).differentiableWithinAt, ?_, ?_⟩
  · intro z hz
    by_cases hDz : D z = 0
    · rw [hDz, mul_zero]; exact hAz z hz hDz
    · rw [hh, if_neg hDz, div_mul_cancel₀ _ hDz]
  · intro z hz
    by_cases hDz : D z = 0
    · have hUn : U ∈ 𝓝 z := hU.mem_nhds hz
      have hFd : DifferentiableAt ℂ (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) z := by
        apply ((hdiffAt z hz).pow n).add
        have hsum := DifferentiableAt.sum (u := Finset.univ)
          (A := fun (j : Fin n) (w : ℂ) => s j w * h w ^ (j : ℕ))
          (fun j _ => ((hs j).differentiableAt hUn).mul ((hdiffAt z hz).pow _))
        convert hsum using 1
        ext w
        simp [Finset.sum_apply]
      have hev : ∀ᶠ w in 𝓝[≠] z, h w ^ n + ∑ j, s j w * h w ^ (j : ℕ) = 0 := by
        filter_upwards [hiso z hz, nhdsWithin_le_nhds hUn] with w hw hwU
        rw [hh, if_neg hw]
        exact hroot w hwU hw
      have ht : Tendsto (fun w => h w ^ n + ∑ j, s j w * h w ^ (j : ℕ)) (𝓝[≠] z) (𝓝 0) :=
        tendsto_const_nhds.congr' (hev.mono fun w hw => hw.symm)
      exact tendsto_nhds_unique (hFd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ht
    · rw [hh, if_neg hDz]
      exact hroot z hz hDz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamifiedDivisibilityOfUnramifiedDivisibility
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.KZ.ramified_divisible_of_unramified : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (v : Valuation Ω ℝ≥0) (ψ : O0 p →+* Ω) (E F : ℕ) (π : Ω) (κ : Fin F → Ω), 1 ≤ E → 0 < v (p : Ω) → v (p : Ω) < 1 → v π ^ E = v (p : Ω) → (∀ j, v (κ j) ≤ 1) → (∀ y, v (ψ y) ≤ 1) → (∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 → ∀ j, (p : Lau p) ∣ b j) → ∀ b : Fin F → Fin E → Lau p, v (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s := by
  intro p _ Ω _ _ v ψ E F π κ hE hp0 hp1 hπE hκ hψ hunr b htot
  classical
  set a := algebraMap (Lau p) (O0 p) with ha
  set Y : Fin E → Ω := fun s => ∑ j, κ j * ψ (a (b j s)) with hY
  have hsum : (∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (a (b j s)))
      = ∑ s : Fin E, π ^ (s : ℕ) * Y s := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [hY, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum] at htot

  have hπpos : 0 < v π := by
    rcases eq_or_ne (v π) 0 with h | h
    · exfalso
      have : v π ^ E = 0 := by rw [h]; exact zero_pow (by omega)
      rw [hπE] at this; exact absurd this hp0.ne'
    · exact pos_iff_ne_zero.mpr h
  have hπ1 : v π < 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 1 ≤ v π ^ E := one_le_pow₀ h
    rw [hπE] at this
    exact absurd hp1 (not_lt.mpr this)
  have hπle : v π ≤ 1 := hπ1.le
  have hY1 : ∀ s, v (Y s) ≤ 1 := by
    intro s
    refine Valuation.map_sum_le v (fun j _ => ?_)
    rw [map_mul]
    calc v (κ j) * v (ψ (a (b j s))) ≤ 1 * 1 := mul_le_mul' (hκ j) (hψ _)
      _ = 1 := one_mul 1
  have hYp : ∀ s, (∀ j, (p : Lau p) ∣ b j s) → v (Y s) ≤ v (p : Ω) := by
    intro s hs
    refine Valuation.map_sum_le v (fun j _ => ?_)
    obtain ⟨c, hc⟩ := hs j
    rw [hc, map_mul, map_mul, map_natCast, map_mul, map_natCast, map_mul]
    calc v (κ j) * (v (p : Ω) * v (ψ (a c))) ≤ 1 * (v (p : Ω) * 1) :=
          mul_le_mul' (hκ j) (mul_le_mul' le_rfl (hψ _))
      _ = v (p : Ω) := by rw [one_mul, mul_one]
  have step : ∀ s : Fin E, (∀ s' : Fin E, s' < s → ∀ j, (p : Lau p) ∣ b j s') →
      ∀ j, (p : Lau p) ∣ b j s := by
    intro s ih
    have hsE : (s : ℕ) + 1 ≤ E := s.isLt
    have hpB : v (p : Ω) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [← hπE]; exact pow_le_pow_of_le_one zero_le hπle hsE
    have hrest : v (∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s') ≤ v π ^ ((s : ℕ) + 1) := by
      refine Valuation.map_sum_le v (fun s' hs' => ?_)
      have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
      rw [map_mul, map_pow]
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · calc v π ^ (s' : ℕ) * v (Y s') ≤ 1 * v (p : Ω) :=
              mul_le_mul' (pow_le_one₀ zero_le hπle) (hYp s' (ih s' hlt))
          _ ≤ v π ^ ((s : ℕ) + 1) := by rw [one_mul]; exact hpB
      · have hgt' : (s : ℕ) + 1 ≤ (s' : ℕ) := hgt
        calc v π ^ (s' : ℕ) * v (Y s') ≤ v π ^ (s' : ℕ) * 1 := mul_le_mul' le_rfl (hY1 s')
          _ = v π ^ (s' : ℕ) := mul_one _
          _ ≤ v π ^ ((s : ℕ) + 1) := pow_le_pow_of_le_one zero_le hπle hgt'
    have hsplit : π ^ (s : ℕ) * Y s
        = (∑ s' : Fin E, π ^ (s' : ℕ) * Y s') - ∑ s' ∈ Finset.univ.erase s, π ^ (s' : ℕ) * Y s' := by
      rw [← Finset.add_sum_erase Finset.univ (fun s' : Fin E => π ^ (s' : ℕ) * Y s')
        (Finset.mem_univ s)]
      ring
    have hmain : v (π ^ (s : ℕ) * Y s) ≤ v π ^ ((s : ℕ) + 1) := by
      rw [hsplit]
      refine (Valuation.map_sub v _ _).trans (max_le (htot.trans hpB) hrest)
    rw [map_mul, map_pow, pow_succ] at hmain
    have hYs : v (Y s) ≤ v π :=
      le_of_mul_le_mul_left hmain (pow_pos hπpos _)
    exact hunr (fun j => b j s) (lt_of_le_of_lt hYs hπ1)
  intro j s
  exact WellFoundedLT.induction s (fun s ih => step s ih) j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOne
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.K5.ResDisj

variable {p : ℕ} [hp : Fact p.Prime]

theorem const_of_pow_eq {f : ℕ} (hf : f ≠ 0) (a : LaurentSeries (ZMod p)) (ha : a ^ p ^ f = a) :
    a = HahnSeries.C (a.coeff 0) := by
  haveI : CharP (LaurentSeries (ZMod p)) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (HahnSeries.C : ZMod p →+* LaurentSeries (ZMod p))]; simp)
  by_contra hne
  have hb : a - HahnSeries.C (a.coeff 0) ≠ 0 := sub_ne_zero.2 hne
  have hpow : (a - HahnSeries.C (a.coeff 0)) ^ p ^ f = a - HahnSeries.C (a.coeff 0) := by
    rw [sub_pow_char_pow, ha, ← map_pow, ZMod.pow_card_pow]
  have h0 : (a - HahnSeries.C (a.coeff 0)).coeff 0 = 0 := by simp
  generalize a - HahnSeries.C (a.coeff 0) = b at hb hpow h0
  have ho := HahnSeries.order_pow b (p ^ f)
  rw [hpow, nsmul_eq_mul] at ho
  have h1 : (1 : ℤ) < ((p ^ f : ℕ) : ℤ) := by exact_mod_cast Nat.one_lt_pow hf hp.out.one_lt
  have h2 : b.order = 0 := by
    have : (((p ^ f : ℕ) : ℤ) - 1) * b.order = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact h
  exact hb (HahnSeries.coeff_order_eq_zero.1 (by rw [h2]; exact h0))

theorem coeff_rel_of_pow {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι]
    (φ : LaurentSeries (ZMod p) →+* k) {f : ℕ} (hf : f ≠ 0) (ε : ι → k) (hε : ∀ t, ε t ^ p ^ f = ε t)
    (s : Finset ι) : ∀ b : ι → LaurentSeries (ZMod p), (∀ t, t ∉ s → b t = 0) → ∑ t, ε t * φ (b t) = 0 →
      ∀ r, ∑ t, ε t * algebraMap (ZMod p) k ((b t).coeff r) = 0 := by
  classical
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) k)]; simp)
  have hC : ∀ c : ZMod p, φ (HahnSeries.C c) = algebraMap (ZMod p) k c := fun c =>
    DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) c
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hb hrel r
  by_cases hA : ∃ l : ι → ZMod p, (∀ t, t ∉ s → l t = 0) ∧ ∑ t, ε t * algebraMap (ZMod p) k (l t) = 0 ∧ ∃ u, l u = 1
  · obtain ⟨l, hl, hlr, u, hu⟩ := hA
    have hus : u ∈ s := by
      by_contra h
      rw [hl u h] at hu; exact zero_ne_one hu
    have := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => b t - HahnSeries.C (l t) * b u) ?_ ?_ r
    · simp only [HahnSeries.coeff_sub, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
        map_sub, map_mul, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr] at this
      simpa using this
    · intro t ht
      by_cases htu : t = u
      · subst htu; simp [hu]
      · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
        simp [hb t this, hl t this]
    · simp only [map_sub, map_mul, hC, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul, hlr, hrel]
      simp
  · have hb0 : ∀ u, b u = 0 := by
      intro u
      by_contra hu
      have hus : u ∈ s := by
        by_contra h
        exact hu (hb u h)
      have hq : p ^ f ≠ 0 := pow_ne_zero _ hp.out.ne_zero
      set c : ι → LaurentSeries (ZMod p) := fun t => b t * (b u)⁻¹ with hc
      have hcu : c u = 1 := mul_inv_cancel₀ hu
      have hcs : ∀ t, t ∉ s → c t = 0 := fun t ht => by simp [hc, hb t ht]
      have hcr : ∑ t, ε t * φ (c t) = 0 := by
        simp only [hc, map_mul, ← mul_assoc, ← Finset.sum_mul, hrel, zero_mul]
      have hcr' : ∑ t, ε t * φ (c t ^ p ^ f) = 0 := by
        have := congrArg (· ^ p ^ f) hcr
        simp only [sum_pow_char_pow, mul_pow, hε, zero_pow hq] at this
        simpa only [map_pow] using this
      have hi := ih (s.erase u) (Finset.erase_ssubset hus) (fun t => c t ^ p ^ f - c t) ?_ ?_
      · have hfix : ∀ t, c t ^ p ^ f = c t := by
          intro t
          rw [← sub_eq_zero]
          ext r'
          by_contra hne
          apply hA
          refine ⟨fun t' => (c t' ^ p ^ f - c t').coeff r' * ((c t ^ p ^ f - c t).coeff r')⁻¹, ?_, ?_, t,
            mul_inv_cancel₀ hne⟩
          · intro t' ht'
            simp [hcs t' ht', zero_pow hq]
          · simp only [map_mul, ← mul_assoc, ← Finset.sum_mul, hi r', zero_mul]
        apply hA
        refine ⟨fun t => (c t).coeff 0, fun t ht => by simp [hcs t ht], ?_, u, by simp [hcu]⟩
        rw [← hcr]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hC, ← const_of_pow_eq hf _ (hfix t)]
      · intro t ht
        by_cases htu : t = u
        · subst htu; simp [hcu]
        · have : t ∉ s := fun h => ht (Finset.mem_erase.2 ⟨htu, h⟩)
          simp [hcs t this, zero_pow hq]
      · simp only [map_sub, mul_sub, Finset.sum_sub_distrib, hcr, hcr', sub_self]
    simp [hb0]

theorem exists_pow_eq {k : Type} [Field k] [Algebra (ZMod p) k] {ι : Type} [Fintype ι] (ε : ι → k)
    (h : ∀ t, IsAlgebraic (ZMod p) (ε t)) : ∃ f : ℕ, f ≠ 0 ∧ ∀ t, ε t ^ p ^ f = ε t := by
  let K := IntermediateField.adjoin (ZMod p) (Set.range ε)
  haveI : FiniteDimensional (ZMod p) K :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨t, rfl⟩; exact (h t).isIntegral)
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (algebraMap (ZMod p) K)]; simp)
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  refine ⟨n, n.ne_zero, fun t => ?_⟩
  have := FiniteField.pow_card (⟨ε t, IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩⟩ : K)
  rw [hn] at this
  exact congrArg Subtype.val this

open Polynomial in
theorem exists_prim (P : ℤ_[p][X]) (hP : P ≠ 0) :
    ∃ (c : ℤ_[p]) (Q : ℤ_[p][X]), c ≠ 0 ∧ P = C c * Q ∧ Q.map (PadicInt.toZMod (p := p)) ≠ 0 := by
  classical
  letI : NormalizedGCDMonoid ℤ_[p] := Classical.arbitrary _
  refine ⟨P.content, P.primPart, by rwa [Ne, content_eq_zero_iff], P.eq_C_content_mul_primPart, ?_⟩
  intro h0
  have hd : ∀ n, (p : ℤ_[p]) ∣ P.primPart.coeff n := by
    intro n
    have := congrArg (fun Q => Q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    rwa [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at this
  exact PadicInt.prime_p.not_unit (isPrimitive_primPart P (p : ℤ_[p]) ((C_dvd_iff_dvd_coeff _ _).2 hd))

theorem coeff_lt_one : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt (p := p) x) →
    v (p : Ω) < 1 → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ →
    ∀ (d : ℕ) (e : Fin d → Ω) (a : Fin d → Lau p),
    (∀ t, IsInt (p := p) (e t) ∧ IsAlgZp (p := p) (e t)) →
    v (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) < 1 →
    ∀ r : ℤ, v (∑ t, e t * zp Ω ((a t).coeff r)) < 1 := by
  intro p hp Ω _ _ hC v hv hvp T n ψ hψ d e a he hsum r
  have hq : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hqq : IsIntegral (O0 p) (T.qq n) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hq) (by rw [Basic.qq_pow]; exact isIntegral_algebraMap)
  have hint : ∀ x, ψ x ∈ v.valuationSubring := by
    intro x
    have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
    rw [hψ.rng] at hx
    exact (hv _).2 (adjoin_le_integralClosure hqq hx)
  have hzp : ∀ z : ℤ_[p], ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
    intro z
    refine hψ.sub _ _ (fun i => ?_) (fun r hr => ?_)
    · by_cases hi : i = 0
      · simp [hi]
      · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero (by exact_mod_cast hq) hi
        simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this, HahnSeries.coeff_single_of_ne hi]
    · have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
      simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne this]
  let A := v.valuationSubring
  let k := IsLocalRing.ResidueField A
  let ρ : A →+* k := IsLocalRing.residue A
  have hρ : ∀ x : A, ρ x = 0 ↔ v (x : Ω) < 1 := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  let g : Lau p →+* A := (ψ.comp (algebraMap (Lau p) (O0 p))).codRestrict A (fun x => hint _)
  have hg : ∀ x, (g x : Ω) = ψ (algebraMap (Lau p) (O0 p) x) := fun _ => rfl
  have hp0 : (p : k) = 0 := by
    rw [← map_natCast ρ, hρ]; simpa using hvp
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero hp.out).2 hp0
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hker : RingHom.ker (LauZ.red p) ≤ RingHom.ker (ρ.comp g) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (Basic.dvd_iff_map p x).2 hx
    rw [RingHom.mem_ker, map_mul, map_natCast, hp0, zero_mul]
  let φ : LaurentSeries (ZMod p) →+* k :=
    RingHom.liftOfRightInverse (LauZ.red p) (LauZ.lift p) (LauZ.red_lift p) ⟨ρ.comp g, hker⟩
  have hφ : ∀ x, φ (LauZ.red p x) = ρ (g x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨ρ.comp g, hker⟩ x
  have hCz : ∀ z : ℤ_[p], ρ (g (HahnSeries.C z)) = algebraMap (ZMod p) k (PadicInt.toZMod z) := by
    intro z
    have h1 : LauZ.red p (HahnSeries.C z) = HahnSeries.C (PadicInt.toZMod z) := by
      ext i
      rw [LauZ.red_coeff]
      by_cases hi : i = 0
      · simp [hi]
      · simp [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne hi]
    rw [← hφ, h1]
    exact DFunLike.congr_fun (Subsingleton.elim (φ.comp HahnSeries.C) (algebraMap (ZMod p) k)) _
  let E : Fin d → A := fun t => ⟨e t, (hv _).2 (he t).1⟩
  let g0 : ℤ_[p] →+* A := g.comp HahnSeries.C
  have hg0 : (algebraMap (O0 p) Ω).comp (algebraMap ℤ_[p] (O0 p)) = A.subtype.comp g0 := by
    ext z
    have h2 : algebraMap ℤ_[p] (O0 p) z = algebraMap (Lau p) (O0 p) (HahnSeries.single 0 z) := by
      rw [IsScalarTower.algebraMap_apply ℤ_[p] (Lau p) (O0 p)]
      congr 1
      ext i
      simp [HahnSeries.algebraMap_apply']
    show algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) z) = ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z))
    rw [hzp, h2, zp]
  have halg : ∀ t, IsAlgebraic (ZMod p) (ρ (E t)) := by
    intro t
    obtain ⟨P, hP, hPe⟩ := (he t).2
    obtain ⟨c, Q, hc, rfl, hQ⟩ := exists_prim P hP
    refine ⟨_, hQ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hg0, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hPe
    have hc' : (A.subtype.comp g0) c ≠ 0 := by
      haveI : CharZero Ω := Basic.charZero_of_isClo hC
      obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc PadicInt.irreducible_p
      rw [map_mul, map_pow, map_natCast]
      exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))
    have h1 := (mul_eq_zero.1 hPe).resolve_left hc'
    have h2 : Q.eval₂ g0 (E t) = 0 := by
      apply A.subtype_injective
      rw [Polynomial.hom_eval₂, map_zero]
      exact h1
    have h3 := congrArg ρ h2
    rw [Polynomial.hom_eval₂, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← h3]
    congr 1
    ext z
    exact (hCz z).symm
  obtain ⟨f, hf, hfix⟩ := exists_pow_eq _ halg
  have hrel : ∑ t, ρ (E t) * φ (LauZ.red p (a t)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hφ, ← map_mul, ← map_sum]
    rw [hρ]
    convert hsum using 2
    exact map_sum A.subtype _ _
  have hres := coeff_rel_of_pow φ hf _ hfix Finset.univ _ (fun t ht => absurd (Finset.mem_univ t) ht) hrel r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LauZ.red_coeff, ← hCz, ← map_mul, ← map_sum] at hres
  rw [hρ] at hres
  convert hres using 2
  refine Eq.trans ?_ (map_sum A.subtype _ _).symm
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hzp]; rfl

end GlobalTheory.K5.ResDisj
end

