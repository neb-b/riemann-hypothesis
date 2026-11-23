module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentMonomialOfMultiplicative
section
open Matrix

namespace GlobalTheory

theorem laurentMonomial_of_multiplicative :
    ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 →
      (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) →
      (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) →
      ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  intro n χ h1 hmul hk
  choose k hk using hk
  refine ⟨k, fun d hd => ?_⟩
  have hne : ∀ (s : Finset (Fin n)) (i : Fin n), (∏ j ∈ s, Pi.mulSingle j (d j)) i ≠ 0 := by
    intro s i
    rw [Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [Pi.mulSingle_apply]
    split_ifs with h
    · subst h; exact hd _
    · exact one_ne_zero
  have key : ∀ s : Finset (Fin n), χ (∏ i ∈ s, Pi.mulSingle i (d i)) = ∏ i ∈ s, d i ^ k i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul _ _ ?_ (hne s), hk a (d a) (hd a), ih]
      intro i
      rw [Pi.mulSingle_apply]
      split_ifs with h
      · subst h; exact hd _
      · exact one_ne_zero
  have := key Finset.univ
  rwa [Finset.univ_prod_mulSingle] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LaurentPolyEvalOfLaurent
section
open Matrix

namespace GlobalTheory

theorem laurent_poly_eval_of_laurent :
    ∀ (σ : Type) (g : σ → ℂ → ℂ), (∀ a, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 → t ^ N * g a t = p.eval t) →
      ∀ Q : MvPolynomial σ ℂ, ∃ (N : ℕ) (p : Polynomial ℂ), ∀ t : ℂ, t ≠ 0 →
        t ^ N * MvPolynomial.eval (fun a => g a t) Q = p.eval t := by
  intro σ g hg Q
  induction Q using MvPolynomial.induction_on
  · rename_i c
    exact ⟨0, Polynomial.C c, fun t _ => by simp⟩
  · rename_i p q hp hq
    obtain ⟨N₁, P₁, h₁⟩ := hp
    obtain ⟨N₂, P₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, Polynomial.X ^ N₂ * P₁ + Polynomial.X ^ N₁ * P₂, fun t ht => ?_⟩
    simp only [map_add (f := _), Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← h₁ t ht, ← h₂ t ht]
    ring
  · rename_i p a hp
    obtain ⟨N, P, h⟩ := hp
    obtain ⟨N', P', h'⟩ := hg a
    refine ⟨N + N', P * P', fun t ht => ?_⟩
    simp only [map_mul, MvPolynomial.eval_X, Polynomial.eval_mul]
    rw [← h t ht, ← h' t ht]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanes
section
open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneLocBound

lemma isOpen_offHyperplanes (n a : ℕ) (ρ : ℝ) :
    IsOpen {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
  have : {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      ball 0 ρ ∩ ⋂ k ∈ (Finset.univ.filter fun k : Fin n => (k : ℕ) < a),
        (fun z : Fin n → ℂ => z k) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [this]
  exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
    (continuous_apply k).isOpen_preimage _ isOpen_compl_singleton)

lemma prod_update_eq {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℕ) (k : Fin n) (t : ℂ) :
    ∏ j, ‖Function.update z k t j‖ ^ m j =
      ‖t‖ ^ m k * ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma norm_le_of_circle {n a : ℕ} {ρ r : ℝ} {Φ : (Fin n → ℂ) → ℂ} {m : Fin n → ℕ}
    (hext : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t)
    (hΦ : DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0})
    (hgr : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1)
    {z₀ z : Fin n → ℂ} (hr : 0 < r) (hsub : ball z₀ (2 * r) ⊆ ball 0 ρ)
    (hz : z ∈ closedBall z₀ r) (hgen : ∀ j, z j ≠ 0) {k : Fin n} (hk0 : z₀ k = 0)
    {B : ℝ} (hB : ∀ t : ℂ, ‖t‖ = r → ‖Φ (Function.update z k t)‖ ≤ B) : ‖Φ z‖ ≤ B := by
  set H : ℂ → ℂ := fun t => Φ (Function.update z k t) with hH
  have hmem : ∀ t ∈ ball (0 : ℂ) (2 * r), Function.update z k t ∈ ball z₀ (2 * r) := by
    intro t ht
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj; simpa [hk0] using ht
    · rw [Function.update_of_ne hj]
      exact lt_of_le_of_lt ((dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)) (by linarith)
  have hU : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 → Function.update z k t ∈
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    intro t ht ht0
    refine ⟨hsub (hmem t ht), fun j _ => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using ht0
    · rw [Function.update_of_ne hj]; exact hgen j
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) (2 * r) \ {0}) := by
    intro t ht
    have hd := (hΦ _ (hU t ht.1 ht.2)).differentiableAt
      ((isOpen_offHyperplanes n a ρ).mem_nhds (hU t ht.1 ht.2))
    exact (hd.comp t (hasFDerivAt_update z t).differentiableAt).differentiableWithinAt
  set P := ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hgen j)) _
  have hHg : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ m k ≤ 1 / P := by
    intro t ht ht0
    have h1 := hgr _ (hU t ht ht0).1 (hU t ht ht0).2
    rw [prod_update_eq, ← mul_assoc] at h1
    exact (le_div_iff₀ hP).2 h1
  obtain ⟨G, hGd, hGH⟩ := hext H (2 * r) (1 / P) (m k) (by linarith) hHd hHg
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hzk : z k ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall]
    have := dist_le_pi_dist z z₀ k
    rw [hk0] at this
    exact this.trans (mem_closedBall.1 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hGd.diffContOnCl_ball hcl) (C := B) ?_ (by rw [closure_ball 0 hr.ne']; exact hzk)
  · rw [hGH _ (hcl hzk) (hgen k)] at key
    simpa [H] using key
  · intro t ht
    rw [frontier_ball 0 hr.ne', mem_sphere, dist_zero_right] at ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; linarith
    have htb : t ∈ ball (0 : ℂ) (2 * r) := by rw [mem_ball, dist_zero_right]; linarith
    rw [hGH t htb ht0]
    exact hB t ht

theorem locally_bounded : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  intro hext n a ρ Φ m hρ hΦ hgr z₀ hz₀
  have hUo := isOpen_offHyperplanes n a ρ
  have hδ : 0 < ρ - ‖z₀‖ := by rw [mem_ball, dist_zero_right] at hz₀; linarith
  obtain ⟨r, hr0, hrδ, hrk⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ρ - ‖z₀‖ ∧ ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρ - ‖z₀‖ := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
      exact this.eventually (gt_mem_nhds hδ)
    have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
      rw [eventually_all]; intro k
      by_cases hk : z₀ k = 0
      · exact Eventually.of_forall fun _ h => absurd hk h
      · exact (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖z₀ k‖ from
          nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.2 hk))).mono fun r hr _ => hr
    exact (h1.and (h2.and h3)).exists
  have hsub : ball z₀ (2 * r) ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  set K := closedBall z₀ r ∩ {ζ : Fin n → ℂ | ∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → ‖ζ k‖ = r}
    with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ r).inter_right (by
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_norm.comp (continuous_apply k)) continuous_const)
  have hKU : K ⊆ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    rintro ζ ⟨hζ, hζc⟩
    refine ⟨hsub (closedBall_subset_ball (by linarith) hζ), fun k hk => ?_⟩
    by_cases h0 : z₀ k = 0
    · intro h; have := hζc k hk h0; rw [h, norm_zero] at this; linarith
    · intro h
      have h1 := dist_le_pi_dist ζ z₀ k
      rw [h, dist_comm, dist_zero_right] at h1
      have := hrk k h0
      linarith [mem_closedBall.1 hζ]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKU)
  have hind : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, (∀ j, z j ≠ 0) → z ∈ closedBall z₀ r →
      (∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → k ∉ S → ‖z k‖ = r) → ‖Φ z‖ ≤ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro z _ hz hc
      exact hM z ⟨hz, fun k hk h0 => hc k hk h0 (by simp)⟩
    · intro k S hkS ih z hgen hz hc
      by_cases hk : (k : ℕ) < a ∧ z₀ k = 0
      · refine norm_le_of_circle hext hΦ hgr hr0 hsub hz hgen hk.2 fun t ht => ?_
        apply ih
        · intro j
          by_cases hj : j = k
          · subst hj; simp only [Function.update_self]; rintro rfl; simp at ht; linarith
          · rw [Function.update_of_ne hj]; exact hgen j
        · rw [mem_closedBall, dist_pi_le_iff hr0.le]
          intro j
          by_cases hj : j = k
          · subst hj; simp [hk.2, ht]
          · rw [Function.update_of_ne hj]
            exact (dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)
        · intro j hj h0 hjS
          by_cases hjk : j = k
          · subst hjk; simpa using ht
          · rw [Function.update_of_ne hjk]; exact hc j hj h0 (by simp [hjk, hjS])
      · apply ih z hgen hz
        intro j hj h0 hjS
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, h0⟩ hk
        · exact hc j hj h0 (by simp [hjk, hjS])
  refine ⟨ball z₀ r, ball_mem_nhds z₀ hr0, M, fun z hzV hzρ hza => ?_⟩
  have hzU : z ∈ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} :=
    ⟨hzρ, hza⟩
  let w : ℂ → Fin n → ℂ := fun s j => if z j = 0 then s else z j
  have hwc : Continuous w := continuous_pi fun j => by
    by_cases h : z j = 0
    · simp only [w, h, if_true]; exact continuous_id
    · simp only [w, h, if_false]; exact continuous_const
  have hw0 : w 0 = z := funext fun j => by by_cases h : z j = 0 <;> simp [w, h]
  have hΦz : ContinuousAt Φ z := (hΦ.differentiableAt (hUo.mem_nhds hzU)).continuousAt
  have hT : Tendsto (fun s => Φ (w s)) (𝓝[≠] (0 : ℂ)) (𝓝 (Φ z)) := by
    have hc : ContinuousAt (Φ ∘ w) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hw0]; exact hΦz) hwc.continuousAt
    have h := hc.tendsto
    rw [Function.comp_apply, hw0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Φ (w s)‖ ≤ M := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℂ), w s ∈ ball z₀ r :=
      hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact isOpen_ball.mem_nhds hzV)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    apply hind Finset.univ (w s)
    · intro j
      simp only [w]
      split_ifs with h
      · exact hs0
      · exact h
    · exact ball_subset_closedBall hs
    · intro k _ _ hk; exact absurd (Finset.mem_univ k) hk
  exact le_of_tendsto hT.norm hev

end GlobalTheory.HyperplaneLocBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem log_factorial_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ n ∈ Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N, vonMangoldt_mul_zeta]
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le k), ← ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), add_comm]
    rfl

theorem sum_vonMangoldt_div_nat_bounds (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ∧
      ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤ Real.log N + (Real.log 4 + 4) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hF := log_factorial_eq_sum_vonMangoldt_mul_div N
  have hfp : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hup : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log hfp (by exact_mod_cast N.factorial_le_pow)
  have hlo : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
    have h1 := Real.pow_div_factorial_le_exp (N : ℝ) hN'.le N
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_exp, Real.log_div (by positivity) hfp.ne', Real.log_pow] at h2
    linarith
  have h1 : Real.log (N.factorial : ℝ) ≤ N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) := by
    rw [hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    calc Λ n * ((N / n : ℕ) : ℝ) ≤ Λ n * ((N : ℝ) / n) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = N * (Λ n / n) := by ring
  have h2 : N * ∑ n ∈ Ioc 0 N, Λ n / (n : ℝ) ≤
      Real.log (N.factorial : ℝ) + ∑ n ∈ Ioc 0 N, Λ n := by
    rw [hF, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have h := Nat.lt_div_mul_add (a := N) hn0
      have h' : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast h
      linarith
    calc (N : ℝ) * (Λ n / n) = Λ n * ((N : ℝ) / n) := by ring
      _ ≤ Λ n * (((N / n : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hlt vonMangoldt_nonneg
      _ = _ := by ring
  have h3 : ∑ n ∈ Ioc 0 N, Λ n ≤ (Real.log 4 + 4) * N := by
    have h := Chebyshev.psi_le_const_mul_self hN'.le
    rwa [Chebyshev.psi, Nat.floor_natCast] at h
  constructor
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith
  · refine le_of_mul_le_mul_left ?_ hN'
    nlinarith

theorem mertens_first_vonMangoldt :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ y : ℝ, 1 ≤ y →
      |∑ n ∈ Icc 1 ⌊y⌋₊, Λ n / (n : ℝ) - Real.log y| ≤ CM := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨Real.log 4 + 4, by positivity, fun y hy => ?_⟩
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hN' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hN
  have hI : Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  obtain ⟨h1, h2⟩ := sum_vonMangoldt_div_nat_bounds _ hN
  have h5 : Real.log ⌊y⌋₊ ≤ Real.log y :=
    Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have h6 : Real.log y ≤ Real.log 4 + Real.log ⌊y⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    refine Real.log_le_log (by linarith) ?_
    have := Nat.lt_floor_add_one y
    linarith
  rw [hI, abs_le]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfInteger
section
namespace GlobalTheory.DenominatorExists

open NumberField

theorem exists_mul_eq {R : Type} [CommRing R] [IsDedekindDomain R] (P : Ideal R) [hP : P.IsPrime]
    (a b : R) (hb : b ≠ 0) :
    ∃ s t : R, s ∉ P ∧ (a * t = b * s ∨ b * t = a * s) := by
  by_cases h0 : P = ⊥
  · refine ⟨b, a, ?_, Or.inr (mul_comm _ _)⟩
    rw [h0]; simpa using hb
  · haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 _
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) a)
      (algebraMap R (Localization.AtPrime P) b)
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj P.primeCompl c
    simp only at hts
    refine ⟨s, t, s.2, ?_⟩
    rcases hc with hc | hc
    · left
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]
    · right
      apply hinj
      rw [map_mul, map_mul, ← hts, ← mul_assoc, hc]

theorem mem_of_integer {L Ω : Type} [Field L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (s : 𝓞 L) : algebraMap L Ω (s : L) ∈ A := by
  have hz : IsIntegral ℤ (algebraMap L Ω (s : L)) := s.2.map (algebraMap L Ω).toIntAlgHom
  have hA : IsIntegral A (algebraMap L Ω (s : L)) := hz.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem exists_denominator {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : L) (hx : A.valuation (algebraMap L Ω x) ≤ 1) :
    ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧ (s : L) * x = (t : L) := by
  let f : 𝓞 L →+* A :=
    ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A (fun s => mem_of_integer A s)
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  have hle : ∀ s : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) ≤ 1 :=
    fun s => (A.valuation_le_one_iff _).mpr (mem_of_integer A s)
  have hP : ∀ s : 𝓞 L, s ∉ P → A.valuation (algebraMap L Ω (s : L)) = 1 := by
    intro s hs
    refine le_antisymm (hle s) (not_lt.mp fun h => hs ?_)
    exact Ideal.mem_comap.mpr ((A.valuation_lt_one_iff (f s)).mpr h)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : (b : L) ≠ 0 := by exact_mod_cast hb0
  change A.valuation (algebraMap L Ω ((a : L) / (b : L))) ≤ 1 at hx
  change ∃ s t : 𝓞 L, A.valuation (algebraMap L Ω (s : L)) = 1 ∧
    (s : L) * ((a : L) / (b : L)) = (t : L)
  obtain ⟨s, t, hs, h | h⟩ := exists_mul_eq P a b hb0
  · have h' : (a : L) * t = b * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    have e : (t : L) * ((a : L) / (b : L)) = s := by
      field_simp
      linear_combination h'
    refine ⟨t, s, le_antisymm (hle t) ?_, e⟩
    have h1 := hP s hs
    rw [← e, map_mul, map_mul] at h1
    rw [← h1]
    exact mul_le_of_le_one_right' hx
  · have h' : (b : L) * t = a * s := by exact_mod_cast congrArg (fun z : 𝓞 L => (z : L)) h
    refine ⟨s, t, hP s hs, ?_⟩
    field_simp
    linear_combination -h'

end GlobalTheory.DenominatorExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanPairPowSucc
section
namespace GlobalTheory.SpanPairPowSucc

theorem mem_span_pair_pow_succ {R : Type} [inst : CommRing R] (p w : R) (k : ℕ) :
    ∀ x ∈ Ideal.span {p, w} ^ (k + (1 : ℕ)),
      ∃ (c : R), ∃ G ∈ Ideal.span {p, w} ^ k, x = w ^ (k + (1 : ℕ)) * c + p * G := by
  induction k with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    exact ⟨b, a, by simp, by ring⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨c, G, hG, rfl⟩ := ih y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
      refine ⟨c * b, w ^ (k + 1) * c * a + G * (a * p + b * w), ?_, by ring⟩
      refine Ideal.add_mem _ ?_ ?_
      · have hw : w ∈ Ideal.span ({p, w} : Set R) := Ideal.subset_span (by simp)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _))
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hG hz
    · rintro _ _ ⟨c₁, G₁, hG₁, rfl⟩ ⟨c₂, G₂, hG₂, rfl⟩
      exact ⟨c₁ + c₂, G₁ + G₂, Ideal.add_mem _ hG₁ hG₂, by ring⟩

end GlobalTheory.SpanPairPowSucc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NrmAbsOfValuationEqExp
section
noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

end GlobalTheory.Mem.NrmCompl
end
end

