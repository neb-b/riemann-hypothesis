module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlane
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.UHPRoot

noncomputable def cen (k : ℕ) : ℂ := ((k : ℂ) + 2) * Complex.I

noncomputable def rad (k : ℕ) : ℝ := ((k : ℝ) + 2) - 1 / ((k : ℝ) + 2)

theorem rad_pos (k : ℕ) : 0 < rad k := by
  unfold rad
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h : 1 / ((k : ℝ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  linarith

theorem cen_im (k : ℕ) : (cen k).im = (k : ℝ) + 2 := by simp [cen]
theorem cen_re (k : ℕ) : (cen k).re = 0 := by simp [cen]

theorem closedBall_sub (k : ℕ) : Metric.closedBall (cen k) (rad k) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_im_le_norm (z - cen k)
  have h2 : (z - cen k).im = z.im - ((k : ℝ) + 2) := by rw [Complex.sub_im, cen_im]
  rw [h2] at h1
  have h3 : 0 < 1 / ((k : ℝ) + 2) := by positivity
  show 0 < z.im
  unfold rad at hz
  have := neg_abs_le (z.im - ((k : ℝ) + 2))
  linarith

theorem ball_mono : Monotone (fun k : ℕ => Metric.ball (cen k) (rad k)) := by
  refine monotone_nat_of_le_succ fun k => Metric.ball_subset_ball' ?_
  have hd : cen k - cen (k + 1) = -Complex.I := by
    simp only [cen]; push_cast; ring
  rw [dist_eq_norm, hd, norm_neg, Complex.norm_I]
  unfold rad
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 1 / ((k : ℝ) + 1 + 2) ≤ 1 / ((k : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

theorem cover (z : ℂ) (hz : z ∈ Hs) : ∃ k : ℕ, z ∈ Metric.ball (cen k) (rad k) := by
  have hy : 0 < z.im := hz
  obtain ⟨k, hk⟩ := exists_nat_gt ((z.re ^ 2 + z.im ^ 2 + 2) / (2 * z.im))
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  set a : ℝ := (k : ℝ) + 2 with ha
  have hapos : 0 < a := by positivity
  have hka : (k : ℝ) < a := by linarith
  have h1 : z.re ^ 2 + z.im ^ 2 + 2 < 2 * z.im * a := by
    have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * z.im)).1 (hk.trans hka)
    linarith
  have hsq : ‖z - cen k‖ ^ 2 = z.re ^ 2 + (z.im - a) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, cen_re, cen_im]
    ring
  have hrad : rad k = a - 1 / a := rfl
  have hinv : a * (1 / a) = 1 := by field_simp
  have hlt : ‖z - cen k‖ ^ 2 < rad k ^ 2 := by
    rw [hsq, hrad]
    nlinarith [sq_nonneg (1 / a)]
  exact lt_of_pow_lt_pow_left₀ 2 (rad_pos k).le hlt

theorem eqOn_of_pow_eq {D : Set ℂ} (hD : IsOpen D) (hc : IsPreconnected D) {m : ℕ} (hm : 0 < m)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    {z0 : ℂ} (hz0 : z0 ∈ D) (hfg0 : f z0 = g z0) (hne : f z0 ≠ 0)
    (hpow : ∀ z ∈ D, f z ^ m = g z ^ m) : Set.EqOn f g D := by
  have hfc : ContinuousAt f z0 := (hf.differentiableAt (hD.mem_nhds hz0)).continuousAt
  have hgc : ContinuousAt g z0 := (hg.differentiableAt (hD.mem_nhds hz0)).continuousAt
  set S : ℂ → ℂ := fun z => ∑ i ∈ Finset.range m, f z ^ i * g z ^ (m - 1 - i) with hS
  have hSc : ContinuousAt S z0 := by
    simp only [hS]; fun_prop
  have hS0 : S z0 ≠ 0 := by
    have : S z0 = (m : ℂ) * f z0 ^ (m - 1) := by
      simp only [hS, ← hfg0]
      rw [Finset.sum_congr rfl (g := fun _ => f z0 ^ (m - 1))]
      · simp
      · intro i hi
        rw [← pow_add]
        congr 1
        have := Finset.mem_range.1 hi
        omega
    rw [this]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hne)
  have hev : f =ᶠ[nhds z0] g := by
    filter_upwards [hSc.eventually_ne hS0, hD.mem_nhds hz0] with z hz hzD
    have key : S z * (f z - g z) = f z ^ m - g z ^ m := by
      simp only [hS]; exact geom_sum₂_mul (f z) (g z) m
    rw [hpow z hzD, sub_self] at key
    exact sub_eq_zero.1 ((mul_eq_zero.1 key).resolve_left hz)
  exact (hf.analyticOnNhd hD).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hD) hc hz0 hev

end GlobalTheory.UHPRoot


open GlobalTheory.UHPRoot in
theorem GlobalTheory.KZ.H3.uhp_root : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt h τ = ((m * k : ℕ) : ℕ∞)) →
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r Hs ∧ ∀ z ∈ Hs, r z ^ m = h z := by
  classical
  intro h m hm hd hord
  have hHo : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have han : AnalyticOnNhd ℂ h Hs := hd.analyticOnNhd hHo
  have hr : ∀ k : ℕ, ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (Metric.ball (cen k) (rad k)) ∧
      ∀ z ∈ Metric.ball (cen k) (rad k), r z ^ m = h z := fun k =>
    _root_.GlobalTheory.KZ.RootDisc.exists_root_disc h m (cen k) (rad k) hm (rad_pos k) (han.mono (closedBall_sub k))
      (fun τ hτ => hord τ (closedBall_sub k hτ))
  choose r hrd hrp using hr

  have hc0 : cen 0 ∈ Hs := closedBall_sub 0 (Metric.mem_closedBall_self (rad_pos 0).le)
  obtain ⟨k0, hk0⟩ := hord (cen 0) hc0
  have hnt : ¬ ∀ᶠ z in nhds (cen 0), h z = 0 := by
    rw [← analyticOrderAt_eq_top, hk0]; exact ENat.coe_ne_top _
  obtain ⟨z0, hz0h, hz0D⟩ := ((Filter.not_eventually.1 hnt).and_eventually
    (Metric.ball_mem_nhds (cen 0) (rad_pos 0))).exists
  obtain ⟨w0, hw0⟩ := IsAlgClosed.exists_pow_nat_eq (h z0) hm
  have hw0ne : w0 ≠ 0 := by
    rintro rfl; rw [zero_pow hm.ne'] at hw0; exact hz0h hw0.symm
  have hz0k : ∀ k, z0 ∈ Metric.ball (cen k) (rad k) := fun k => ball_mono (Nat.zero_le k) hz0D
  have hrk0 : ∀ k, r k z0 ≠ 0 := by
    intro k h0; have := hrp k z0 (hz0k k); rw [h0, zero_pow hm.ne'] at this; exact hz0h this.symm

  set r' : ℕ → ℂ → ℂ := fun k z => (w0 / r k z0) * r k z with hr'
  have hr'd : ∀ k, DifferentiableOn ℂ (r' k) (Metric.ball (cen k) (rad k)) := fun k =>
    (differentiableOn_const _).mul (hrd k)
  have hr'p : ∀ k, ∀ z ∈ Metric.ball (cen k) (rad k), r' k z ^ m = h z := by
    intro k z hz
    simp only [hr', mul_pow, div_pow, hw0, hrp k z hz, hrp k z0 (hz0k k)]
    rw [div_self hz0h, one_mul]
  have hr'0 : ∀ k, r' k z0 = w0 := by
    intro k; simp only [hr']; rw [div_mul_cancel₀ _ (hrk0 k)]
  have agree_le : ∀ j k, j ≤ k → Set.EqOn (r' j) (r' k) (Metric.ball (cen j) (rad j)) := by
    intro j k hjk
    refine eqOn_of_pow_eq Metric.isOpen_ball (convex_ball _ _).isPreconnected hm (hr'd j)
      ((hr'd k).mono (ball_mono hjk)) (hz0k j) (by rw [hr'0, hr'0]) (by rw [hr'0]; exact hw0ne) ?_
    intro z hz; rw [hr'p j z hz, hr'p k z (ball_mono hjk hz)]
  have agree : ∀ j k w, w ∈ Metric.ball (cen j) (rad j) → w ∈ Metric.ball (cen k) (rad k) →
      r' j w = r' k w := by
    intro j k w hj hk
    rcases le_total j k with hjk | hkj
    · exact agree_le j k hjk hj
    · exact (agree_le k j hkj hk).symm
  choose N hN using cover
  let R : ℂ → ℂ := fun z => if hz : z ∈ Hs then r' (N z hz) z else 0
  refine ⟨R, ?_, ?_⟩
  · intro z hz
    have hzk := hN z hz
    have hev : R =ᶠ[nhds z] r' (N z hz) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzk] with w hw
      have hwH : w ∈ Hs := closedBall_sub _ (Metric.ball_subset_closedBall hw)
      simp only [R, dif_pos hwH]
      exact agree _ _ w (hN w hwH) hw
    exact (((hr'd _).differentiableAt (Metric.isOpen_ball.mem_nhds hzk)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    simp only [R, dif_pos hz]
    exact hr'p _ z (hN z hz)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHolomorphicRootUpperHalfPlaneOfOrderDvd
section
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section
namespace GlobalTheory.RootHs
open Metric Complex

lemma mem_ball_big (u : ℂ) (R ε : ℝ) (hε : 0 < ε) (hu : 2 * ε ≤ u.im) (hR : u.re ^ 2 + u.im ^ 2 < R * u.im)
    (hRε : ε < R) : u ∈ ball ((R : ℂ) * I) (R - ε) := by
  have hRe : 0 ≤ R - ε := by linarith
  rw [Metric.mem_ball, Complex.dist_eq]
  have hsq : ‖u - (R : ℂ) * I‖ ^ 2 = u.re ^ 2 + (u.im - R) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hlt : ‖u - (R : ℂ) * I‖ ^ 2 < (R - ε) ^ 2 := by
    rw [hsq]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ R) (by linarith : (0:ℝ) ≤ u.im - 2 * ε), sq_nonneg ε]
  nlinarith [norm_nonneg (u - (R : ℂ) * I)]

lemma closedBall_big_sub (R ε : ℝ) (hε : 0 < ε) : closedBall ((R : ℂ) * I) (R - ε) ⊆ Hs := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have h1 := Complex.abs_im_le_norm (z - (R : ℂ) * I)
  have h2 : (z - (R : ℂ) * I).im = z.im - R := by simp
  rw [h2] at h1
  show 0 < z.im
  have h3 := neg_abs_le (z.im - R)
  linarith

lemma exists_disc (z₀ z : ℂ) (h₀ : 0 < z₀.im) (hz : 0 < z.im) :
    ∃ (c : ℂ) (r : ℝ), closedBall c r ⊆ Hs ∧ z₀ ∈ ball c r ∧ z ∈ ball c r := by
  set ε : ℝ := min z₀.im z.im / 2 with hεdef
  have hε : 0 < ε := half_pos (lt_min h₀ hz)
  have h2ε₀ : 2 * ε ≤ z₀.im := by rw [hεdef]; linarith [min_le_left z₀.im z.im]
  have h2ε : 2 * ε ≤ z.im := by rw [hεdef]; linarith [min_le_right z₀.im z.im]
  have ha : 0 ≤ (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im := div_nonneg (by positivity) h₀.le
  have hb : 0 ≤ (z.re ^ 2 + z.im ^ 2) / z.im := div_nonneg (by positivity) hz.le
  set R : ℝ := (z₀.re ^ 2 + z₀.im ^ 2) / z₀.im + (z.re ^ 2 + z.im ^ 2) / z.im + ε + 1 with hRdef
  have hR₀ : z₀.re ^ 2 + z₀.im ^ 2 < R * z₀.im := (div_lt_iff₀ h₀).mp (by rw [hRdef]; linarith)
  have hR : z.re ^ 2 + z.im ^ 2 < R * z.im := (div_lt_iff₀ hz).mp (by rw [hRdef]; linarith)
  have hRε : ε < R := by rw [hRdef]; linarith
  exact ⟨(R : ℂ) * I, R - ε, closedBall_big_sub R ε hε, mem_ball_big z₀ R ε hε h2ε₀ hR₀ hRε,
    mem_ball_big z R ε hε h2ε hR hRε⟩

theorem discRoot : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    (∃ z₀ ∈ Hs, h z₀ ≠ 0) → ∀ (c : ℂ) (r : ℝ), Metric.closedBall c r ⊆ Hs →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball c r) ∧ ∀ z ∈ Metric.ball c r, g z ^ m = h z := by
  rintro h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz => ?_⟩
    rw [Metric.ball_eq_empty.mpr hr] at hz
    exact absurd hz (Set.notMem_empty z)
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have hHsConn : IsPreconnected Hs := by
    show IsPreconnected {z : ℂ | 0 < z.im}
    exact (convex_halfSpace_im_gt (r := 0)).isPreconnected
  have han : AnalyticOnNhd ℂ h Hs := hh.analyticOnNhd hHsOpen
  refine GlobalTheory.KZ.RootDisc.exists_root_disc h m c r hm hr (han.mono hsub) ?_
  intro τ hτ
  have hτ' := hsub hτ
  have hfin : analyticOrderAt h τ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hHsConn hτ' htop hz₀)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hmer : meromorphicOrderAt h τ = ((n : ℤ) : WithTop ℤ) := by
    rw [(han τ hτ').meromorphicOrderAt_eq, ← hn]
    rfl
  obtain ⟨k, hk⟩ := Int.natCast_dvd_natCast.mp (hdiv τ hτ' n hmer)
  exact ⟨k, by rw [← hn, hk]⟩

theorem rootUnique : ∀ (U : Set ℂ) (g₁ g₂ : ℂ → ℂ) (m : ℕ) (z₀ : ℂ), 0 < m → IsOpen U → IsPreconnected U →
    DifferentiableOn ℂ g₁ U → DifferentiableOn ℂ g₂ U → (∀ z ∈ U, g₁ z ^ m = g₂ z ^ m) → z₀ ∈ U →
    g₁ z₀ = g₂ z₀ → g₁ z₀ ≠ 0 → Set.EqOn g₁ g₂ U := by
  intro U g₁ g₂ m z₀ hm hU hC hg₁ hg₂ hpow hz₀ heq hne
  have hc₁ : ContinuousAt g₁ z₀ := (hg₁.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hc₂ : ContinuousAt g₂ z₀ := (hg₂.differentiableAt (hU.mem_nhds hz₀)).continuousAt
  have hq : ContinuousAt (fun z => g₂ z / g₁ z) z₀ := hc₂.div hc₁ hne
  have hq0 : g₂ z₀ / g₁ z₀ = 1 := by rw [← heq, div_self hne]
  set S : Finset ℂ := (Polynomial.nthRoots m (1 : ℂ)).toFinset.erase 1 with hSdef
  have hS : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
  have hopen : (S : Set ℂ)ᶜ ∈ 𝓝 (g₂ z₀ / g₁ z₀) := by
    rw [hq0]
    exact hS.isOpen_compl.mem_nhds (by simp [hSdef])
  have hev : g₁ =ᶠ[𝓝 z₀] g₂ := by
    filter_upwards [hq.preimage_mem_nhds hopen, hc₁.eventually_ne hne, hU.mem_nhds hz₀] with z hzS hz1 hzU
    have hroot : g₂ z / g₁ z ∈ Polynomial.nthRoots m (1 : ℂ) := by
      rw [Polynomial.mem_nthRoots hm, div_pow, ← hpow z hzU, div_self (pow_ne_zero _ hz1)]
    have h1 : g₂ z / g₁ z = 1 := by
      by_contra hne1
      exact hzS (Finset.mem_erase.mpr ⟨hne1, Multiset.mem_toFinset.mpr hroot⟩)
    rw [div_eq_one_iff_eq hz1] at h1
    exact h1.symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hg₁.analyticOnNhd hU) (hg₂.analyticOnNhd hU) hC hz₀ hev

theorem rootHs : ∀ (h : ℂ → ℂ) (m : ℕ), 0 < m → DifferentiableOn ℂ h Hs →
    (∀ τ ∈ Hs, ∀ k : ℤ, meromorphicOrderAt h τ = (k : WithTop ℤ) → (m : ℤ) ∣ k) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Hs ∧ ∀ z ∈ Hs, g z ^ m = h z := by
  classical
  intro h m hm hh hdiv
  by_cases hz : ∃ z₀ ∈ Hs, h z₀ ≠ 0
  swap
  · simp only [not_exists, not_and, not_not] at hz
    refine ⟨fun _ => 0, differentiableOn_const 0, fun z hz' => ?_⟩
    rw [hz z hz', zero_pow hm.ne']
  obtain ⟨z₀, hz₀, hne⟩ := hz
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq (h z₀) hm
  have hw₀ne : w₀ ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hw₀, zero_pow hm.ne'])
  have hHsOpen : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}
    exact isOpen_lt continuous_const Complex.continuous_im
  have key : ∀ z ∈ Hs, ∃ (c : ℂ) (r : ℝ), z₀ ∈ ball c r ∧ z ∈ ball c r ∧ ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball c r) ∧ (∀ y ∈ ball c r, g y ^ m = h y) ∧ g z₀ = w₀ := by
    intro z hz
    obtain ⟨c, r, hsub, h0, h1⟩ := exists_disc z₀ z hz₀ hz
    obtain ⟨g, hgd, hgp⟩ := discRoot h m hm hh hdiv ⟨z₀, hz₀, hne⟩ c r hsub
    have hg0 : g z₀ ≠ 0 := by
      intro h0'
      apply hne
      rw [← hgp z₀ h0, h0', zero_pow hm.ne']
    refine ⟨c, r, h0, h1, fun y => (w₀ / g z₀) * g y, hgd.const_mul _, fun y hy => ?_, ?_⟩
    · rw [mul_pow, div_pow, hgp y hy, hw₀, hgp z₀ h0, div_self hne, one_mul]
    · exact div_mul_cancel₀ w₀ hg0
  choose c r h0 h1 g hgd hgp hgz using key
  have hloc : ∀ z₁ (hz₁ : z₁ ∈ Hs) z (hz : z ∈ Hs), z ∈ ball (c z₁ hz₁) (r z₁ hz₁) →
      g z hz z = g z₁ hz₁ z := by
    intro z₁ hz₁ z hz hzb
    have hU : IsOpen (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) := isOpen_ball.inter isOpen_ball
    have hC : IsPreconnected (ball (c z hz) (r z hz) ∩ ball (c z₁ hz₁) (r z₁ hz₁)) :=
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    refine rootUnique _ (g z hz) (g z₁ hz₁) m z₀ hm hU hC ((hgd z hz).mono Set.inter_subset_left)
      ((hgd z₁ hz₁).mono Set.inter_subset_right) (fun y hy => by rw [hgp z hz y hy.1, hgp z₁ hz₁ y hy.2])
      ⟨h0 z hz, h0 z₁ hz₁⟩ ((hgz z hz).trans (hgz z₁ hz₁).symm) (by rw [hgz z hz]; exact hw₀ne) ⟨h1 z hz, hzb⟩
  refine ⟨fun z => if h' : z ∈ Hs then g z h' z else 0, ?_, ?_⟩
  · intro z₁ hz₁
    have hev : (fun z => if h' : z ∈ Hs then g z h' z else 0) =ᶠ[𝓝 z₁] g z₁ hz₁ := by
      have hmem : ball (c z₁ hz₁) (r z₁ hz₁) ∩ Hs ∈ 𝓝 z₁ := (isOpen_ball.inter hHsOpen).mem_nhds ⟨h1 z₁ hz₁, hz₁⟩
      filter_upwards [hmem] with z hz
      show (if h' : z ∈ Hs then g z h' z else 0) = g z₁ hz₁ z
      rw [dite_eq_left hz.2]
      exact hloc z₁ hz₁ z hz.2 hz.1
    exact (((hgd z₁ hz₁).differentiableAt (isOpen_ball.mem_nhds (h1 z₁ hz₁))).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · intro z hz
    show (if h' : z ∈ Hs then g z h' z else 0) ^ m = h z
    rw [dite_eq_left hz]
    exact hgp z hz z (h1 z hz)

end GlobalTheory.RootHs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CongruenceDescent

theorem mem_Gamma_iff_exists {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma N ↔ ∃ B : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have d00 : (N : ℤ) ∣ γ 0 0 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
    have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
    have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
    have d11 : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
    obtain ⟨a, ha⟩ := d00; obtain ⟨b, hb⟩ := d01; obtain ⟨c, hc⟩ := d10; obtain ⟨d, hd⟩ := d11
    refine ⟨!![a, b; c, d], ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨B, hB⟩
    have e : ∀ i j, γ i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := fun i j => by
      rw [show γ i j = (γ : Matrix (Fin 2) (Fin 2) ℤ) i j from rfl, hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  obtain ⟨c, rfl⟩ := h
  exact mem_Gamma_iff_exists.2 ⟨(c : ℤ) • B, by rw [hB, smul_smul]; push_cast; ring_nf⟩

theorem pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    γ ^ q ∈ CongruenceSubgroup.Gamma (L * q) := by
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  have key : ∀ m : ℕ, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ m = 1 + ((m : ℤ) * L) • B + ((L : ℤ) * L) • (B * B * Y) := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      refine ⟨(m : ℤ) • 1 + Y + Y * ((L : ℤ) • B), ?_⟩
      rw [pow_succ, hY, hB]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, Matrix.mul_assoc]
      push_cast
      module
  obtain ⟨Y, hY⟩ := key q
  obtain ⟨c, rfl⟩ := hq
  refine mem_Gamma_iff_exists.2 ⟨B + (c : ℤ) • (B * B * Y), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hY, smul_add, smul_smul]
  push_cast
  module

theorem pow_pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) (j : ℕ) :
    γ ^ (q ^ j) ∈ CongruenceSubgroup.Gamma (L * q ^ j) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, mul_one] using hγ
  | succ j ih =>
    rw [pow_succ, pow_mul, ← mul_assoc]
    exact pow_mem_Gamma_mul (hq.mul_right _) ih

theorem coprime_card_of_pow_eq_one {Q : Type} [Group Q] [Finite Q] {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m)
    (h : ∀ x : Q, x ^ m = 1) : l.Coprime (Nat.card Q) := by
  rw [hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  exact (hl.coprime_iff_not_dvd.1 hm) this

theorem exists_invariant {H A : Type} [Group H] [CommGroup A] (s : H → A →* A)
    (hs : ∀ g h a, s (g * h) a = s h (s g a)) (D : Subgroup H) [D.Normal] [Finite (H ⧸ D)] {m : ℕ}
    (hm : m.Coprime (Nat.card (H ⧸ D))) (f : A) (hD : ∀ δ ∈ D, s δ f = f) (hf : ∀ γ, ∃ g : A, s γ f = f * g ^ m) :
    ∃ h : A, ∀ γ, s γ (f * h ^ m) = f * h ^ m := by
  classical
  haveI := Fintype.ofFinite (H ⧸ D)
  choose g hg using hf
  have hwd : ∀ a b : H, (a : H ⧸ D) = b → s a f = s b f := by
    intro a b hab
    have h1 : a * (a⁻¹ * b) * a⁻¹ ∈ D :=
      Subgroup.Normal.conj_mem (a⁻¹ * b) (QuotientGroup.eq.1 hab) a
    have h2 : b = (a * (a⁻¹ * b) * a⁻¹) * a := by group
    conv_rhs => rw [h2, hs, hD _ h1]
  set F : A := ∏ x : H ⧸ D, s x.out f with hF
  have hinv : ∀ γ, s γ F = F := by
    intro γ
    rw [hF, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (γ : H ⧸ D)) _ _ fun x => ?_
    rw [← hs]
    apply hwd
    simp
  have hFeq : F = f ^ Nat.card (H ⧸ D) * (∏ x : H ⧸ D, g x.out) ^ m := by
    rw [hF]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hm
  refine ⟨f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v, fun γ => ?_⟩
  have e : f * (f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v) ^ m = F ^ v := by
    have e1 : f * f ^ (-u * (m : ℤ)) = f ^ ((Nat.card (H ⧸ D) : ℤ) * v) := by
      rw [← _root_.zpow_one_add]
      congr 1
      linear_combination -huv
    rw [hFeq, mul_pow, _root_.mul_zpow, ← _root_.zpow_natCast, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_natCast]
    simp only [← _root_.zpow_mul]
    rw [← mul_assoc, e1, mul_comm v]
  rw [e, map_zpow, hinv]

end GlobalTheory.KZ.ES.CongruenceDescent

namespace GlobalTheory.KZ.ES


open CongruenceDescent CongruenceSubgroup in
theorem exists_lev_mul_pow_of_invariant_mod_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M e hl hM f hlev hf
  obtain ⟨a, q, hq, hMq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have hlq : l.Coprime q := hl.coprime_iff_not_dvd.2 hq
  let H : Subgroup SL(2, ℤ) := CongruenceSubgroup.Gamma (M * l ^ (a * e))
  haveI := CongruenceSubgroup.Gamma_normal (M ^ e)
  haveI : NeZero (M ^ e) := ⟨(pow_pos hM e).ne'⟩
  let D : Subgroup H := (CongruenceSubgroup.Gamma (M ^ e)).subgroupOf H
  haveI : D.FiniteIndex := inferInstance
  have hcard : l.Coprime (Nat.card (H ⧸ D)) := by
    refine CongruenceDescent.coprime_card_of_pow_eq_one hl (hlq.pow_right e) fun x => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    refine CongruenceDescent.Gamma_le_of_dvd ?_ (CongruenceDescent.pow_pow_mem_Gamma_mul (q := q) ?_ γ.2 e)
    · exact ⟨M, by rw [hMq]; ring⟩
    · exact ⟨l ^ a * l ^ (a * e), by rw [hMq]; ring⟩
  obtain ⟨h, hh⟩ := CongruenceDescent.exists_invariant (H := H) (A := X.Kˣ)
    (fun γ => Units.map (X.sl (ofSL γ) : X.K →* X.K))
    (fun g h a => Units.ext (by simp [X.sl_mul])) D (hcard.pow_left n) f
    (fun δ hδ => Units.ext (by simpa using hlev δ hδ))
    (fun γ => by
      obtain ⟨g, hg⟩ := hf γ (CongruenceDescent.Gamma_le_of_dvd (dvd_mul_right _ _) γ.2)
      exact ⟨g, Units.ext (by simpa using hg)⟩)
  refine ⟨a * e, h, fun γ hγ => ?_⟩
  have := congrArg Units.val (hh ⟨γ, hγ⟩)
  simpa using this

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesPowOfLeadingQInvStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeries_pow_of_leading_qInv : ∀ {R : Type} [CommRing R] (x : HahnSeries ℚ R), x.coeff (-1) = 1 → (∀ r : ℚ, r < -1 → x.coeff r = 0) → ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  first | exact @GlobalTheory.hahn_pow_neg_one_lead | exact GlobalTheory.hahn_pow_neg_one_lead | (intros; apply GlobalTheory.hahn_pow_neg_one_lead <;> assumption)
end

