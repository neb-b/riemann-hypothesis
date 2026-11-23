module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.RegMaxReindex

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedChartComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

theorem exists_lipschitz_near_compact {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ δ > 0, ∃ L : ℝ, ∀ z ∈ K, ∀ y ∈ closedBall z δ, y ∈ W ∧ ‖f y - f z‖ ≤ L * ‖y - z‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hW hKW
  have hcont : ContinuousOn (fderiv ℝ f) W :=
    ContDiffOn.continuousOn_fderiv_of_isOpen (fun y hy => (hf y hy).contDiffWithinAt) hW le_rfl
  obtain ⟨L, hL⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨δ, hδ, L, fun z hz y hy => ⟨hsub (closedBall_subset_cthickening hz δ hy), ?_⟩⟩
  have hB : closedBall z δ ⊆ W := (closedBall_subset_cthickening hz δ).trans hsub
  exact (convex_closedBall z δ).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hf w (hB hw)).differentiableAt one_ne_zero)
    (fun w hw => hL w (closedBall_subset_cthickening hz δ hw)) (mem_closedBall_self hδ.le) hy

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem exists_transfer_pair [CompactSpace X] (j k : Fin P.N) :
    ∃ δ > 0, ∃ L : ℝ, ∀ x ∈ P.mid j ∩ P.mid k, ∀ y ∈ closedBall (P.chart j x) δ,
      y ∈ (P.chart j).target ∧ (P.chart j).symm y ∈ (P.chart k).source ∧
      ‖P.chart k ((P.chart j).symm y) - P.chart k x‖ ≤ L * ‖y - P.chart j x‖ ∧
      P.q j y - P.q k (P.chart k ((P.chart j).symm y)) - (P.q j (P.chart j x) - P.q k (P.chart k x)) ≤
        L * ‖y - P.chart j x‖ := by
  set K := (P.chart j) '' (closure (P.mid j) ∩ closure (P.mid k)) with hKdef
  set W := (P.chart j).target ∩ (P.chart j).symm ⁻¹' (P.chart k).source with hWdef
  have hK : IsCompact K := (isClosed_closure.inter isClosed_closure).isCompact.image_of_continuousOn
    ((P.chart j).continuousOn.mono (inter_subset_left.trans (P.closure_mid j)))
  have hW : IsOpen W := (P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
    (P.chart k).open_source
  have hKW : K ⊆ W := by
    rintro _ ⟨x, ⟨hxj, hxk⟩, rfl⟩
    exact ⟨(P.chart j).map_source (P.closure_mid j hxj), by
      simp [(P.chart j).left_inv (P.closure_mid j hxj), P.closure_mid k hxk]⟩
  have hτ : ∀ y ∈ W, ContDiffAt ℝ 1 (P.chart k ∘ (P.chart j).symm) y := by
    intro y hy
    have h := analyticAt_transition (P.compat j) (P.compat k) ((P.chart j).map_target hy.1) hy.2
    rw [(P.chart j).right_inv hy.1] at h
    exact (h.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hg : ∀ y ∈ W, ContDiffAt ℝ 1
      (fun y => P.q j y - P.q k ((P.chart k ∘ (P.chart j).symm) y)) y := by
    intro y hy
    have h1 : ContDiffAt ℝ 1 (P.q j) y :=
      ((P.q_smooth j).contDiffAt ((P.chart j).open_target.mem_nhds hy.1)).of_le (by simp)
    have h2 : ContDiffAt ℝ 1 (P.q k) ((P.chart k ∘ (P.chart j).symm) y) :=
      ((P.q_smooth k).contDiffAt
        ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hy.2))).of_le (by simp)
    exact h1.sub (h2.comp y (hτ y hy))
  obtain ⟨δ₁, hδ₁, L₁, h₁⟩ := exists_lipschitz_near_compact hK hW hKW hτ
  obtain ⟨δ₂, hδ₂, L₂, h₂⟩ := exists_lipschitz_near_compact hK hW hKW hg
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max L₁ L₂, fun x hx y hy => ?_⟩
  have hxK : P.chart j x ∈ K := mem_image_of_mem _ ⟨subset_closure hx.1, subset_closure hx.2⟩
  obtain ⟨hyW, e₁⟩ := h₁ _ hxK y (closedBall_subset_closedBall (min_le_left _ _) hy)
  obtain ⟨-, e₂⟩ := h₂ _ hxK y (closedBall_subset_closedBall (min_le_right _ _) hy)
  have hxj : (P.chart j).symm (P.chart j x) = x := (P.chart j).left_inv (P.mid_subset_source j hx.1)
  simp only [Function.comp_apply, hxj] at e₁ e₂
  have hn : 0 ≤ ‖y - P.chart j x‖ := norm_nonneg _
  refine ⟨hyW.1, hyW.2, e₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn), ?_⟩
  rw [Real.norm_eq_abs] at e₂
  exact (le_abs_self _).trans (e₂.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn))

theorem exists_transfer [CompactSpace X] :
    ∃ δ > 0, ∃ L : ℝ, 1 ≤ L ∧ ∀ j k : Fin P.N, ∀ x ∈ P.mid j ∩ P.mid k,
      ∀ y ∈ closedBall (P.chart j x) δ,
      y ∈ (P.chart j).target ∧ (P.chart j).symm y ∈ (P.chart k).source ∧
      ‖P.chart k ((P.chart j).symm y) - P.chart k x‖ ≤ L * ‖y - P.chart j x‖ ∧
      P.q j y - P.q k (P.chart k ((P.chart j).symm y)) - (P.q j (P.chart j x) - P.q k (P.chart k x)) ≤
        L * ‖y - P.chart j x‖ := by
  choose δ hδ L hL using fun p : Fin P.N × Fin P.N => P.exists_transfer_pair p.1 p.2
  by_cases hN : Nonempty (Fin P.N × Fin P.N)
  · obtain ⟨p₀, hp₀⟩ := Finite.exists_min δ
    have hS : 0 ≤ ∑ p, |L p| := Finset.sum_nonneg fun p _ => abs_nonneg (L p)
    refine ⟨δ p₀, hδ p₀, 1 + ∑ p, |L p|, by linarith, fun j k x hx y hy => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hL (j, k) x hx y (closedBall_subset_closedBall (hp₀ (j, k)) hy)
    have hLp : L (j, k) ≤ 1 + ∑ p, |L p| := by
      have := Finset.single_le_sum (fun p _ => abs_nonneg (L p)) (Finset.mem_univ (j, k))
      linarith [le_abs_self (L (j, k))]
    have hn := norm_nonneg (y - P.chart j x)
    exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hLp hn),
      h4.trans (mul_le_mul_of_nonneg_right hLp hn)⟩
  · exact ⟨1, one_pos, 1, le_rfl, fun j k => (hN ⟨(j, k)⟩).elim⟩

end PotentialCharts

theorem BoundedChartComparison.proof (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) : BoundedChartComparison.Statement := by
  intro X _ _ _ D A B ρ
  obtain ⟨δ, hδ, hmarg⟩ := B.exists_margin
  obtain ⟨Q, hQ⟩ := B.exists_bound_q hmarg
  obtain ⟨Cφ, hCφ⟩ := B.bdd
  obtain ⟨δ₁, hδ₁, L, hL, hT⟩ := B.exists_transfer
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨B₀, hB₀⟩ : ∃ c : ℝ, c = |Q| + |Cφ| := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by rw [hB₀]; positivity

  have hball : ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ r, r ≤ δ →
      closedBall (B.chart k x) r ⊆ (B.chart k).target := fun k x hx r hr =>
    (closedBall_subset_closedBall hr).trans
      ((closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ).trans (hmarg k))
  have hbd : ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ y ∈ closedBall (B.chart k x) δ, |B.u k y| ≤ B₀ := by
    intro k x hx y hy
    have e1 := hQ k y (closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ hy)
    have e2 := hCφ ((B.chart k).symm y)
    have e3 : |B.u k y| ≤ |B.q k y| + |B.ph ((B.chart k).symm y)| := abs_add_le _ _
    rw [hB₀]
    linarith [le_abs_self Q, le_abs_self Cφ]
  have hpsh : ∀ k : Fin B.N, IsPsh (B.chart k).target (B.u k) := fun k => B.u_psh k
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (4 * Real.log (4 * C₁ ^ 2) * B₀) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max E L := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ le_max_left _ _
  have hCL : L ≤ C := hC ▸ le_max_right _ _
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min δ₁ (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min hδ₁ (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀
  simp only [lt_min_iff] at ht₀
  obtain ⟨htδ₁, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hCt' : t * (C₁ + 2) = C₁ * t + 2 * t := by ring
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  obtain ⟨hℓa, -⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
    rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
      Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
    have := neg_abs_le (Real.log (δ / C₁))
    rw [← ha] at this
    linarith [Real.exp_pos 1]
  have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
  have key : ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
      B.phReg ρ t j x - B.phReg ρ t k x ≤ E / Real.log t⁻¹ + L * t := by
    intro j k x hx
    have hpj := hpsh j
    have hpk := hpsh k

    have hi : molli ρ t (B.u j) (B.chart j x) ≤ polyMax (B.u j) (B.chart j x) t :=
      (((mollify_thm D ρ _ (B.u j) (B.chart j).open_target hpj).1 t ht).2.2.2 (B.chart j x)
        (hball j x hx.1 t (by linarith))).2

    have hii : polyMax (B.u j) (B.chart j x) t ≤ polyMax (B.u k) (B.chart k x) (L * t) +
        (B.q j (B.chart j x) - B.q k (B.chart k x)) + L * t := by
      refine polyMax_le' ht.le fun y hy => ?_
      obtain ⟨-, hyk, hτ, hg⟩ := hT j k x hx y (closedBall_subset_closedBall htδ₁.le hy)
      have hyt : ‖y - B.chart j x‖ ≤ t := by rw [← dist_eq_norm]; exact hy
      have hLy := mul_le_mul_of_nonneg_left hyt (by linarith : (0 : ℝ) ≤ L)
      have hτ' : B.chart k ((B.chart j).symm y) ∈ closedBall (B.chart k x) (L * t) := by
        rw [mem_closedBall, dist_eq_norm]
        exact hτ.trans hLy
      have hle := le_polyMax hpk.1 (hball k x hx.2 (L * t) (by linarith)) hτ'
      have hu : B.u j y = B.u k (B.chart k ((B.chart j).symm y)) +
          (B.q j y - B.q k (B.chart k ((B.chart j).symm y))) := by
        simp only [BoundedPshData.u, PotentialCharts.chartFun, (B.chart k).left_inv hyk]
        ring
      linarith
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (B.u k) (B.chart k x) s ≤ polyMax (B.u k) (B.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball k x hx.2 _ hs')
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have h4C : 0 < 4 * C₁ := by linarith
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t

    have hiv := h0 D ρ b _ (B.u k) (B.chart k x) t (B.chart k).open_target hpk ht
      (hball k x hx.2 _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D _ (B.u k) (B.chart k x) δ t C₁ (B.chart k).open_target hpk
      (hball k x hx.2 δ le_rfl) ht (by linarith) hC₁tlt
    have hMδ : polyMax (B.u k) (B.chart k x) δ ≤ B₀ :=
      polyMax_le' hδ.le fun y hy => (le_abs_self _).trans (hbd k x hx.2 y hy)
    have hMC : -B₀ ≤ polyMax (B.u k) (B.chart k x) (C₁ * t) :=
      (neg_le_of_abs_le (hbd k x hx.2 _ (mem_closedBall_self hδ.le))).trans
        (le_polyMax hpk.1 (hball k x hx.2 _ hC₁t) (mem_closedBall_self (by positivity)))
    have hN : polyMax (B.u k) (B.chart k x) δ - polyMax (B.u k) (B.chart k x) (C₁ * t) ≤ 2 * B₀ := by
      linarith
    have hO : polyMax (B.u k) (B.chart k x) (C₁ * t) - polyMax (B.u k) (B.chart k x) (t / (4 * C₁)) ≤
        4 * Real.log (4 * C₁ ^ 2) * B₀ / Real.log t⁻¹ := by
      refine hv.trans ?_
      rw [div_le_div_iff₀ hden0 hℓ0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (B.u k) (B.chart k x) δ -
              polyMax (B.u k) (B.chart k x) (C₁ * t)) * Real.log t⁻¹
          ≤ Real.log (4 * C₁ ^ 2) * (2 * B₀) * Real.log t⁻¹ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hlog4) hℓ0.le
        _ = 4 * Real.log (4 * C₁ ^ 2) * B₀ * (Real.log t⁻¹ / 2) := by ring
        _ ≤ 4 * Real.log (4 * C₁ ^ 2) * B₀ * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg (mul_nonneg (by norm_num) hlog4) hB₀0)
    have hc : c₀ * (polyMax (B.u k) (B.chart k x) (2 * t) - polyMax (B.u k) (B.chart k x) (t / 4)) ≤
        c₀ * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) ≤ E / Real.log t⁻¹ := by
      rw [hE, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hO (by linarith)
    have hsum : polyMax (B.u k) (B.chart k x) (L * t) - polyMax (B.u k) (B.chart k x) (2 * t) +
          c₀ * (polyMax (B.u k) (B.chart k x) (2 * t) - polyMax (B.u k) (B.chart k x) (t / 4)) ≤
        (1 + c₀) * (polyMax (B.u k) (B.chart k x) (C₁ * t) -
          polyMax (B.u k) (B.chart k x) (t / (4 * C₁))) := by
      have h' : polyMax (B.u k) (B.chart k x) (L * t) - polyMax (B.u k) (B.chart k x) (2 * t) ≤
          polyMax (B.u k) (B.chart k x) (C₁ * t) - polyMax (B.u k) (B.chart k x) (t / (4 * C₁)) := by
        linarith
      linarith
    simp only [BoundedPshData.phReg, BoundedPshData.smoothed]
    linarith
  intro j k x hx
  have hEC : E / Real.log t⁻¹ + L * t ≤ C / Real.log t⁻¹ + C * t :=
    add_le_add (div_le_div_of_nonneg_right hCE hℓ0.le) (mul_le_mul_of_nonneg_right hCL ht.le)
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PBoundedGlue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)

noncomputable section

namespace PotentialCharts

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)


open Classical in
theorem glue_eventually_of_close (a : Fin P.N → X → ℝ) (η : Fin P.N → X → ℝ) {Cη ε : ℝ}
    (hcut : P.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ P.mid j ∩ P.mid k, |a j x - a k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      P.glue (fun j x => a j x + 4 * ε * η j x) ε y =
        regMax ε (fun j : {j // x₀ ∈ P.mid j} => a j y + 4 * ε * η j y) + ε / 2 := by
  choose L hLc hLsub hL using hcut.eq_neg_one
  have hev : ∀ᶠ y in 𝓝 x₀, ∀ j, (x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      (x₀ ∉ P.mid j → y ∉ L j ∧ y ∉ closure (P.inner j)) := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases h : x₀ ∈ P.mid j
    · filter_upwards [(P.isOpen_mid j).mem_nhds h] with y hy
      exact ⟨fun _ => hy, fun h' => absurd h h'⟩
    · have hc : IsOpen (L j ∪ closure (P.inner j))ᶜ :=
        ((hLc j).union isClosed_closure).isOpen_compl
      have hx : x₀ ∈ (L j ∪ closure (P.inner j))ᶜ := by
        rintro (h1 | h1)
        · exact h (hLsub j h1)
        · exact h (P.closure_inner j h1)
      filter_upwards [hc.mem_nhds hx] with y hy
      simp only [mem_compl_iff, mem_union, not_or] at hy
      exact ⟨fun h' => absurd h' h, fun _ => hy⟩
  filter_upwards [hev] with y hy
  refine ⟨fun j hj => (hy j).1 hj, ?_⟩
  simp only [PotentialCharts.glue]
  refine congrArg (· + ε / 2) ?_
  refine regMax_of_injective
    (fun j : {j // x₀ ∈ P.mid j} => (⟨j.1, (hy j.1).1 j.2⟩ : {j // y ∈ P.mid j}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)) hε _ ?_
  intro i hi
  obtain ⟨k, hk⟩ := P.cover y
  have hk0 : x₀ ∈ P.mid k := by
    by_contra h
    exact ((hy k).2 h).2 (subset_closure hk)
  refine ⟨⟨k, hk0⟩, ?_⟩
  have hi0 : x₀ ∉ P.mid i := fun h => hi ⟨i.1, h⟩ rfl
  have hiL : η i y = -1 := hL i y ⟨i.2, ((hy i).2 hi0).1⟩
  have hk1 : η k y = 0 := hcut.eq_zero k y hk
  have hc := (abs_le.1 (hcmp i k y ⟨i.2, P.inner_subset_mid k hk⟩)).2
  simp only [hiL, hk1]
  linarith

end PotentialCharts

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

theorem smoothed_local (ρ : Mollifier D) {t : ℝ} (ht : 0 < t) (j : Fin B.N)
    {z : Fin D → ℂ} (hz : closedBall z t ⊆ (B.chart j).target) :
    ContDiffAt ℝ ∞ (B.smoothed ρ t j) z ∧ ∀ w, 0 ≤ levi (B.smoothed ρ t j) z w := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall z t).exists_cthickening_subset_open (B.chart j).open_target hz
  rw [cthickening_closedBall hδ.le ht.le] at hδsub
  have hU'sub : ball z (δ + t) ⊆ (B.chart j).target := ball_subset_closedBall.trans hδsub
  have hpsh : IsPsh (ball z (δ + t)) (B.u j) := isPsh_mono (B.u_psh j) hU'sub
  obtain ⟨hopen, hsm, hpm, -⟩ :=
    (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ (B.u j) isOpen_ball hpsh).1 t ht
  have hz' : z ∈ shrink (ball z (δ + t)) t := closedBall_subset_ball (lt_add_of_pos_left t hδ)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ hopen
    (hsm.of_le (WithTop.coe_le_coe.mpr le_top))).1 hpm
  exact ⟨hsm.contDiffAt (hopen.mem_nhds hz'), fun w => hlevi.2 z hz' w⟩

theorem arg_contDiffAt (ρ : Mollifier D) (η : Fin B.N → X → ℝ) {Cη t ε : ℝ}
    (hcut : B.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin B.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ B.mid j) :
    ContDiffAt ℝ ∞ (fun y => B.phReg ρ t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by
  have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
  have hT : ContDiffAt ℝ ∞ (B.chart j ∘ ψ.symm) (ψ x) :=
    ((analyticAt_transition hψ (B.compat j) hx hxj).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hTx : (B.chart j ∘ ψ.symm) (ψ x) = B.chart j x := by simp [ψ.left_inv hx]
  have hS := (B.smoothed_local ρ ht j (hball j x (subset_closure hj))).1
  have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
    (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
  rw [← hTx] at hS hq
  have hη := contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hx
  exact ((hS.comp (ψ x) hT).sub (hq.comp (ψ x) hT)).add (contDiffAt_const.mul hη)

end BoundedPshData


open Classical in
theorem BoundedGlue.proof : BoundedGlue.Statement := by
  intro X _ _ _ D A B ρ η Cη t ε hcut ht hε hball hcmp
  have hloc := B.glue_eventually_of_close (fun j x => B.phReg ρ t j x) η hcut hε.le hcmp
  refine ⟨fun i y hy => ?_, fun k x hx w => ?_⟩
  ·
    have hyt : y ∈ (A.chart i).target := hy.1
    have hx₀ : (A.chart i).symm y ∈ (A.chart i).source := (A.chart i).map_target hyt
    have hψ : IsCompatChart A (A.chart i) := fun l => ⟨A.holo l i, A.holo i l⟩
    have hyx : A.chart i ((A.chart i).symm y) = y := (A.chart i).right_inv hyt
    have hG : ContDiffAt ℝ ∞ (fun y' => regMax ε (fun j : {j // (A.chart i).symm y ∈ B.mid j} =>
        B.phReg ρ t j ((A.chart i).symm y') + 4 * ε * η j ((A.chart i).symm y')) + ε / 2) y := by
      have hr := ((ReciprocityTheory.AnForm.A.regMax_thm {j // (A.chart i).symm y ∈ B.mid j}).1 ε hε).1
      refine (hr.contDiffAt.comp y (contDiffAt_pi.2 fun j => ?_)).add contDiffAt_const
      have := B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hx₀ j.2
      rwa [hyx] at this
    refine (hG.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (((A.chart i).continuousAt_symm hyt).tendsto.eventually (hloc ((A.chart i).symm y))).mono
      fun y' hy' => hy'.2
  ·
    have hψ := B.compat k
    have hxk : x ∈ (B.chart k).source := B.mid_subset_source k hx
    have hzt : B.chart k x ∈ (B.chart k).target := (B.chart k).map_source hxk
    have hqk : ContDiffAt ℝ ∞ (B.q k) (B.chart k x) :=
      (B.q_smooth k).contDiffAt ((B.chart k).open_target.mem_nhds hzt)
    set b : {j // x ∈ B.mid j} → (Fin D → ℂ) → ℝ := fun j y =>
      B.phReg ρ t j ((B.chart k).symm y) + 4 * ε * η j ((B.chart k).symm y) + B.q k y with hb_def
    have hb : ∀ j, ContDiffAt ℝ ∞ (b j) (B.chart k x) := fun j =>
      (B.arg_contDiffAt ρ η (ε := ε) hcut ht hball hψ hxk j.2).add hqk
    have hadd := ((ReciprocityTheory.AnForm.A.regMax_thm {j // x ∈ B.mid j}).1 ε hε).2.2.2.2.2.2.1
    have hgerm : B.chartFun (B.regularised ρ t ε η) k =ᶠ[𝓝 (B.chart k x)]
        fun y => regMax ε (fun j => b j y) + ε / 2 := by
      have ht' : Tendsto (B.chart k).symm (𝓝 (B.chart k x)) (𝓝 x) := by
        have := ((B.chart k).continuousAt_symm hzt).tendsto
        rwa [(B.chart k).left_inv hxk] at this
      filter_upwards [ht'.eventually (hloc x)] with y hy
      simp only [PotentialCharts.chartFun, BoundedPshData.regularised]
      rw [hy.2, hb_def, hadd]
      ring
    have hconst : levi (fun y => regMax ε (fun j => b j y) + ε / 2) (B.chart k x) w =
        levi (fun y => regMax ε (fun j => b j y)) (B.chart k x) w := by
      unfold levi
      have : fderiv ℝ (fun y => regMax ε (fun j => b j y) + ε / 2) =
          fderiv ℝ (fun y => regMax ε (fun j => b j y)) := funext fun _ => fderiv_add_const _
      rw [this]
    rw [levi_congr hgerm w, hconst]
    have hzV : B.chart k x ∈ interior {y | ∀ j, ContDiffAt ℝ 2 (b j) y} :=
      mem_interior_iff_mem_nhds.2 (Filter.eventually_all.2 fun j =>
        ((hb j).of_le (WithTop.coe_le_coe.mpr le_top)).eventually (by simp))
    refine ReciprocityTheory.AnForm.A.regMaxLevi_thm D {j // x ∈ B.mid j} ε _ b isOpen_interior hε
      (fun j y hy => (interior_subset hy j).contDiffWithinAt) _ hzV w _ fun ⟨j, hj⟩ => ?_
    have hxj : x ∈ (B.chart j).source := B.mid_subset_source j hj
    set T := B.chart j ∘ (B.chart k).symm with hT
    have hTa : AnalyticAt ℂ T (B.chart k x) := analyticAt_transition hψ (B.compat j) hxk hxj
    have hTR : ContDiffAt ℝ ∞ T (B.chart k x) := (hTa.restrictScalars (𝕜 := ℝ)).contDiffAt
    have hTz : T (B.chart k x) = B.chart j x := by simp [hT, (B.chart k).left_inv hxk]
    obtain ⟨hS, hSl⟩ := B.smoothed_local ρ ht j (hball j x (subset_closure hj))
    have hq : ContDiffAt ℝ ∞ (B.q j) (B.chart j x) :=
      (B.q_smooth j).contDiffAt ((B.chart j).open_target.mem_nhds ((B.chart j).map_source hxj))
    rw [← hTz] at hS hSl hq
    have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hS2 : ContDiffAt ℝ 2 (B.smoothed ρ t j ∘ T) (B.chart k x) := (hS.comp _ hTR).of_le h2
    have hQ2 : ContDiffAt ℝ 2 (fun y => B.q k y - B.q j (T y)) (B.chart k x) :=
      (hqk.sub (hq.comp _ hTR)).of_le h2
    have hE2 : ContDiffAt ℝ 2 (η j ∘ (B.chart k).symm) (B.chart k x) :=
      (contDiffAt_comp_symm_of_smoothOn hψ (B.isOpen_mid j) (hcut.smooth j) hj hxk).of_le h2
    have hF2 : ContDiffAt ℝ 2 (fun y => (B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y)))
        (B.chart k x) := hS2.add (contDiffAt_const.mul hQ2)
    have hbe : b ⟨j, hj⟩ = fun y => ((B.smoothed ρ t j ∘ T) y + 1 * (B.q k y - B.q j (T y))) +
        4 * ε * (η j ∘ (B.chart k).symm) y := by
      funext y
      simp only [hb_def, BoundedPshData.phReg, hT, Function.comp_apply]
      ring
    have e1 := levi_add_smul (4 * ε) hF2 hE2 w
    have e2 := levi_add_smul 1 hS2 hQ2 w
    have e3 := levi_comp (φ := B.smoothed ρ t j) w hTa (hS.of_le h2)

    have e4 : levi (fun y => B.q k y - B.q j (T y)) (B.chart k x) w = 0 := by
      obtain ⟨W, hWo, hxW, G, hG, hGeq⟩ := B.q_th k x x ⟨B.th.mem_U x, hxk⟩
      obtain ⟨W', hWo', hxW', G', hG', hGeq'⟩ := B.q_th j x x ⟨B.th.mem_U x, hxj⟩
      have hO : IsOpen (W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source) :=
        (((hWo.inter hWo').inter (B.th.isOpen_U x)).inter (B.chart k).open_source).inter
          (B.chart j).open_source
      have hxO : x ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ⟨⟨⟨⟨hxW, hxW'⟩, B.th.mem_U x⟩, hxk⟩, hxj⟩
      have hev1 : ∀ᶠ y in 𝓝 (B.chart k x),
          (B.chart k).symm y ∈ W ∩ W' ∩ B.th.U x ∩ (B.chart k).source ∩ (B.chart j).source :=
        ((B.chart k).continuousAt_symm hzt).preimage_mem_nhds
          (by rw [(B.chart k).left_inv hxk]; exact hO.mem_nhds hxO)
      have hev := hev1.and ((B.chart k).open_target.mem_nhds hzt)
      have hGa := analyticAt_comp_symm_of_holoOn hψ hG hxW hxk
      have hGa' := analyticAt_comp_symm_of_holoOn hψ hG' hxW' hxk
      have hgerm : (fun y => B.q k y - B.q j (T y)) =ᶠ[𝓝 (B.chart k x)]
          fun y => (((G ∘ (B.chart k).symm) - (G' ∘ (B.chart k).symm)) y).re := by
        filter_upwards [hev] with y hy
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, hyt⟩ := hy
        have ek := hGeq _ ⟨⟨h1, h3⟩, h4⟩
        have ej := hGeq' _ ⟨⟨h2, h3⟩, h5⟩
        rw [(B.chart k).right_inv hyt] at ek
        simp only [hT, Function.comp_apply, Pi.sub_apply, Complex.sub_re]
        linarith
      rw [levi_congr hgerm w]
      exact levi_re_analytic (hGa.sub hGa') w
    have hl := hcut.levi_ge j k x ⟨hj, hx⟩ w
    have h4 := mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 4 * ε)
    have h0 := hSl (fderiv ℂ T (B.chart k x) w)
    rw [hbe, e1, e2, e3, e4]
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

