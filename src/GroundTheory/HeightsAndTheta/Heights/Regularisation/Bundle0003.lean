module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

theorem PolyMaxLowerBound.exists_pos_le {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ, 0 < δ ∧ ∀ j, δ ≤ f j := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min f
    exact ⟨f j₀, hf j₀, hj₀⟩

theorem PolyMaxLowerBound.chart_margin {X : Type} [TopologicalSpace X] [CompactSpace X] {D : ℕ}
    {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.N) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧ ∀ x ∈ R.mid j, ∀ y ∈ closedBall (R.chart j x) δ,
      y ∈ (R.chart j).target ∧ |R.q j y| ≤ Q := by
  have hK : IsCompact ((R.chart j) '' closure (R.mid j)) :=
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have hKT : (R.chart j) '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (R.chart j).open_target hKT
  obtain ⟨Q, hQ⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    ((R.q_smooth j).continuousOn.mono hsub)
  refine ⟨δ, max Q 0, hδ, le_max_right _ _, fun x hx y hy => ?_⟩
  have hy' : y ∈ cthickening δ ((R.chart j) '' closure (R.mid j)) :=
    closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ hy
  refine ⟨hsub hy', ?_⟩
  have := hQ y hy'
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem PolyMaxLowerBound.exists_far_point {D : ℕ} (z : Fin D → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ y ∈ closedBall z t, ∀ i, t / 2 ≤ ‖y i‖ := by
  classical
  refine ⟨fun i => if t / 2 ≤ ‖z i‖ then z i else z i + (t : ℂ), ?_, fun i => ?_⟩
  · rw [mem_closedBall, dist_pi_le_iff ht.le]
    intro i
    by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h, dist_self]; exact ht.le
    · simp only [if_neg h, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, le_refl]
  · by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h]; exact h
    · simp only [if_neg h]
      replace h := not_le.mp h
      have h1 : ‖((t : ℝ) : ℂ)‖ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := by
        calc ‖((t : ℝ) : ℂ)‖ = ‖(z i + (t : ℂ)) - z i‖ := by ring_nf
          _ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
      linarith

theorem PolyMaxLowerBound.log_inv_half_sq {t : ℝ} (ht : 0 < t) :
    Real.log ((t / 2) ^ 2)⁻¹ = 2 * Real.log 2 + 2 * Real.log t⁻¹ := by
  have h : ((t / 2) ^ 2)⁻¹ = (2 * t⁻¹) ^ 2 := by field_simp
  rw [h, Real.log_pow, Real.log_mul (by norm_num) (inv_ne_zero ht.ne')]
  push_cast; ring

theorem PolyMaxLowerBound.proof : PolyMaxLowerBound.Statement := by
  intro X _ _ _ D A R
  obtain ⟨B, hB⟩ := R.f_bdd
  choose δf Qf hδf hQf hball using PolyMaxLowerBound.chart_margin R
  obtain ⟨δ, hδ0, hδle⟩ := PolyMaxLowerBound.exists_pos_le δf hδf
  set Q : ℝ := ∑ j, Qf j with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => hQf j
  have hQj : ∀ j, Qf j ≤ Q := fun j =>
    Finset.single_le_sum (f := Qf) (fun k _ => hQf k) (Finset.mem_univ j)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set Λ : ℝ := Real.exp 1 + |B| + 2 * D * Real.log 2 + 2 * D with hΛdef
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
    have : 0 ≤ |B| := abs_nonneg B
    linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  set C : ℝ := Q + |R.Clog| * (Real.log Λ + 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, min δ (Real.exp (-Real.exp 1)), lt_min hδ0 (Real.exp_pos _), ?_⟩
  intro t ht htt K j x hx
  have htδ : t ≤ δ := (htt.trans_le (min_le_left _ _)).le
  have hte : t < Real.exp (-Real.exp 1) := htt.trans_le (min_le_right _ _)
  set ℓ : ℝ := Real.log t⁻¹ with hℓdef
  have hℓe : Real.exp 1 < ℓ := by
    rw [hℓdef, Real.lt_log_iff_exp_lt (inv_pos.2 ht)]
    rw [Real.exp_neg] at hte
    exact (lt_inv_comm₀ ht (Real.exp_pos _)).1 hte
  have hℓ1 : 1 ≤ ℓ := he1.trans hℓe.le
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hℓe.le
  obtain ⟨y, hy, hyn⟩ := PolyMaxLowerBound.exists_far_point (R.chart j x) ht
  obtain ⟨hyT, hqy⟩ := hball j x hx y (closedBall_subset_closedBall (htδ.trans (hδle j)) hy)
  have hyD : y ∉ coordDiv (R.S j) := by
    rintro ⟨i, -, hi⟩
    have := hyn i
    rw [hi, norm_zero] at this
    linarith
  have hsrc := (R.chart j).map_target hyT
  have hYo : (R.chart j).symm y ∈ R.Yo :=
    (R.mem_Yo j _ hsrc).2 (by rwa [(R.chart j).right_inv hyT])
  have hr1 := R.one_le_r _ hYo

  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
    have hterm : ∀ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ 2 * Real.log 2 + 2 * ℓ := by
      intro i _
      rw [← PolyMaxLowerBound.log_inv_half_sq ht]
      have h2 : 0 < t / 2 := by linarith
      have hyi : 0 < ‖y i‖ := h2.trans_le (hyn i)
      apply Real.log_le_log (by positivity)
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le (hyn i) 2)
    have hM : 0 ≤ 2 * Real.log 2 + 2 * ℓ := by linarith
    calc ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, (2 * Real.log 2 + 2 * ℓ) :=
          Finset.sum_le_sum hterm
      _ = (R.S j).card * (2 * Real.log 2 + 2 * ℓ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
          apply mul_le_mul_of_nonneg_right _ hM
          have := Finset.card_le_univ (R.S j)
          rw [Fintype.card_fin] at this
          exact_mod_cast this
  have hrle : R.r ((R.chart j).symm y) ≤ Λ * ℓ := by
    rw [R.r_chart j y ⟨hyT, hyD⟩]
    have hf : R.f j y ≤ |B| := (le_abs_self _).trans ((hB j y hyT).trans (le_abs_self B))
    have hA : 0 ≤ Real.exp 1 + |B| + 2 * D * Real.log 2 := by
      have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
      have : 0 ≤ |B| := abs_nonneg B
      linarith
    have : Real.exp 1 + |B| + 2 * D * Real.log 2 ≤ (Real.exp 1 + |B| + 2 * D * Real.log 2) * ℓ :=
      le_mul_of_one_le_right hA hℓ1
    rw [hΛdef]
    nlinarith
  have hlogr : Real.log (R.r ((R.chart j).symm y)) ≤ Real.log Λ + Real.log ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hrle
  have hlogr0 : 0 ≤ Real.log (R.r ((R.chart j).symm y)) := Real.log_nonneg hr1
  have hph := R.ph_ge _ hYo

  have hq : -Q ≤ R.q j y := by
    have := (abs_le.1 (hqy.trans (hQj j))).1
    linarith
  have h1 : -(|R.Clog| * Real.log (R.r ((R.chart j).symm y))) ≤
      -R.Clog * Real.log (R.r ((R.chart j).symm y)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlogr0
    linarith
  have h2 : |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤
      |R.Clog| * (Real.log Λ + 1) * Real.log ℓ := by
    have h3 : Real.log Λ + Real.log ℓ ≤ (Real.log Λ + 1) * Real.log ℓ := by nlinarith
    calc |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤ |R.Clog| * (Real.log Λ + Real.log ℓ) :=
          mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)
      _ ≤ |R.Clog| * ((Real.log Λ + 1) * Real.log ℓ) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = _ := by ring
  have hQℓ : Q ≤ Q * Real.log ℓ := le_mul_of_one_le_right hQ0 hlogℓ
  have hu : -C * Real.log ℓ ≤ R.u j y := by
    show -C * Real.log ℓ ≤ R.q j y + R.ph ((R.chart j).symm y)
    rw [hCdef]
    nlinarith
  have htr : R.trunc K j y = max (R.u j y) (-K) := by
    simp only [RegChartData.trunc, limsupExt, if_neg hyD]

  unfold polyMax
  by_cases hb : BddAbove (R.trunc K j '' closedBall (R.chart j x) t)
  · refine le_trans ?_ (le_csSup hb (mem_image_of_mem _ hy))
    rw [htr]
    exact hu.trans (le_max_left _ _)
  · rw [Real.sSup_of_not_bddAbove hb]
    have : 0 ≤ C * Real.log ℓ := mul_nonneg hC0 (by linarith)
    linarith

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.ToPotentialChartsChartFun
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular

open MeasureTheory Metric Set
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.A (Mollifier molli regMax tmax kθ le_tmax tmax_le kθ_integral abs_le_of_kθ_ne)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot IsCompatChart)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)

noncomputable section

theorem closure_image_subset {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (e : OpenPartialHomeomorph X Y) {s : Set X} (hs : closure s ⊆ e.source) :
    IsCompact (e '' closure s) ∧ closure (e.target ∩ e.symm ⁻¹' s) ⊆ e '' closure s := by
  have hK : IsCompact (e '' closure s) :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hs)
  refine ⟨hK, closure_minimal ?_ hK.isClosed⟩
  rintro y ⟨hy, hys⟩
  exact ⟨e.symm y, subset_closure hys, e.right_inv hy⟩

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

namespace RegCharts

def ofPotentialCharts [CompactSpace X] (P : PotentialCharts A) (om : LocPot X)
    (om_pot : IsPotential A om) (om_pos : IsPosPot A om) : RegCharts A where
  n := P.N
  ψ := P.chart
  compat := P.compat
  W j := (P.chart j).target
  W' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.mid j
  W'' j := (P.chart j).target ∩ (P.chart j).symm ⁻¹' P.inner j
  isOpen_kappaOpenNeighbourhood j := (P.chart j).open_target
  isOpen_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_mid j)
  isOpen_alt_alt j := (P.chart j).isOpen_inter_preimage_symm (P.isOpen_inner j)
  W_subset _ := subset_rfl
  isCompact_closure_middle j :=
    (closure_image_subset (P.chart j) (P.closure_mid j)).1.of_isClosed_subset isClosed_closure
      (closure_image_subset (P.chart j) (P.closure_mid j)).2
  closure_W'_subset j := (closure_image_subset (P.chart j) (P.closure_mid j)).2.trans
    (image_subset_iff.2 fun _ hx => (P.chart j).map_source (P.closure_mid j hx))
  closure_W''_subset j := by
    have hs := (P.closure_inner j).trans (P.mid_subset_source j)
    refine (closure_image_subset (P.chart j) hs).2.trans ?_
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(P.chart j).map_source (hs hx), ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.mid j
    rw [(P.chart j).left_inv (hs hx)]
    exact P.closure_inner j hx
  cover x := by
    obtain ⟨j, hj⟩ := P.cover x
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hj)
    refine ⟨j, hs, (P.chart j).map_source hs, ?_⟩
    show (P.chart j).symm (P.chart j x) ∈ P.inner j
    rw [(P.chart j).left_inv hs]
    exact hj
  θ := P.th
  θ_pot := P.th_pot
  om := om
  om_pot := om_pot
  om_pos := om_pos
  q := P.q
  q_smooth := P.q_smooth
  q_θ j y hy _ := by
    obtain ⟨V, hV, hyV, G, hG, hq⟩ := P.q_th j y y ⟨P.th.mem_U y, hy⟩
    refine ⟨V, hV, hyV, fun x => -G x, fun k => (hG k).neg, fun x hx _ => ?_⟩
    have := hq x hx
    simp only [Complex.neg_re]
    linarith

variable [CompactSpace X] (P : PotentialCharts A) (om : LocPot X) (om_pot : IsPotential A om)
  (om_pos : IsPosPot A om)

end RegCharts

namespace RegCharts

variable (R : RegCharts A)

variable [T2Space X] (hW : ∀ j, R.W j ⊆ ball 0 1)

end RegCharts

section RoundTrip

variable [CompactSpace X] [T2Space X]

end RoundTrip

namespace PotentialCharts

variable (P : PotentialCharts A)


end PotentialCharts

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
end

