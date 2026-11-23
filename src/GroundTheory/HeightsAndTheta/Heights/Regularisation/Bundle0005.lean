module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' polyMax_mono')

noncomputable section

theorem log_inv_facts {t a : ℝ} (ht : 0 < t) (ha : 0 ≤ a)
    (hta : t < Real.exp (-(Real.exp 1 + 2 * a))) :
    Real.exp 1 + 2 * a < Real.log t⁻¹ ∧ 1 < Real.log (Real.log t⁻¹) := by
  have h1 : Real.log t < -(Real.exp 1 + 2 * a) := by
    have := Real.log_lt_log ht hta
    rwa [Real.log_exp] at this
  rw [Real.log_inv]
  have he := Real.exp_pos 1
  refine ⟨by linarith, ?_⟩
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  linarith

theorem ChartComparison.proof (h0 : MollifiedLowerBound.Statement)
    (h1 : PolyMaxOscillation.Statement) (h2 : PolyMaxLowerBound.Statement)
    (h3 : TruncPsh.Statement) (h4 : TruncTransfer.Statement) : ChartComparison.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h3 X D A R
  choose V hVo _hVt hVball hVpsh using hV
  obtain ⟨δ₁, L, B₁, hδ₁, hL, hT⟩ := h4 X D A R
  obtain ⟨C₂, t₂, ht₂, hlow⟩ := h2 X D A R
  obtain ⟨b, hb⟩ := mollifier_exists_bound ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = L + 2 := ⟨_, rfl⟩
  have hC₁3 : 3 ≤ C₁ := by linarith
  obtain ⟨a, ha⟩ : ∃ c : ℝ, c = |Real.log (δ / C₁)| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  obtain ⟨B₀', hB₀'⟩ : ∃ c : ℝ, c = max B₀ 0 := ⟨_, rfl⟩
  obtain ⟨C₂', hC₂'⟩ : ∃ c : ℝ, c = max C₂ 0 := ⟨_, rfl⟩
  have hB₀'0 : 0 ≤ B₀' := hB₀' ▸ le_max_right _ _
  have hC₂'0 : 0 ≤ C₂' := hC₂' ▸ le_max_right _ _
  have hC₂C₂' : C₂ ≤ C₂' := hC₂' ▸ le_max_left _ _
  have hlog4 : 0 ≤ Real.log (4 * C₁ ^ 2) := Real.log_nonneg (by nlinarith)
  obtain ⟨E, hE⟩ : ∃ c : ℝ, c = (1 + c₀) * (2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂')) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = max (max E L) (C₂' + |B₁| + 1) := ⟨_, rfl⟩
  have hCE : E ≤ C := hC ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hCL : L ≤ C := hC ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hCB : C₂' + |B₁| + 1 ≤ C := hC ▸ le_max_right _ _
  have hC0 : 0 ≤ C := by linarith [abs_nonneg B₁]
  have hC₁2 : 0 < C₁ + 2 := by linarith
  refine ⟨C, min (min t₂ δ₁) (min (δ / (C₁ + 2)) (Real.exp (-(Real.exp 1 + 2 * a)))),
    lt_min (lt_min ht₂ hδ₁) (lt_min (div_pos hδ hC₁2) (Real.exp_pos _)), ?_⟩
  intro t ht ht₀ K hK
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htt₂, htδ₁⟩, htδ, hte⟩ := ht₀
  have hCt : t * (C₁ + 2) < δ := (lt_div_iff₀ hC₁2).1 htδ
  have hCt' : t * (C₁ + 2) = C₁ * t + 2 * t := by ring
  have hC₁t : C₁ * t ≤ δ := by linarith
  have hC₁tlt : C₁ * t < δ := by linarith
  have htLt : t ≤ L * t := le_mul_of_one_le_left ht.le hL
  have hLt : L * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h2t : 2 * t ≤ C₁ * t := mul_le_mul_of_nonneg_right (by linarith) ht.le
  have htC : t ≤ C₁ * t := le_mul_of_one_le_left ht.le (by linarith)
  obtain ⟨hℓa, hlogℓ⟩ := log_inv_facts ht ha0 hte
  have hℓ0 : 0 < Real.log t⁻¹ := by linarith [Real.exp_pos 1]
  have hK0 : 0 ≤ K := le_trans (mul_nonneg hC0 (by linarith)) hK
  have hKB : -K + B₁ ≤ -C₂ * Real.log (Real.log t⁻¹) := by
    have h1' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hCB (by linarith)
    have h2' : B₁ ≤ |B₁| * Real.log (Real.log t⁻¹) := by
      have := le_mul_of_one_le_right (abs_nonneg B₁) hlogℓ.le
      linarith [le_abs_self B₁]
    have h3' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
    have h4' : (C₂' + |B₁| + 1) * Real.log (Real.log t⁻¹) = C₂' * Real.log (Real.log t⁻¹) +
        |B₁| * Real.log (Real.log t⁻¹) + Real.log (Real.log t⁻¹) := by ring
    have h5' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
    linarith
  have key : ∀ j k : Fin R.N, ∀ x ∈ R.mid j ∩ R.mid k,
      R.phReg ρ K t j x - R.phReg ρ K t k x ≤ E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t := by
    intro j k x hx
    obtain ⟨hpj, -⟩ := hVpsh j K
    obtain ⟨hpk, hbk⟩ := hVpsh k K
    have hball : ∀ r, r ≤ δ → closedBall (R.chart k x) r ⊆ V k := fun r hr =>
      (closedBall_subset_closedBall hr).trans (hVball k x hx.2)
    have hballj : closedBall (R.chart j x) t ⊆ V j :=
      (closedBall_subset_closedBall (by linarith : t ≤ δ)).trans (hVball j x hx.1)

    have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
      (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) hpj).1 t ht).2.2.2 (R.chart j x) hballj).2

    have hii : polyMax (R.trunc K j) (R.chart j x) t ≤
        max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t :=
      polyMax_le' ht.le fun y hy => hT K j k x hx t ht htδ₁ y hy
    have mono : ∀ s s', 0 ≤ s → s ≤ s' → s' ≤ δ →
        polyMax (R.trunc K k) (R.chart k x) s ≤ polyMax (R.trunc K k) (R.chart k x) s' :=
      fun s s' hs hss' hs' => polyMax_mono' hpk.1 hs hss' (hball _ hs')
    have hlowk := hlow t ht htt₂ K k x hx.2
    have e0 := mono t (L * t) ht.le htLt (by linarith)
    have e1 := mono (L * t) (C₁ * t) (by linarith) hLt hC₁t
    have h4C : 0 < 4 * C₁ := by linarith
    have hq : t / (4 * C₁) ≤ t / 4 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith)
    have e2 := mono (t / (4 * C₁)) (t / 4) (by positivity) hq (by linarith)
    have e3 := mono (t / 4) (2 * t) (by positivity) (by linarith) (by linarith)
    have e4 := mono (2 * t) (C₁ * t) (by positivity) h2t hC₁t
    have e5 := mono t (C₁ * t) ht.le htC hC₁t
    have hmax : max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B₁) =
        polyMax (R.trunc K k) (R.chart k x) (L * t) := max_eq_left (by linarith)
    rw [hmax] at hii

    have hiv := h0 D ρ b (V k) (R.trunc K k) (R.chart k x) t (hVo k) hpk ht
      (hball _ (by linarith)) hb
    rw [← hc₀] at hiv

    have hv := h1 D (V k) (R.trunc K k) (R.chart k x) δ t C₁ (hVo k) hpk (hball δ le_rfl) ht
      (by linarith) hC₁tlt
    have hMδ : polyMax (R.trunc K k) (R.chart k x) δ ≤ B₀' :=
      polyMax_le' hδ.le fun y hy => (hbk y (hVball k x hx.2 hy)).trans
        (max_le (hB₀' ▸ le_max_left _ _) (by linarith))
    have hN : polyMax (R.trunc K k) (R.chart k x) δ - polyMax (R.trunc K k) (R.chart k x) (C₁ * t) ≤
        (B₀' + C₂') * Real.log (Real.log t⁻¹) := by
      have h1' : C₂ * Real.log (Real.log t⁻¹) ≤ C₂' * Real.log (Real.log t⁻¹) :=
        mul_le_mul_of_nonneg_right hC₂C₂' (by linarith)
      have h2' : B₀' ≤ B₀' * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hB₀'0 hlogℓ.le
      have h3' : -C₂ * Real.log (Real.log t⁻¹) = -(C₂ * Real.log (Real.log t⁻¹)) := by ring
      have h4' : (B₀' + C₂') * Real.log (Real.log t⁻¹) =
          B₀' * Real.log (Real.log t⁻¹) + C₂' * Real.log (Real.log t⁻¹) := by ring
      linarith
    have hden : Real.log t⁻¹ / 2 ≤ Real.log (δ / (C₁ * t)) := by
      rw [show δ / (C₁ * t) = (δ / C₁) * t⁻¹ by field_simp,
        Real.log_mul (div_pos hδ (by linarith)).ne' (inv_pos.2 ht).ne']
      have := neg_abs_le (Real.log (δ / C₁))
      rw [← ha] at this
      linarith [Real.exp_pos 1]
    have hden0 : 0 < Real.log (δ / (C₁ * t)) := by linarith
    have hP : 0 ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') := by positivity
    have hO : polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) ≤
        2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      refine hv.trans ?_
      rw [div_le_iff₀ hden0]
      calc Real.log (4 * C₁ ^ 2) * (polyMax (R.trunc K k) (R.chart k x) δ -
              polyMax (R.trunc K k) (R.chart k x) (C₁ * t))
          ≤ Real.log (4 * C₁ ^ 2) * ((B₀' + C₂') * Real.log (Real.log t⁻¹)) :=
            mul_le_mul_of_nonneg_left hN hlog4
        _ = 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * (Real.log t⁻¹ / 2) := by
            have hx := div_mul_cancel₀ (Real.log (Real.log t⁻¹)) hℓ0.ne'
            linear_combination (-(Real.log (4 * C₁ ^ 2) * (B₀' + C₂'))) * hx
        _ ≤ 2 * Real.log (4 * C₁ ^ 2) * (B₀' + C₂') *
              (Real.log (Real.log t⁻¹) / Real.log t⁻¹) * Real.log (δ / (C₁ * t)) :=
            mul_le_mul_of_nonneg_left hden (mul_nonneg hP (div_nonneg (by linarith) hℓ0.le))
    have hc : c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₀0
    have hfin : (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) ≤
        E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) := by
      rw [hE]
      have := mul_le_mul_of_nonneg_left hO (by linarith : (0 : ℝ) ≤ 1 + c₀)
      linarith
    have hsum : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) +
          c₀ * (polyMax (R.trunc K k) (R.chart k x) (2 * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / 4)) ≤
        (1 + c₀) * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
          polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := by
      have h' : polyMax (R.trunc K k) (R.chart k x) (L * t) -
          polyMax (R.trunc K k) (R.chart k x) (2 * t) ≤
          polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
            polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁)) := by linarith
      calc _ ≤ (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) +
            c₀ * (polyMax (R.trunc K k) (R.chart k x) (C₁ * t) -
              polyMax (R.trunc K k) (R.chart k x) (t / (4 * C₁))) := add_le_add h' hc
        _ = _ := by ring
    simp only [RegChartData.phReg, RegChartData.smoothed]
    linarith
  have hr : 0 ≤ Real.log (Real.log t⁻¹) / Real.log t⁻¹ := div_nonneg (by linarith) hℓ0.le
  intro j k x hx
  have hEC : E * (Real.log (Real.log t⁻¹) / Real.log t⁻¹) + L * t ≤
      C * Real.log (Real.log t⁻¹) / Real.log t⁻¹ + C * t := by
    rw [mul_div_assoc]
    have := mul_le_mul_of_nonneg_right hCE hr
    have := mul_le_mul_of_nonneg_right hCL ht.le
    linarith
  exact abs_sub_le_iff.2 ⟨(key j k x hx).trans hEC, (key k j x ⟨hx.2, hx.1⟩).trans hEC⟩

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

namespace LogCoverDescent

variable {n a : ℕ} (h : a ≤ n)

lemma add_mem_logCover_iff {v : Fin n → ℂ} (hre : ∀ k : Fin n, (v k).re = 0)
    (hz : ∀ k : Fin n, a ≤ k.val → v k = 0) (w : Fin n → ℂ) :
    w + v ∈ logCover h ↔ w ∈ logCover h := by
  simp only [logCover, Set.mem_ofPred_eq, Pi.add_apply, Complex.add_re, hre, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk => ?_⟩
    simpa [hz k hk] using h2 k hk

def periods (φ : (Fin n → ℂ) → ℂ) : AddSubgroup (Fin n → ℂ) where
  carrier := {v | ∀ w, (w + v ∈ logCover h ↔ w ∈ logCover h) ∧ (w ∈ logCover h → φ (w + v) = φ w)}
  zero_mem' := fun w => by simp
  add_mem' := by
    intro u v hu hv w
    simp only [Set.mem_ofPred_eq] at hu hv
    have e : w + (u + v) = (w + u) + v := (add_assoc _ _ _).symm
    refine ⟨?_, fun hw => ?_⟩
    · rw [e, (hv _).1, (hu _).1]
    · rw [e, (hv _).2 ((hu w).1.2 hw), (hu w).2 hw]
  neg_mem' := by
    intro v hv w
    simp only [Set.mem_ofPred_eq] at hv
    have e : (w + -v) + v = w := by abel
    have key : w + -v ∈ logCover h ↔ w ∈ logCover h := by
      rw [← (hv (w + -v)).1, e]
    refine ⟨key, fun hw => ?_⟩
    have := (hv (w + -v)).2 (key.2 hw)
    rw [e] at this
    exact this.symm

variable {h}

lemma single_mem_periods {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w)
    (k : Fin n) (hk : k.val < a) : Pi.single k (2 * Real.pi * Complex.I) ∈ periods h φ := by
  have hkk : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
  intro w
  refine ⟨add_mem_logCover_iff h (fun j => ?_) (fun j hj => ?_) w, fun hw => ?_⟩
  · by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  · have : j ≠ k := fun e => by subst e; omega
    simp [this]
  · have := hφ ⟨k.val, hk⟩ w hw
    rwa [hkk] at this

lemma mem_periods_of {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {v : Fin n → ℂ}
    (hv : ∀ k : Fin n, (k.val < a → ∃ m : ℤ, v k = m * (2 * Real.pi * Complex.I)) ∧
      (a ≤ k.val → v k = 0)) :
    v ∈ periods h φ := by
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  by_cases hk : k.val < a
  · obtain ⟨m, hm⟩ := (hv k).1 hk
    have e : Pi.single k (v k) = m • (Pi.single k (2 * Real.pi * Complex.I) : Fin n → ℂ) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [hm, zsmul_eq_mul]
      · simp [hj]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (single_mem_periods hφ k hk) m
  · rw [(hv k).2 (by omega), Pi.single_zero]
    exact AddSubgroup.zero_mem _

lemma eq_of_exp_eq {φ : (Fin n → ℂ) → ℂ} (hφ : ∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) {w w' : Fin n → ℂ}
    (hw : w ∈ logCover h)
    (hd : ∀ k : Fin n, (k.val < a → Complex.exp (w' k) = Complex.exp (w k)) ∧
      (a ≤ k.val → w' k = w k)) :
    φ w' = φ w := by
  have hv : w' - w ∈ periods h φ := mem_periods_of hφ fun k => by
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 ((hd k).1 hk)
      exact ⟨m, by simp [hm]⟩
    · simp [(hd k).2 hk]
  have := (hv w).2 hw
  have e : w + (w' - w) = w' := by abel
  rwa [e] at this

def branchLift (a : ℕ) (z0 z : Fin n → ℂ) : Fin n → ℂ :=
  fun k => if k.val < a then Complex.log (z k / z0 k) + Complex.log (z0 k) else z k

omit h in
lemma analyticAt_eval (k : Fin n) (z : Fin n → ℂ) : AnalyticAt ℂ (fun z : Fin n → ℂ => z k) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt z

lemma ne_zero_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n)
    (hk : k.val < a) : z k ≠ 0 := by
  have := hz.2 ⟨k.val, hk⟩
  unfold cuspCoord at this
  rwa [show Fin.castLE h ⟨k.val, hk⟩ = k from Fin.ext rfl] at this

lemma norm_lt_one_of_mem {z : Fin n → ℂ} (hz : z ∈ puncturedChart h (ball 0 1)) (k : Fin n) :
    ‖z k‖ < 1 :=
  (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz.1)

omit h in
lemma exp_branchLift {z0 z : Fin n → ℂ} {k : Fin n} (hk : k.val < a) (h0 : z0 k ≠ 0)
    (hz : z k ≠ 0) : Complex.exp (branchLift a z0 z k) = z k := by
  simp only [branchLift, if_pos hk]
  rw [Complex.exp_add, Complex.exp_log (div_ne_zero hz h0), Complex.exp_log h0,
    div_mul_cancel₀ _ h0]

lemma branchLift_mem {z0 z : Fin n → ℂ} (h0 : z0 ∈ puncturedChart h (ball 0 1))
    (hz : z ∈ puncturedChart h (ball 0 1)) : branchLift a z0 z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    have e := exp_branchLift hi (ne_zero_of_mem h0 _ hi) (ne_zero_of_mem hz _ hi)
    have hn := norm_lt_one_of_mem hz (Fin.castLE h i)
    rw [← e, Complex.norm_exp] at hn
    exact Real.exp_lt_one_iff.1 hn
  · simp only [branchLift, if_neg (by omega : ¬ k.val < a)]
    exact norm_lt_one_of_mem hz k

omit h in
lemma analyticAt_branchLift {z0 : Fin n → ℂ} (h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0) :
    AnalyticAt ℂ (branchLift a z0) z0 := by
  refine AnalyticAt.pi (f := fun k z => branchLift a z0 z k) fun k => ?_
  by_cases hk : k.val < a
  · simp only [branchLift, if_pos hk]
    refine AnalyticAt.add (AnalyticAt.clog ?_ ?_) analyticAt_const
    · exact (analyticAt_eval k z0).div analyticAt_const (h0 k hk)
    · rw [div_self (h0 k hk)]
      exact Complex.one_mem_slitPlane
  · simp only [branchLift, if_neg hk]
    exact analyticAt_eval k z0

lemma isOpen_puncturedChart : IsOpen (puncturedChart h (ball (0 : Fin n → ℂ) 1)) := by
  have : puncturedChart h (ball (0 : Fin n → ℂ) 1) =
      ball 0 1 ∩ ⋂ j : Fin a, {z | z (Fin.castLE h j) ≠ 0} := by
    ext z; simp [puncturedChart, cuspCoord]
  rw [this]
  exact isOpen_ball.inter
    (isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply _) continuous_const)

end LogCoverDescent


open LogCoverDescent in
theorem LogCoverDescent.proof : LogCoverDescent.Statement := by
  intro n a h φ hφa hφ
  refine ⟨fun z0 hz0 => ?_, fun w hw => ?_⟩
  · have h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0 := ne_zero_of_mem hz0
    have hc : AnalyticAt ℂ (fun z => φ (branchLift a z0 z)) z0 :=
      (hφa _ (branchLift_mem hz0 hz0)).comp (analyticAt_branchLift h0)
    refine hc.congr ?_
    filter_upwards [(isOpen_puncturedChart (h := h)).mem_nhds hz0] with z hz
    symm
    refine eq_of_exp_eq hφ (branchLift_mem hz0 hz) fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [exp_branchLift hk (h0 k hk) (ne_zero_of_mem hz k hk)]
      simp only [logLift, if_pos hk]
      exact Complex.exp_log (ne_zero_of_mem hz k hk)
    · simp only [logLift, branchLift, if_neg (by omega : ¬ k.val < a)]
  · refine eq_of_exp_eq hφ hw fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · simp only [logLift, expCover, if_pos hk]
      exact Complex.exp_log (Complex.exp_ne_zero _)
    · simp only [logLift, expCover, if_neg (by omega : ¬ k.val < a)]

end

end GroundTheory.Heights₂.Heights.Regular
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Set
open ReciprocityTheory.AnForm.A

noncomputable section

theorem volume_real_closedBall_polydisc {D : ℕ} (x : Fin D → ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (closedBall x r) = (Real.pi * r ^ 2) ^ D := by
  rw [Measure.real, volume_pi_closedBall x hr]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  simp [mul_comm]

theorem MollifiedLowerBound.proof (h0 : SubMeanPolydiscStatement)
    (h1 : PolyMaxLogConvexStatement) : MollifiedLowerBound.Statement := by
  intro D ρ b U u z t hU hu ht hzU hb
  set M2 := polyMax u z (2 * t)
  set M4 := polyMax u z (t / 4)
  obtain ⟨-, -, hatt, -⟩ := h1 D U u z (2 * t) hU hu (by positivity) hzU
  obtain ⟨x, hx, hux⟩ := hatt (t / 4) (by positivity) (by linarith)
  rw [mem_closedBall] at hx
  set B := closedBall x (3 / 2 * t) with hBdef
  have hBz : B ⊆ closedBall z (2 * t) :=
    closedBall_subset_closedBall' (by linarith)
  have hzB : closedBall z t ⊆ B :=
    closedBall_subset_closedBall' (by rw [dist_comm]; linarith)
  obtain ⟨hint, hmean⟩ := h0 D U u x (3 / 2 * t) hU hu (by positivity) (hBz.trans hzU)
  rw [← hBdef] at hint hmean
  have hle2 : ∀ p ∈ B, u p ≤ M2 := fun p hp => le_polyMax hu.1 hzU (hBz hp)
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hb 0)
  have hV : volume.real B = (Real.pi * (3 / 2 * t) ^ 2) ^ D :=
    volume_real_closedBall_polydisc x (by positivity)
  have hVpos : 0 < volume.real B := by rw [hV]; positivity
  have hcint : IntegrableOn (fun _ => M2) B := integrableOn_const measure_closedBall_lt_top.ne

  have hIB : ∫ p in B, (M2 - u p) ≤ volume.real B * (M2 - M4) := by
    rw [integral_sub hcint hint, setIntegral_const, smul_eq_mul]
    rw [setAverage_eq, smul_eq_mul] at hmean
    have h := mul_le_mul_of_nonneg_left hmean hVpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hVpos.ne', one_mul] at h
    rw [show M4 = u x from hux.symm]
    linarith

  set g : (Fin D → ℂ) → ℝ := B.indicator (fun p => M2 - u p) with hgdef
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q
    by_cases hq : q ∈ B
    · rw [hgdef, indicator_of_mem hq]; exact sub_nonneg.2 (hle2 q hq)
    · rw [hgdef, indicator_of_notMem hq]
  have hgint : Integrable g :=
    (integrable_indicator_iff measurableSet_closedBall).2 (hcint.sub hint)
  have hBind : Integrable (B.indicator u) :=
    (integrable_indicator_iff measurableSet_closedBall).2 hint
  set c : ℝ := (t ^ (2 * D))⁻¹ * b with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hsc : ∀ y, ρ.scaled t y ≤ c := fun y =>
    mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have key : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) ≤
      ∫ y, c * g (z - y) := by
    refine integral_mono (((integrable_scaled ρ ht).mul_const M2).sub
      (integrable_kC ρ ht hBind z)) ((hgint.comp_sub_left z).const_mul c) fun y => ?_
    by_cases hy : ρ.scaled t y = 0
    · simp only [hy, zero_mul, sub_zero]
      exact mul_nonneg hc0 (hg0 _)
    · have hm : z - y ∈ B := hzB (mem_ball_sub ρ ht hy z)
      simp only [hgdef, indicator_of_mem hm]
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_right (hsc y) (sub_nonneg.2 (hle2 _ hm))
  have hLHS : ∫ y, (ρ.scaled t y * M2 - ρ.scaled t y * B.indicator u (z - y)) =
      M2 - molli ρ t u z := by
    rw [integral_sub ((integrable_scaled ρ ht).mul_const M2) (integrable_kC ρ ht hBind z),
      integral_mul_const, integral_scaled ρ ht, one_mul, molli_eq_C ρ ht hzB (φ := u)]
  have hRHS : ∫ y, c * g (z - y) = c * ∫ p in B, (M2 - u p) := by
    rw [integral_const_mul]
    congr 1
    have := (Measure.measurePreserving_sub_left volume z).integral_comp
      (Homeomorph.subLeft z).measurableEmbedding g
    rw [this, hgdef, integral_indicator measurableSet_closedBall]
  have hcV : c * volume.real B = Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b := by
    rw [hV, hcdef]
    have ht' : t ^ (2 * D) ≠ 0 := by positivity
    rw [mul_pow, ← pow_mul, mul_pow, pow_mul (3 / 2 : ℝ) 2 D]
    field_simp
  have hfin := mul_le_mul_of_nonneg_left hIB hc0
  have e : c * (volume.real B * (M2 - M4)) =
      Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b * (M2 - M4) := by
    rw [← hcV]; ring
  linarith

theorem MollifiedLowerBound.closed : MollifiedLowerBound.Statement :=
  MollifiedLowerBound.proof subMeanPolydisc_thm polyMaxLogConvex_thm

end

end GroundTheory.Heights₂.Heights.Regular
end

