module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0001
public import Formalism.HermitianCurvature.Bundle0001
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtPrim
section
open Set Filter Topology MeasureTheory intervalIntegral Metric

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def seg (w₀ x : ℂ) (t : ℝ) : ℂ := w₀ + (t : ℂ) * (x - w₀)

theorem seg_mem (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by
  have h := hc.add_smul_sub_mem hw₀ hx ht
  simpa [seg, Complex.real_smul] using h

theorem seg_one (w₀ x : ℂ) : seg w₀ x 1 = x := by
  simp [seg]

theorem continuous_seg : Continuous fun p : ℂ × ℝ => seg w₀ p.1 p.2 := by
  unfold seg
  fun_prop

theorem hasDerivAt_seg (x : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => seg w₀ x s) (x - w₀) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const (x - w₀)).const_add w₀
  simpa [seg] using h

theorem hasFDerivAt_seg (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)
  have h2 := h.const_add w₀
  have hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y := by
    funext y
    simp [seg, smul_eq_mul]
  rw [hf]
  exact h2

theorem prim_eq (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) :
    prim ω w₀ w = ∫ t in (0 : ℝ)..1, ω (seg w₀ w t) (w - w₀) := rfl

theorem hasFDerivAt_prim (hS : IsOpen S) (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) (hω : ContDiffOn ℝ 1 ω S)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} (hw : w ∈ S) :
    HasFDerivAt (prim ω w₀) (ω w) w := by
  have hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p := fun p hp =>
    (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt
  have hcontω : ContinuousOn ω S := hω.continuousOn
  have hcontD : ContinuousOn (fderiv ℝ ω) S := hω.continuousOn_fderiv_of_isOpen hS le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS w hw
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hcb : closedBall w δ' ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
  set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg
  have hKS : K ⊆ S := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact seg_mem hc hw₀ (hcb hx) ht
  have hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K := fun x hx t ht =>
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hcontω.mono hKS)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcontD.mono hKS)
  set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)
    with hF'
  have hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x := by
    intro x hx t ht
    have hs := hmemK x hx t ht
    have hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)
    have hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const w₀
    have h := hc1.clm_apply hu
    refine h.congr_fderiv ?_
    ext h'
    simp only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
    rw [show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]
    simp
  have hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1) := fun x _ =>
    (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine (hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hwc : w ∈ closedBall w δ' := mem_closedBall_self hδ'0.le
  have hLeib := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1)
    (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have hint : ∫ t in (0 : ℝ)..1, F' w t = ω w := by
      have hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        simp only [hF']
        congr 2
        ext h'
        simp only [ContinuousLinearMap.flip_apply]
        exact hsym _ hs h' (w - w₀)
      rw [intervalIntegral.integral_congr hEq]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s))
          (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        have h1 := (hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)
        have h2 := (hasDerivAt_id t).smul h1
        refine h2.congr_deriv ?_
        simp only [id, one_smul]
        abel
      have hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact (hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]
      simp [seg_one]
    rw [← hint]
    exact hLeib
  · filter_upwards [ball_mem_nhds w hδ'0] with x hx
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    rw [hIoc]
    exact (((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hωseg w hwc).clm_apply continuousOn_const
  · rw [hIoc]
    exact ((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    have hs := hmemK x hxc t ht'
    have h1 : ‖ω (seg w₀ x t)‖ ≤ M₁ := hM₁ _ hs
    have h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂ := hM₂ _ hs
    have h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w₀
      have hxw : ‖x - w‖ ≤ δ' := by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc
      linarith
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    simp only [hF']
    calc ‖ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖
        ≤ ‖ω (seg w₀ x t)‖ + ‖t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ := norm_add_le _ _
      _ ≤ M₁ + M₂ * (δ' + ‖w - w₀‖) := by
        refine add_le_add h1 ?_
        rw [norm_smul]
        have hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖) := by
          refine ((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul h2 h3 (norm_nonneg _) hM₂0
        have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
        calc ‖t‖ * ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ 1 * (M₂ * (δ' + ‖w - w₀‖)) :=
              mul_le_mul ht1 hf (norm_nonneg _) zero_le_one
          _ = M₂ * (δ' + ‖w - w₀‖) := one_mul _
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    exact hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
section
namespace Formalism.FourierDecayAlt.P.Interlace

open Finset Formalism.FourierDecayAlt.I

lemma interlaces_swap {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    Interlaces k u' u ρ := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := h i hi
  exact ⟨b, a, d, c⟩

lemma antitone_on {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by
  intro i j hi hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (h n (by omega) hjk).trans (ih (by omega))

lemma u_step {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by
  intro i h1 h2
  obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨h1, by omega⟩)
  linarith

lemma sign_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) (e : ℝ)
    (he : -1 ≤ e ∧ e ≤ 1) :
    0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hcard : (filter (fun i => ¬ i < l) (Icc 1 (k - 1))).card = k - l := by
    have : filter (fun i => ¬ i < l) (Icc 1 (k - 1)) = Icc l (k - 1) := by
      ext i; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  have key : (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) =
      ∏ i ∈ Icc 1 (k - 1), ((if i < l then (1 : ℝ) else -1) * (Y + e + ρ i)) := by
    rw [prod_mul_distrib, prod_ite, prod_const_one, one_mul, prod_const, hcard]
    rfl
  rw [key]
  apply prod_pos
  intro i hi
  have hi' := mem_Icc.1 hi
  obtain ⟨a, b, c, d⟩ := h i hi
  split_ifs with hil
  · have := hu' (i + 1) l (by omega) (by omega) hlk
    rw [one_mul]; linarith
  · have := hu l i hl1 (by omega) (by omega)
    rw [neg_one_mul]; linarith

theorem interlaceSign : InterlaceSign := by
  intro k u u' ρ l Y hl1 hlk h hc e he
  have he' : -1 ≤ e ∧ e ≤ 1 := by
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  rcases hc with hA | hB
  · exact sign_core k u u' ρ l Y hl1 hlk h hA e he'
  · exact sign_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB e he'

lemma q_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

theorem qPositive : QPositive := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core k u u' ρ l Y hl1 hlk h hA
    · have := q_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
      rwa [prod_congr rfl (fun i _ => mul_comm (Y + 1/2 + u' i) (Y + 1/2 + u i))] at this
  unfold qpoly
  nlinarith

lemma ratio_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  set g : ℕ → ℝ := fun j => |Y + 1/2 + u j| * |Y + 1/2 + u' j| with hg
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  have hR : |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| =
      g l * ∏ i ∈ Icc 1 (k - 1), g (if i < l then i else i + 1) := by
    rw [abs_mul, abs_prod, abs_prod, ← prod_mul_distrib, ← mul_prod_erase _ _ hl]
    congr 1
    symm
    apply prod_nbij' (fun i => if i < l then i else i + 1) (fun j => if j < l then j else j - 1)
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_erase, mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      simp only [mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      rfl
  rw [hR, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold xpoly
  rw [← prod_pow]
  apply prod_le_prod₀
  · intro i _; positivity
  · intro i hi
    have hi' := mem_Icc.1 hi
    obtain ⟨a, b, c, d⟩ := h i hi
    simp only [hg]
    split_ifs with hil
    · have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      nlinarith
    · have h1 := hu l i hl1 (by omega) (by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith

theorem interlaceRatio : InterlaceRatio := by
  intro k u u' ρ l Y hl1 hlk h hc
  rcases hc with hA | hB
  · exact ratio_core k u u' ρ l Y hl1 hlk h hA
  · have := ratio_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
    rwa [mul_comm (|Y + 1/2 + u' l|), mul_comm (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))] at this

end Formalism.FourierDecayAlt.P.Interlace

theorem Formalism.FourierDecayAlt.P.interlacing_sign : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.Interlace.interlaceSign
theorem Formalism.FourierDecayAlt.P.q_positive_interlacing : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.Interlace.qPositive
theorem Formalism.FourierDecayAlt.P.interlacing_ratio : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormIteratedFDerivWithinInvOneLe
section
open MeasureTheory Module Set
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_iteratedFDeriv_id_le (j : ℕ) (x : V) : ‖iteratedFDeriv ℝ j (id : V → V) x‖ ≤ 1 + ‖x‖ := by
  rcases j with _ | _ | m
  · rw [norm_iteratedFDeriv_zero]
    simp
  · rw [norm_iteratedFDeriv_one, fderiv_id]
    exact (ContinuousLinearMap.norm_id_le).trans (by linarith [norm_nonneg x])
  · rw [iteratedFDeriv_succ_eq_comp_right]
    have e : (fun y : V => fderiv ℝ (id : V → V) y) = fun _ => ContinuousLinearMap.id ℝ V := by
      funext y
      exact fderiv_id
    rw [e, iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0)]
    simp
    positivity

theorem norm_iteratedFDeriv_inner_self_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
  have hB := (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear
    (f := (id : V → V)) (g := (id : V → V)) (N := ⊤) contDiff_id contDiff_id x (n := n) le_top
  have e : (fun y : V => (innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ) (id y) (id y)) = fun y : V => inner ℝ y y := by
    funext y
    simp
  rw [e] at hB
  have hnB : ‖(innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ ≤ 2 ^ n * (1 + ‖x‖) ^ 2 := by
    calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
          ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖
        ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖x‖) * (1 + ‖x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := norm_iteratedFDeriv_id_le i x
          have h2 := norm_iteratedFDeriv_id_le (n - i) x
          have hc : (0 : ℝ) ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
          gcongr
      _ = 2 ^ n * (1 + ‖x‖) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [this]
          ring
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (id : V → V) x‖ *
      ‖iteratedFDeriv ℝ (n - i) (id : V → V) x‖ := Finset.sum_nonneg fun i _ => by positivity
  calc ‖iteratedFDeriv ℝ n (fun y : V => inner ℝ y y) x‖ ≤ _ := hB
    _ ≤ 1 * (2 ^ n * (1 + ‖x‖) ^ 2) := mul_le_mul hnB hsum hS0 zero_le_one
    _ = 2 ^ n * (1 + ‖x‖) ^ 2 := one_mul _

theorem norm_iteratedFDerivWithin_inv_one_le (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) 1‖ ≤ i ! := by
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    (iteratedDerivWithin_of_isOpen isOpen_Ioi) (show (1 : ℝ) ∈ Ioi 0 by norm_num), iteratedDeriv_eq_iterate]
  have e : (fun t : ℝ => t⁻¹) = Inv.inv := rfl
  rw [e, iter_deriv_inv]
  simp

theorem norm_iteratedFDeriv_u_le (k : ℕ) (x₀ : V) :
    ‖iteratedFDeriv ℝ k (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x₀‖ ≤ (k ! * k ! * 4 ^ k) * (1 + ‖x₀‖ ^ 2)⁻¹ := by
  set q₀ : ℝ := 1 + ‖x₀‖ ^ 2 with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  set f : V → ℝ := fun y => q₀⁻¹ * (1 + inner ℝ y y) with hf
  have hfpos : ∀ y, 0 < f y := fun y => by
    simp only [hf, real_inner_self_eq_norm_sq]; positivity
  have hfc : ContDiff ℝ k f :=
    contDiff_const.mul (contDiff_const.add (contDiff_id.inner ℝ contDiff_id))
  have hfx : f x₀ = 1 := by
    simp only [hf, real_inner_self_eq_norm_sq]
    rw [← hq₀]
    exact inv_mul_cancel₀ hq₀pos.ne'
  have hu : (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) = q₀⁻¹ • ((fun t : ℝ => t⁻¹) ∘ f) := by
    funext y
    simp only [hf, Pi.smul_apply, Function.comp, real_inner_self_eq_norm_sq, smul_eq_mul]
    field_simp
  have hgc : ContDiff ℝ k ((fun t : ℝ => t⁻¹) ∘ f) :=
    hfc.inv fun y => (hfpos y).ne'
  rw [hu, iteratedFDeriv_const_smul_apply (hgc.contDiffAt), norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hq₀pos), mul_comm]
  gcongr
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x₀‖ ≤ 4 ^ i := by
    intro i hi _
    have e : f = (fun _ : V => q₀⁻¹) + q₀⁻¹ • (fun y : V => inner ℝ y y) := by
      funext y; simp only [hf, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hin : ContDiff ℝ i (fun y : V => inner ℝ y y) := contDiff_id.inner ℝ contDiff_id
    have hc2 : ContDiffAt ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)) x₀ :=
      ((hin.const_smul q₀⁻¹ : ContDiff ℝ i (q₀⁻¹ • (fun y : V => inner ℝ y y)))).contDiffAt
    have hc1 : ContDiffAt ℝ i (fun _ : V => q₀⁻¹) x₀ := contDiffAt_const
    rw [e, iteratedFDeriv_add_apply hc1 hc2,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add,
      iteratedFDeriv_const_smul_apply hin.contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq₀pos)]
    have h1 := norm_iteratedFDeriv_inner_self_le i x₀
    have h2 : (1 + ‖x₀‖) ^ 2 ≤ 2 * q₀ := by
      rw [hq₀]; nlinarith [sq_nonneg (‖x₀‖ - 1)]
    have h3 : (2 : ℝ) ^ i * 2 ≤ 4 ^ i := by
      have : (4 : ℝ) ^ i = 2 ^ i * 2 ^ i := by rw [← mul_pow]; norm_num
      rw [this]
      gcongr
      exact le_self_pow₀ (by norm_num) (by omega)
    calc q₀⁻¹ * ‖iteratedFDeriv ℝ i (fun y : V => inner ℝ y y) x₀‖ ≤ q₀⁻¹ * (2 ^ i * (2 * q₀)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = 2 ^ i * 2 := by field_simp
      _ ≤ 4 ^ i := h3
  have hC : ∀ i, i ≤ k → ‖iteratedFDerivWithin ℝ i (fun t : ℝ => t⁻¹) (Ioi 0) (f x₀)‖ ≤ k ! := by
    intro i hi
    rw [hfx]
    exact (norm_iteratedFDerivWithin_inv_one_le i).trans (by exact_mod_cast Nat.factorial_le hi)
  have hmain := norm_iteratedFDeriv_comp_le' (N := (k : ℕ∞)) (t := Ioi (0 : ℝ))
    (by rintro _ ⟨y, rfl⟩; exact hfpos y) (uniqueDiffOn_Ioi 0)
    (ContDiffOn.mono (contDiffOn_inv (𝕜 := ℝ)) (fun t (ht : t ∈ Ioi (0 : ℝ)) => (ne_of_gt ht : t ≠ 0))) hfc le_rfl x₀ hC hD
  calc ‖iteratedFDeriv ℝ k ((fun t : ℝ => t⁻¹) ∘ f) x₀‖ ≤ k ! * k ! * 4 ^ k := hmain
    _ = k ! * k ! * 4 ^ k := rfl

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferProductMonic
section
namespace Formalism.FourierDecayAlt.P.Misc

open Formalism.FourierDecayAlt.I Finset Polynomial

theorem selfDualG_holds : SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩
    have h2 := h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩
    simp only [mul_one, mul_zero, sub_zero] at h1 h2
    have e2 : a.1 * q / q = a.1 := by field_simp
    rw [e2] at h2
    refine ⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩
    have : a.2 = a.1 - q * ((a.1 - a.2) / q) := by field_simp; ring
    rw [this]; exact o.sub_mem h2 (o.mul_mem hq h1)
  · rintro ⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩
    have ha : a.1 = a.2 + q * s := by linear_combination has
    have hb : b.1 = b.2 + q * t := by linear_combination hbt
    have e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)

end Formalism.FourierDecayAlt.P.Misc

theorem Formalism.FourierDecayAlt.P.self_dual_gamma : Formalism.FourierDecayAlt.I.SelfDualG := Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
end

