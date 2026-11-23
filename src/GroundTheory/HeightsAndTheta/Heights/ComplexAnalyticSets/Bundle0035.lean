module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices

open scoped Real

noncomputable section

namespace OsgoodSeparate

theorem cons_mem_ball {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := pos_of_mem_ball hx
  refine (mem_ball_pi_iff hR).mpr fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa [Fin.tail] using (mem_ball_pi_iff hR).mp hy j

theorem cauchy_torus : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  | 0, G, c, _, _, _, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, G, c, R, hc, hs, r, hr0, hrR, z, hz => by
    have htor : ∀ θ, torusMap c (fun _ => r) θ ∈ ball c R := fun θ =>
      closedBall_subset_ball hrR (torusMap_mem_closedBall c hr0.le θ)
    have hint : TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * G ζ) c (fun _ => r) := by
      refine ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn ?_)
      refine Continuous.mul ?_ (hc.comp_continuous (continuous_torusMap c r) htor)
      refine continuous_finsetProd _ fun i _ => Continuous.inv₀ ?_ fun θ => torusMap_sub_ne hr0 hz θ i
      exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    refine (torusIntegral_succ hint).trans ?_
    have hz' : Fin.tail z ∈ ball (Fin.tail c) r :=
      (mem_ball_pi_iff hr0).mpr fun i => by simpa [Fin.tail] using (mem_ball_pi_iff hr0).mp hz i.succ
    have hz'R : Fin.tail z ∈ ball (Fin.tail c) R := ball_subset_ball hrR.le hz'
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr0).mp hz 0
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * G (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * G (Fin.cons x (Fin.tail z))))
        (sphere (c 0) r) := by
      intro x hx
      have hxR : x ∈ ball (c 0) R := mem_ball.mpr (by rw [mem_sphere.mp hx]; exact hrR)
      have hc' : ContinuousOn (fun y => G (Fin.cons x y)) (ball (Fin.tail c) R) :=
        hc.comp (differentiable_cons_right x).continuous.continuousOn fun y hy => cons_mem_ball hxR hy
      have hs' : ∀ w ∈ ball (Fin.tail c) R, ∀ i : Fin n,
          DifferentiableAt ℂ (fun t => (fun y => G (Fin.cons x y)) (Function.update w i t)) (w i) := by
        intro w hw i
        have h := hs _ (cons_mem_ball hxR hw) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      have ih := cauchy_torus n (fun y => G (Fin.cons x y)) (Fin.tail c) R hc' hs' r hr0 hrR
        (Fin.tail z) hz'
      have e0 : c ∘ Fin.succ = Fin.tail c := rfl
      have e1 : ((fun _ : Fin (n + 1) => r) ∘ Fin.succ) = fun _ => r := rfl
      simp only [e0, e1]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr0.le key, circleIntegral.integral_const_mul]
    have hcont : ContinuousOn (fun x => G (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      hc.comp (differentiable_cons_left (Fin.tail z)).continuous.continuousOn fun x hx =>
        cons_mem_ball (closedBall_subset_ball hrR hx) hz'R
    have hdiff : ∀ x ∈ ball (c 0) r \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun x => G (Fin.cons x (Fin.tail z))) x := by
      intro x hx
      have h := hs _ (cons_mem_ball (ball_subset_ball hrR.le hx.1) hz'R) 0
      simp only [Fin.cons_zero, Fin.update_cons_zero] at h
      exact h
    have h1 := circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      hz0 hcont hdiff
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end OsgoodSeparate


open OsgoodSeparate in
theorem analyticOnNhd_of_continuousOn_of_separately {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    AnalyticOnNhd ℂ g U := by
  intro c hcU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hcU
  have hr : 0 < ε / 2 := half_pos hε
  have hrε : ε / 2 < ε := half_lt_self hε
  have hcb : ContinuousOn g (ball c ε) := hc.mono hball
  have hsb : ∀ z ∈ ball c ε, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i) :=
    fun z hz => hs z (hball hz)
  have htor : Continuous fun θ => g (torusMap c (fun _ => ε / 2) θ) :=
    hcb.comp_continuous (continuous_torusMap c _) fun θ =>
      closedBall_subset_ball hrε (torusMap_mem_closedBall c hr.le θ)
  set L := torusFunctional c (ε / 2) g htor
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have han : AnalyticAt ℂ (fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern c (ε / 2) z)) c :=
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem c hr (mem_ball_self hr)))
  refine han.congr ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl c (ε / 2) g (kern c (ε / 2) z) = g z
  rw [fctl_kern hr g hz, OsgoodSeparate.cauchy_torus n g c ε hcb hsb (ε / 2) hr hrε z hz, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

namespace AnalyticGermComponents

variable {σ : Type} [Fintype σ]

def vanishingIdeal (X : Set (σ → ℂ)) (w : σ → ℂ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0}
  add_mem' := by
    rintro a b ⟨f, hf, hf0⟩ ⟨g, hg, hg0⟩
    refine ⟨f + g, ?_, ?_⟩
    · show ((f + g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (a : Germ (𝓝 w) ℂ) + (b : Germ (𝓝 w) ℂ)
      rw [← hf, ← hg]
      rfl
    · filter_upwards [hf0, hg0] with z h1 h2 hz
      simp [h1 hz, h2 hz]
  zero_mem' := ⟨0, rfl, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hf0⟩
    obtain ⟨h, -, hh⟩ := c.2
    refine ⟨h * f, ?_, ?_⟩
    · show ((h * f : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (c : Germ (𝓝 w) ℂ) * (a : Germ (𝓝 w) ℂ)
      rw [← hh, ← hf]
      rfl
    · filter_upwards [hf0] with z h1 hz
      simp [h1 hz]

theorem mem_vanishingIdeal_iff {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) :
    (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal X w ↔ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0 := by
  constructor
  · rintro ⟨g, hg, hg0⟩
    have he : g =ᶠ[𝓝 w] f := Germ.coe_eq.1 hg
    filter_upwards [hg0, he] with z h1 h2 hz
    rw [← h2]
    exact h1 hz
  · intro h
    exact ⟨f, rfl, h⟩

theorem vanishingIdeal_anti {X X' : Set (σ → ℂ)} {w : σ → ℂ} (hXX' : X' ⊆ X) :
    vanishingIdeal X w ≤ vanishingIdeal X' w := by
  rintro φ ⟨f, hf, hf0⟩
  refine ⟨f, hf, ?_⟩
  filter_upwards [hf0] with z h hz
  exact h (hXX' hz)

theorem isAnalyticNear_inter_zero {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hX : IsAnalyticNear X w) (hf : AnalyticAt ℂ f w) : IsAnalyticNear (X ∩ {z | f z = 0}) w := by
  obtain ⟨N, k, F, hN, hwN, hF, hXN⟩ := hX
  refine ⟨N ∩ {z | AnalyticAt ℂ f z}, k + 1, Fin.cons f F, hN.inter (isOpen_analyticAt ℂ f), ⟨hwN, hf⟩, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro z hz
      simpa using hz.2
    · intro z hz
      simpa using hF j z hz.1
  · ext z
    have e := Set.ext_iff.1 hXN z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at e ⊢
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    constructor
    · rintro ⟨⟨hzX, hfz⟩, hzN, hza⟩
      exact ⟨⟨hzN, hza⟩, hfz, (e.1 ⟨hzX, hzN⟩).2⟩
    · rintro ⟨⟨hzN, hza⟩, hfz, hFz⟩
      exact ⟨⟨(e.2 ⟨hzN, hFz⟩).1, hfz⟩, hzN, hza⟩

theorem apply_eq_zero_of_not {X : Set (σ → ℂ)} {w : σ → ℂ} {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hfg : ∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) (hng : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) : f w = 0 := by
  by_contra h0
  apply hng
  have hev : ∀ᶠ z in 𝓝 w, f z ≠ 0 := hf.continuousAt.eventually_ne h0
  filter_upwards [hfg, hev] with z h1 h2 hz
  exact (mul_eq_zero.1 (h1 hz)).resolve_left h2

theorem vanishingIdeal_lt {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by
  refine lt_of_le_of_ne (vanishingIdeal_anti Set.inter_subset_left) fun heq => hnf ?_
  have hm : (⟨(f : Germ (𝓝 w) ℂ), f, hf, rfl⟩ : holGerms w) ∈ vanishingIdeal (X ∩ {z | f z = 0}) w :=
    (mem_vanishingIdeal_iff hf).2 (Eventually.of_forall fun z hz => hz.2)
  rw [← heq] at hm
  exact (mem_vanishingIdeal_iff hf).1 hm

theorem exists_finset {w : σ → ℂ} (hN : IsNoetherianRing (holGerms w)) (X : Set (σ → ℂ))
    (hX : IsAnalyticNear X w) (hw : w ∈ X) :
    ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
      ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W := by
  classical
  suffices H : ∀ J : Ideal (holGerms w), ∀ X : Set (σ → ℂ), vanishingIdeal X w = J → IsAnalyticNear X w →
      w ∈ X → ∃ s : Finset (Set (σ → ℂ)), (∀ Y ∈ s, IsAnalyticNear Y w ∧ GermIrreducibleAt Y w) ∧
        ∃ W ∈ 𝓝 w, X ∩ W = (⋃ Y ∈ s, Y) ∩ W from H _ X rfl hX hw
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro X hJ hX hw
  by_cases hirr : GermIrreducibleAt X w
  · refine ⟨{X}, ?_, Set.univ, Filter.univ_mem, ?_⟩
    · intro Y hY
      rw [Finset.mem_singleton] at hY
      exact hY ▸ ⟨hX, hirr⟩
    · simp
  obtain ⟨f, g, hf, hg, hfg, hnf, hng⟩ : ∃ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ AnalyticAt ℂ g w ∧
      (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) ∧ ¬ (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∧
      ¬ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0) := by
    by_contra hcon
    refine hirr ⟨hw, fun f g hf hg hfg => ?_⟩
    by_contra h
    rw [not_or] at h
    exact hcon ⟨f, g, hf, hg, hfg, h.1, h.2⟩
  have hgf : ∀ᶠ z in 𝓝 w, z ∈ X → g z * f z = 0 := by
    filter_upwards [hfg] with z h hz
    rw [mul_comm]
    exact h hz
  have hfw : f w = 0 := apply_eq_zero_of_not hf hfg hng
  have hgw : g w = 0 := apply_eq_zero_of_not hg hgf hnf
  obtain ⟨s₁, hs₁, W₁, hW₁, hX₁⟩ := ih _ (hJ ▸ vanishingIdeal_lt hf hnf) _ rfl
    (isAnalyticNear_inter_zero hX hf) ⟨hw, hfw⟩
  obtain ⟨s₂, hs₂, W₂, hW₂, hX₂⟩ := ih _ (hJ ▸ vanishingIdeal_lt hg hng) _ rfl
    (isAnalyticNear_inter_zero hX hg) ⟨hw, hgw⟩
  refine ⟨s₁ ∪ s₂, ?_, W₁ ∩ W₂ ∩ {z | z ∈ X → f z * g z = 0}, inter_mem (inter_mem hW₁ hW₂) hfg, ?_⟩
  · intro Y hY
    rcases Finset.mem_union.1 hY with h | h
    · exact hs₁ Y h
    · exact hs₂ Y h
  ext z
  have e₁ := Set.ext_iff.1 hX₁ z
  have e₂ := Set.ext_iff.1 hX₂ z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] at e₁ e₂
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.mem_union]
  constructor
  · rintro ⟨hzX, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases mul_eq_zero.1 (hz0 hzX) with h | h
    · obtain ⟨Y, hY, hzY⟩ := (e₁.1 ⟨⟨hzX, h⟩, hz₁⟩).1
      exact ⟨Y, Or.inl hY, hzY⟩
    · obtain ⟨Y, hY, hzY⟩ := (e₂.1 ⟨⟨hzX, h⟩, hz₂⟩).1
      exact ⟨Y, Or.inr hY, hzY⟩
  · rintro ⟨⟨Y, hY, hzY⟩, ⟨hz₁, hz₂⟩, hz0⟩
    refine ⟨?_, ⟨hz₁, hz₂⟩, hz0⟩
    rcases hY with hY | hY
    · exact (e₁.2 ⟨⟨Y, hY, hzY⟩, hz₁⟩).1.1
    · exact (e₂.2 ⟨⟨Y, hY, hzY⟩, hz₂⟩).1.1

theorem proof (hN : AnalyticGermsNoetherian.Statement) : AnalyticGermComponents.Statement := by
  intro σ _ X w hX hw
  obtain ⟨s, hs, W, hW, hXW⟩ := exists_finset (hN σ w) X hX hw
  refine ⟨s.card, fun i => (s.equivFin.symm i : Set (σ → ℂ)), fun i => hs _ (s.equivFin.symm i).2, W, hW, ?_⟩
  rw [hXW]
  congr 1
  ext z
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨Y, hY, hz⟩
    exact ⟨s.equivFin ⟨Y, hY⟩, by simpa using hz⟩
  · rintro ⟨i, hz⟩
    exact ⟨_, (s.equivFin.symm i).2, hz⟩

end AnalyticGermComponents

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

theorem realGraphPt_injective {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)) :
    Function.Injective (realGraphPt F) := by
  intro x y hxy
  ext i
  simpa [realGraphPt] using congrArg (fun z : EuclideanSpace ℝ (Fin k ⊕ Fin m) => z (Sum.inl i)) hxy

theorem realGraphPt_continuousOn {k m : ℕ} {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin k))} (hF : ContinuousOn F s) : ContinuousOn (realGraphPt F) s := by
  unfold realGraphPt
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  rcases i with i | i
  · exact (PiLp.continuous_apply 2 _ i).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF

theorem AreaGraphBound.proof (h₁ : AreaGraphPiece.Statement) (h₂ : AreaGraphPartition.Statement)
    (h₃ : GraphJacContinuous.Statement) : AreaGraphBound.Statement := by
  intro k m U F hU hF A hAU hA δ hδ0 hδ1
  set J : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0∞ := fun B =>
    ENNReal.ofReal (graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) with hJ
  set c : ℝ≥0∞ := ((1 + δ : ℝ≥0) : ℝ≥0∞) with hc

  choose r₃ hr₃0 hr₃ using fun B => h₃ k m B δ (by exact_mod_cast hδ0)
  obtain ⟨t, An, hdisj, htm, -, hcov, happrox, hder⟩ :=
    h₂ k m U F hU hF (fun B => min δ (r₃ B).toNNReal)
      (fun B => (lt_min hδ0 (Real.toNNReal_pos.2 (hr₃0 B))).ne')
  set p : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => A ∩ t n with hp
  have hpm : ∀ n, MeasurableSet (p n) := fun n => hA.inter (htm n)
  have hpd : Pairwise (Function.onFun Disjoint p) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAp : A = ⋃ n, p n := by
    rw [← Set.inter_iUnion]
    exact (Set.inter_eq_left.2 (hAU.trans hcov)).symm

  have hcmp : ∀ n, ∀ x ∈ p n, J (fderiv ℝ F x) ≤ c * J (An n) ∧ J (An n) ≤ c * J (fderiv ℝ F x) := by
    intro n x hx
    have hle : ‖fderiv ℝ F x - An n‖ ≤ r₃ (An n) := by
      have := (hder n x hx.2).trans (min_le_right _ _)
      have h' : ((‖fderiv ℝ F x - An n‖₊ : ℝ≥0) : ℝ) ≤ ((r₃ (An n)).toNNReal : ℝ) := by exact_mod_cast this
      simpa [Real.coe_toNNReal _ (hr₃0 (An n)).le] using h'
    obtain ⟨h1, h2⟩ := hr₃ (An n) (fderiv ℝ F x) hle
    have e : ∀ y : ℝ, ENNReal.ofReal ((1 + δ) * y) = c * ENNReal.ofReal y := fun y => by
      rw [ENNReal.ofReal_mul (by positivity), hc]; congr 1
      rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    exact ⟨(ENNReal.ofReal_le_ofReal h1).trans (e _).le, (ENNReal.ofReal_le_ofReal h2).trans (e _).le⟩

  have hpiece : ∀ n, μH[(k : ℝ)] (realGraphPt F '' p n) ≤ c ^ (k + 1) * ∫⁻ x in p n, J (fderiv ℝ F x)
      ∂(μH[(k : ℝ)]) ∧ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
        c * μH[(k : ℝ)] (realGraphPt F '' p n) := by
    intro n
    obtain ⟨u, l⟩ := h₁ k m F (An n) δ (p n) hδ1
      (((happrox n).mono_set Set.inter_subset_right).mono_num (min_le_left _ _))
    have i₁ : J (An n) * μH[(k : ℝ)] (p n) ≤ c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).2
    have i₂ : ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤ c * (J (An n) * μH[(k : ℝ)] (p n)) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).1
    constructor
    · calc _ ≤ c ^ k * (J (An n) * μH[(k : ℝ)] (p n)) := by rw [← mul_assoc]; exact u
        _ ≤ c ^ k * (c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)])) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
    · calc _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * (c * (J (An n) * μH[(k : ℝ)] (p n))) := by gcongr
        _ = c * (((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * J (An n) * μH[(k : ℝ)] (p n)) := by ring
        _ ≤ _ := by gcongr

  have hG : ∀ n, MeasurableSet (realGraphPt F '' p n) := fun n =>
    (hpm n).image_of_continuousOn_injOn
      (realGraphPt_continuousOn (hF.continuousOn.mono (Set.inter_subset_left.trans hAU)))
      (realGraphPt_injective F).injOn
  have hGd : Pairwise (Function.onFun Disjoint fun n => realGraphPt F '' p n) := fun i j hij =>
    (Set.disjoint_image_iff (realGraphPt_injective F)).2 (hpd hij)
  have hS : μH[(k : ℝ)] (realGraphPt F '' A) = ∑' n, μH[(k : ℝ)] (realGraphPt F '' p n) := by
    rw [hAp, Set.image_iUnion, measure_iUnion hGd hG]
  have hI : ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) =
      ∑' n, ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
    rw [hAp, lintegral_iUnion hpm hpd]
  change μH[(k : ℝ)] (realGraphPt F '' A) ≤ c ^ (k + 1) * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ∧
    ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
      c * μH[(k : ℝ)] (realGraphPt F '' A)
  rw [hS, hI, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun n => (hpiece n).1, ENNReal.tsum_le_tsum fun n => (hpiece n).2⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchContainsNormalPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem HolomorphicOnSubset.continuousWithinAt {σ : Type*} [Fintype σ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : (σ → ℂ) → E} {S : Set (σ → ℂ)}
    (hf : HolomorphicOnSubset f S) {z : σ → ℂ} (hz : z ∈ S) : ContinuousWithinAt f S z := by
  obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hf z hz
  have hc : ContinuousWithinAt F S z :=
    (hF.differentiableAt (hUo.mem_nhds hzU)).continuousAt.continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (hFeq ⟨hz, hzU⟩)
  filter_upwards [inter_mem_nhdsWithin S (hUo.mem_nhds hzU)] with y hy
  exact hFeq hy

theorem BranchContainsNormalPoint.proof (hirr : NormalLocallyIrreducible.Statement)
    (hinv : BranchInverseHolomorphic.Statement) (hext : NormalRiemannExtension.Statement)
    (hmax : NormalMaximumPrinciple.Statement) : BranchContainsNormalPoint.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  obtain ⟨B', hB'o, hwB', hB'B, -, hdense⟩ := hirr σ I h w hI hIc hh hw B hB
  set P := (zeroSetIn I ∩ B') \ {z | eval z h = 0} with hP
  have hPfill : P ⊆ φ '' Metric.ball 0 r := fun z hz => hfill ⟨⟨hz.1.1, hB'B hz.1.2⟩, hz.2⟩
  have hPsub : P ⊆ zeroSetIn I ∩ B' := fun y hy => hy.1
  have hwcl : w ∈ closure P := hdense ⟨hw, hwB'⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hinv σ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  have hPψ : ∀ z ∈ P, ψ z ∈ Metric.ball (0 : Fin k → ℂ) r ∧ φ (ψ z) = z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hPfill hz
    rw [hψφ t ht]
    exact ⟨ht, rfl⟩
  have hPlt : ∀ z ∈ P, ∀ j, ‖ψ z j‖ < r := fun z hz j =>
    (norm_le_pi_norm (ψ z) j).trans_lt (mem_ball_zero_iff.mp (hPψ z hz).1)

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ B') ∧
      Set.EqOn g (fun z => ψ z j) P := by
    intro j
    refine hext σ I h B' (fun z => ψ z j) hI hIc hh hB'o ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψ z (hPfill hz)
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq ⟨hPfill hy.1, hy.2⟩) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hPlt z hz j).le
  choose g hg hgeq using hcoord

  have hgle : ∀ j, ∀ z ∈ zeroSetIn I ∩ B', ‖g j z‖ ≤ r := by
    intro j z hz
    have hcl := (((hg j).continuousWithinAt hz).mono hPsub).mem_closure_image (hdense hz)
    have hsub : g j '' P ⊆ Metric.closedBall 0 r := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hgeq j hy]
      exact (hPlt y hy j).le
    have := closure_minimal hsub Metric.isClosed_closedBall hcl
    rwa [Metric.mem_closedBall, dist_zero_right] at this

  have hglt : ∀ j, ‖g j w‖ < r := by
    intro j
    by_contra hlt
    have heq : ‖g j w‖ = r := le_antisymm (hgle j w ⟨hw, hwB'⟩) (not_lt.mp hlt)
    have hev := hmax σ I w B' (g j) hI hIc hw (hB'o.mem_nhds hwB') (hg j)
      (fun z hz => (hgle j z hz).trans heq.ge)
    obtain ⟨z, hz, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ hev
    have h1 : ‖g j z‖ < r := (congrArg norm (hgeq j hzP)).trans_lt (hPlt z hzP j)
    rw [hz hzP.1.1, heq] at h1
    exact lt_irrefl r h1
  have hr : 0 < r := by
    obtain ⟨z, -, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ Filter.univ_mem
    exact (norm_nonneg _).trans_lt (mem_ball_zero_iff.mp (hPψ z hzP).1)
  set t₀ : Fin k → ℂ := fun j => g j w with ht₀
  have ht₀Δ : t₀ ∈ Metric.ball (0 : Fin k → ℂ) r := mem_ball_zero_iff.mpr ((pi_norm_lt_iff hr).mpr hglt)
  refine ⟨t₀, ht₀Δ, ?_⟩

  have : (𝓝[P] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwcl
  have hG : Tendsto (fun z => fun j => g j z) (𝓝[P] w) (𝓝 t₀) :=
    tendsto_pi_nhds.mpr fun j => (((hg j).continuousWithinAt ⟨hw, hwB'⟩).mono hPsub).tendsto
  have hφc : ContinuousAt φ t₀ := (hφd.differentiableAt (Metric.isOpen_ball.mem_nhds ht₀Δ)).continuousAt
  have h1 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 (φ t₀)) := hφc.tendsto.comp hG
  have h2 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hgz : (fun j => g j z) = ψ z := funext fun j => hgeq j hz
    rw [hgz, (hPψ z hz).2]
    rfl
  exact tendsto_nhds_unique h1 h2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

