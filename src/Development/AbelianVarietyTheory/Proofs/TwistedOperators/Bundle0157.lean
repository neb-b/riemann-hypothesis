module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffOfContinuousQuasiMultiplicativeSmoothDef
section
open MeasureTheory

open Metric Set Filter Topology Convolution

namespace GlobalTheory.FuncEqSmooth

theorem contDiff_of_func_eq (c : ℝ → ℂ) (E : ℝ → ℝ → ℂ) (U : Set (ℝ × ℝ)) (hc : Continuous c)
    (hc0 : c 0 ≠ 0) (hU : IsOpen U) (hUs : ∀ s, (s, 0) ∈ U)
    (hE : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U)
    (hfe : ∀ p ∈ U, c (p.1 + p.2) = c p.1 * c p.2 * E p.1 p.2) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
  have h00 : ((0:ℝ), (0:ℝ)) ∈ U := hUs 0
  have hw0 : c 0 * E 0 0 = 1 := by
    have h1 := hfe (0,0) h00
    simp only [add_zero] at h1
    have h2 : c 0 * (c 0 * E 0 0) = c 0 * 1 := by rw [mul_one, ← mul_assoc]; exact h1.symm
    exact mul_left_cancel₀ hc0 h2
  have hEcont : ContinuousAt (fun p : ℝ × ℝ => E p.1 p.2) (0,0) :=
    hE.continuousOn.continuousAt (hU.mem_nhds h00)
  have hwcont : ContinuousAt (fun v : ℝ => c v * E 0 v) 0 := by
    have h1 : ContinuousAt (fun v : ℝ => E (0:ℝ) v) 0 :=
      hEcont.comp (f := fun v : ℝ => ((0:ℝ), v)) (by fun_prop)
    exact hc.continuousAt.mul h1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ h00
  obtain ⟨δ, hδ, hwδ⟩ := Metric.continuousAt_iff.1 hwcont (1/2) (by norm_num)
  set r := min ε δ with hr
  have hr0 : 0 < r := lt_min hε hδ
  have hbox : ∀ a b : ℝ, |a| < r → |b| < r → (a, b) ∈ U := by
    intro a b ha hb
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero]
    exact ⟨lt_of_lt_of_le ha (min_le_left _ _), lt_of_lt_of_le hb (min_le_left _ _)⟩

  let ψ : ContDiffBump (0:ℝ) := ⟨r/4, r/2, by positivity, by linarith⟩
  set φ : ℝ → ℝ := ψ.normed volume with hφdef
  have hφ0 : ∀ x : ℝ, r/2 ≤ |x| → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support, hφdef, ψ.support_normed_eq, mem_ball, Real.dist_eq, sub_zero]
    show ¬ |x| < r/2
    linarith
  have hφs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := ψ.contDiff_normed
  let φr : ℝ → ℂ := fun y => ((φ y : ℝ) : ℂ)
  have hφr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φr := Complex.ofRealCLM.contDiff.comp hφs
  have hφr0 : ∀ x : ℝ, r/2 ≤ |x| → φr x = 0 := by
    intro x hx; simp [φr, hφ0 x hx]

  let A : ℝ → ℂ := c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have hcs : HasCompactSupport (fun y => φr (-y)) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0:ℝ) (r/2)) (fun y hy => ?_)
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hy
      exact hφr0 _ (by rw [abs_neg]; exact hy.le)
    exact hcs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℂ) hc.locallyIntegrable
      (hφr.comp contDiff_neg)

  let G : ℝ → ℝ → ℂ := fun t y => φr (-y) * E t (-y)
  let h : ℝ → ℂ := fun t => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry G) (ball (0:ℝ) r ×ˢ univ) := by
    intro q hq
    apply ContDiffAt.contDiffWithinAt
    have hq1 : |q.1| < r := by
      have := hq.1; rw [mem_ball, Real.dist_eq, sub_zero] at this; exact this
    by_cases hq2 : |q.2| < r
    · have hmem : (q.1, -q.2) ∈ U := hbox _ _ hq1 (by rw [abs_neg]; exact hq2)
      have hEat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) (q.1, -q.2) :=
        hE.contDiffAt (hU.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => E q.1 (-q.2)) q :=
        hEat.comp (f := fun q : ℝ × ℝ => (q.1, -q.2)) q (by fun_prop)
      have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => φr (-q.2)) q :=
        (hφr.comp (contDiff_snd.neg)).contDiffAt
      exact h1.mul h2
    · push_neg at hq2
      have hev : ∀ᶠ q' in 𝓝 q, r/2 < |q'.2| :=
        continuousAt_const.eventually_lt (by fun_prop) (by linarith)
      refine contDiffAt_const (c := (0:ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hev] with q' hq'
      show φr (-q'.2) * E q'.1 (-q'.2) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hq'.le), zero_mul]
  have hparam := contDiffOn_convolution_right_with_param (μ := volume) (n := ⊤)
    (ContinuousLinearMap.mul ℝ ℂ) (f := c) (g := G) (s := ball (0:ℝ) r) (k := closedBall (0:ℝ) (r/2))
    isOpen_ball (isCompact_closedBall _ _)
    (fun p x _ hx => by
      rw [mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      show φr (-x) * E p (-x) = 0
      rw [hφr0 _ (by rw [abs_neg]; exact hx.le), zero_mul])
    hc.locallyIntegrable hG
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (ball (0:ℝ) r) := by
    have hemb : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t, (0:ℝ))) (ball (0:ℝ) r) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have h3 := ContDiffOn.comp (g := fun q : ℝ × ℝ => (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G q.1) q.2)
      hparam hemb (fun t ht => ⟨ht, mem_univ _⟩)
    exact h3
  have hrδ : r ≤ δ := min_le_right _ _

  let cl : ℝ → ℝ := fun v => max (-(r/2)) (min v (r/2))
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hcl : ∀ v, cl v ∈ Icc (-(r/2)) (r/2) := fun v =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hclid : ∀ v, |v| ≤ r/2 → cl v = v := by
    intro v hv
    obtain ⟨h1, h2⟩ := abs_le.1 hv
    show max (-(r/2)) (min v (r/2)) = v
    rw [min_eq_left h2, max_eq_right h1]
  have hE0on : ContinuousOn (fun v : ℝ => E 0 v) (Icc (-(r/2)) (r/2)) := by
    have h3 := hE.continuousOn.comp (f := fun v : ℝ => ((0:ℝ), v))
      (by fun_prop : Continuous fun v : ℝ => ((0:ℝ), v)).continuousOn
      (fun v (hv : v ∈ Icc (-(r/2)) (r/2)) => hbox 0 v (by simp [hr0]) (abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩))
    exact h3
  let Ehat : ℝ → ℂ := fun v => E 0 (cl v)
  have hEhat : Continuous Ehat := hE0on.comp_continuous hclc hcl
  let g : ℝ → ℂ := fun x => c (-x) * Ehat (-x)
  have hgc : Continuous g := (hc.comp continuous_neg).mul (hEhat.comp continuous_neg)
  have hg0 : g 0 = 1 := by
    show c (-0) * E 0 (cl (-0)) = 1
    rw [neg_zero, hclid 0 (by simp; positivity), hw0]
  have hdist := ψ.dist_normed_convolution_le (μ := volume) (x₀ := 0) (ε := 1/2) hgc.aestronglyMeasurable
    (fun x hx => by
      have hx' : |x| < r/2 := by
        have h6 := hx; rw [mem_ball, Real.dist_eq, sub_zero] at h6; exact h6
      have e1 : g x = c (-x) * E 0 (-x) := by
        show c (-x) * E 0 (cl (-x)) = _
        rw [hclid _ (by rw [abs_neg]; exact hx'.le)]
      rw [e1, hg0, ← hw0]
      exact (hwδ (by rw [Real.dist_eq, sub_zero, abs_neg]; linarith)).le)
  have hconv : (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) 0 = h 0 := by
    show _ = (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G 0) 0
    rw [convolution_def, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g, G, Ehat, φr]
    by_cases hu : |u| < r/2
    · rw [hclid u hu.le, Complex.real_smul]; ring
    · have hz : ψ.normed volume u = 0 := hφ0 u (not_lt.1 hu)
      have hz' : φ u = 0 := hφ0 u (not_lt.1 hu)
      rw [hz, hz']; simp
  have h0ne : h 0 ≠ 0 := by
    intro h0
    rw [hconv, hg0, h0] at hdist
    norm_num at hdist

  have hAh : ∀ t, |t| < r → A t = c t * h t := by
    intro t ht
    show (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] (fun y => φr (-y))) t
      = c t * (c ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G t) 0
    rw [convolution_def, convolution_def, ← integral_const_mul,
      ← integral_add_right_eq_self (μ := volume)
        (fun u => (ContinuousLinearMap.mul ℝ ℂ) (c u) (φr (-(t - u)))) t]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [ContinuousLinearMap.mul_apply', G, zero_sub, neg_neg]
    have e : -(t - (s + t)) = s := by ring
    rw [e]
    by_cases hs : |s| < r/2
    · have h7 := hfe (t, s) (hbox t s ht (by linarith))
      simp only at h7
      rw [add_comm s t, h7]; ring
    · rw [hφr0 s (not_lt.1 hs)]; ring

  have hcont_h : ContinuousOn h (ball (0:ℝ) r) := hh.continuousOn
  set V := ball (0:ℝ) r ∩ h ⁻¹' {0}ᶜ with hV
  have hVo : IsOpen V := hcont_h.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have h0V : (0:ℝ) ∈ V := ⟨mem_ball_self hr0, h0ne⟩
  have hcV : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c V := by
    have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => A t * (h t)⁻¹) V :=
      hA.contDiffOn.mul ((hh.mono inter_subset_left).inv (fun t ht => ht.2))
    refine h4.congr (fun t ht => ?_)
    have ht1 : |t| < r := by
      have h8 := ht.1; rw [mem_ball, Real.dist_eq, sub_zero] at h8; exact h8
    have hne : h t ≠ 0 := ht.2
    show c t = A t * (h t)⁻¹
    rw [hAh t ht1, mul_inv_cancel_right₀ hne]

  rw [contDiff_iff_contDiffAt]
  intro t₀
  set W := (fun t : ℝ => (t₀, t)) ⁻¹' U ∩ V with hW
  have hWo : IsOpen W := (hU.preimage (by fun_prop)).inter hVo
  have h0W : (0:ℝ) ∈ W := ⟨hUs t₀, h0V⟩
  have hFW : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) W := by
    have hE' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => E t₀ t) W :=
      hE.comp (f := fun t : ℝ => (t₀, t)) (contDiff_const.prodMk contDiff_id).contDiffOn (fun t ht => ht.1)
    have h5 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c t₀ * c t * E t₀ t) W :=
      (contDiffOn_const.mul (hcV.mono inter_subset_right)).mul hE'
    refine h5.congr (fun t ht => ?_)
    exact hfe (t₀, t) ht.1
  have hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) 0 := hFW.contDiffAt (hWo.mem_nhds h0W)
  have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => x - t₀) t₀ := (contDiff_id.sub contDiff_const).contDiffAt
  have hF0' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => c (t₀ + t)) ((fun x : ℝ => x - t₀) t₀) := by
    simpa using hF0
  have h9 := ContDiffAt.comp (f := fun x : ℝ => x - t₀) t₀ hF0' hsub
  simpa [Function.comp_def, add_sub_cancel_left] using h9

end GlobalTheory.FuncEqSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvInjOfIsModelsOfTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVectorFinal

theorem evInj_of_isModels_of_tie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → FWTie T R κ v₀ → EvInj T R v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht
  have hHW : R.models_HW := by
    cases hM
    assumption
  exact GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW ht.hv₀

end GlobalTheory.EvalAtUnitVectorFinal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem eval_injective : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → Function.Injective (fun h : H => e h v) := by
  intro D V S M H _ _ e d μ 𝓕 hip v hv x y hxy
  have h0 : e (x - y) v = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := hip (x - y) (x - y)
  rw [ipM_self_eq_zero M μ 𝓕 _ v hv h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAntilinear
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEval

theorem exists_label {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    ∃ τ, labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
  obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have key : ∀ (t : D.R.GG) (ht : t ∈ D.R.Psi),
      labE σ (D.eTau.symm ⟨t, ht⟩) = D.host.emb (g * t) := fun t ht => by
    refine RingHom.ext fun x => ?_
    have h1 : D.host.sigmaOf (g * t) = D.host.sigmaOf g * D.host.sigmaOf t :=
      map_mul (D.host.gal).symm g t
    show (σ.comp D.embE) (D.host.sigmaOf (D.eTau (D.eTau.symm ⟨t, ht⟩)).1 x) = D.host.φ₀ (D.host.sigmaOf (g * t) x)
    rw [Equiv.apply_symm_apply, ← hg, h1]
    rfl
  by_cases h : g⁻¹ * (D.eTau ρ).1 ∈ D.R.Psi
  · refine ⟨D.eTau.symm ⟨_, h⟩, Or.inl ?_⟩
    rw [key, mul_inv_cancel_left]
    rfl
  · have h' : g⁻¹ * (D.eTau ρ).1 * D.R.cc ∈ D.R.Psi := by
      by_contra h2
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).2 h2)
    refine ⟨D.eTau.symm ⟨_, h'⟩, Or.inr ?_⟩
    rw [key, mul_assoc, mul_inv_cancel_left, Formalism.L2.Geo.emb_mul_cc_comp]
    exact RingHom.ext fun x => D.host.conjE_apply (tauE D ρ) x

theorem conj_comp_eq_iff {E : Type} [Field E] (a b : E →+* ℂ) :
    (starRingEnd ℂ).comp a = b ↔ a = (starRingEnd ℂ).comp b := by
  constructor
  · rintro rfl
    ext x; simp
  · rintro rfl
    ext x; simp

theorem labE_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) :
    labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (labE σ τ) := rfl

theorem lab_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : lab ((starRingEnd ℂ).comp σ) ρ = lab σ ρ := by
  have e : (fun τ => labE ((starRingEnd ℂ).comp σ) τ = tauE D ρ ∨
        labE ((starRingEnd ℂ).comp σ) τ = (starRingEnd ℂ).comp (tauE D ρ)) =
      fun τ => labE σ τ = tauE D ρ ∨ labE σ τ = (starRingEnd ℂ).comp (tauE D ρ) := by
    funext τ
    rw [labE_conj, conj_comp_eq_iff, conj_comp_eq_iff, ← (conj_comp_eq_iff (tauE D ρ) _).1 rfl, or_comm]
  unfold lab
  rw [dite_eq_left (exists_label _ ρ), dite_eq_left (exists_label σ ρ)]
  congr 1

theorem evEx_conj {K C H H' Y : Type} [Field K] [AddCommGroup C] [Module K C] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup H'] [Module ℂ H'] (σ : K →+* ℂ) (ev : H → Y → ℂ) (ev' : H' → Y → ℂ)
    (ha : ∀ a b g, ev (a + b) g = ev a g + ev b g) (hs : ∀ (z : ℂ) a g, ev (z • a) g = z * ev a g)
    (ha' : ∀ a b g, ev' (a + b) g = ev' a g + ev' b g) (hs' : ∀ (z : ℂ) a g, ev' (z • a) g = z * ev' a g)
    (hinj : Function.Injective ev') (hx : ∀ y, ∃ x, ∀ g, ev' x g = starRingEnd ℂ (ev y g)) (φ : C → Y → ℂ)
    (h : EvEx ((starRingEnd ℂ).comp σ) ev φ) : EvEx σ ev' fun f g => starRingEnd ℂ (φ f g) := by
  obtain ⟨j, hj⟩ := h
  choose x hx using hx
  refine ⟨⟨⟨fun f => x (j f), fun f f' => hinj (funext fun g => ?_)⟩, fun a f => hinj (funext fun g => ?_)⟩,
    fun f => funext fun g => ?_⟩
  · rw [ha', hx, hx, hx, map_add (f := _), ha, map_add (f := _)]
  · refine (hx _ g).trans ?_
    rw [j.map_smulₛₗ, hs, hs', hx, map_mul, RingHom.comp_apply, Complex.conj_conj]
  · exact (hx (j f) g).trans (congrArg (starRingEnd ℂ) (congrFun (hj f) g))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem levChi_principal {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (k : GA D (Wc D i)) : levChi _ (R.βW i) (R.datWp i R.triv) k = 1 := by
  have h1 : Formalism.L2.DIV.ext1 (R.datWp i R.triv).P.H (R.datWp i R.triv).P.chi
      (Formalism.L2.DIV.rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) k)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [h1]
  simp [LevCh.datWp, datY]

end GlobalTheory.ConjEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCarries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eEp3_eq (R : RealDat3 D A3 Ks)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) :
    R.EEp3 p = R.EEc c ∧ ∀ i, R.Wp3 i p = R.Wc' i c := by
  refine ⟨le_antisymm (iSup₂_le fun c' hc' => ((hU p c c' hc hc').1).symm.le) (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.EEc c') c hc),
    fun i => le_antisymm (iSup₂_le fun c' hc' => (((hU p c c' hc hc').2 i)).symm.le)
      (le_iSup₂ (f := fun c' (_ : R.Carries p c') => R.Wc' i c') c hc)⟩

theorem exists_carries (R : RealDat3 D A3 Ks) {p : A3.fam3.base3.Ix} (h : R.EEp3 p ≠ ⊥) :
    ∃ c, R.Carries p c := by
  by_contra hn
  push_neg at hn
  apply h
  unfold RealDat3.EEp3
  exact iSup₂_eq_bot.2 fun c hc => absurd hc (hn c)

theorem wc_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (c : Pl D.host.E → List ℤ → ℂ) :
    R.Wc' i c = GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c := rfl

theorem ec_eq (R : RealDat3 D A3 Ks) (c : Pl D.host.E → List ℤ → ℂ) :
    R.EEc c = GlobalTheory.Hk3.EEc R.toRealDat R.SF c := rfl

end GlobalTheory.ThmBFromScal

namespace GlobalTheory.ThmBFromScal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem act_on_part (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    {lam : Fin D.R.m → T → GlobalTheory.LiftRows.Eig D → ℝ} {κ : ℝ}
    (hW : ∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R.toRealDat R.SF i c,
      R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x)
    (hE : ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R.toRealDat R.SF c,
      R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x)
    (hM : GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF)
    (hU : ∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c')
    {p : A3.fam3.base3.Ix} {c : Pl D.host.E → List ℤ → ℂ} (hc : R.Carries p c) (t : T) :
    (∀ i, R.lam3 i t p A3.A.v0 = lam i t c) ∧
      ∀ x ∈ R.EEp3 p, R.Th t (LinearMap.adjoint (R.Th t) x) =
        ((κ * ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p : ℝ) : ℂ) • x := by
  have hEp := (eEp3_eq R hU hc).1
  have hWp := (eEp3_eq R hU hc).2
  have hl : ∀ i, R.lam3 i t p A3.A.v0 = lam i t c := by
    intro i
    refine hC.scal.lam0 i t p (lam i t c) ?_ ?_
    · rw [hWp i, wc_eq]
      exact hM c (by rw [← ec_eq]; exact hc.1) i
    · intro x hx
      rw [hWp i, wc_eq] at hx
      exact hW i t c x hx
  refine ⟨hl, fun x hx => ?_⟩
  rw [hEp] at hx
  rw [hE t c x hx, RealDat3.prod_lamN (R := R) t p]
  simp only [hl]

theorem pThmB {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} :
    A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.LiftRows.Scal R.toRealDat R.SF →
    GlobalTheory.LiftRows.MatchUp R.toRealDat R.SF →
    (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmB := by
  intro _ hC _ hS hM hU
  classical
  unfold GlobalTheory.LiftRows.Scal at hS
  obtain ⟨lam, κ, hκ, hlpos, hW, hE⟩ := hS

  have hK : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 R.lamN κ := by
    intro t p x hx
    rw [LinearMap.comp_apply]
    by_cases h0 : R.EEp3 p = ⊥
    · rw [h0, Submodule.mem_bot] at hx
      subst hx
      simp
    · exact (act_on_part R F hC hW hE hM hU (exists_carries R h0).choose_spec t).2 x hx
  by_cases hex : ∃ (_ : T) (p : A3.fam3.base3.Ix), R.EEp3 p ≠ ⊥
  · obtain ⟨t, p, hp⟩ := hex
    have hc := (exists_carries R hp).choose_spec
    have hl := (act_on_part R F hC hW hE hM hU hc t).1
    have hk : R.kap = κ := by
      refine hC.scal.kap κ hK ⟨t, p, hp, ?_⟩
      rw [RealDat3.prod_lamN (R := R) t p, Finset.prod_congr rfl fun i _ => hl i]
      exact (Finset.prod_pos fun i _ => hlpos i t _).ne'
    intro t' p' x hx
    exact (hK t' p' x hx).trans (by rw [hk])
  · push_neg at hex
    intro t p x hx
    rw [hex t p, Submodule.mem_bot] at hx
    subst hx
    simp

end GlobalTheory.ThmBFromScal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzHeisenbergOperatorDerivative
section
open MeasureTheory

namespace GlobalTheory

open LineDeriv

theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVectorStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_of_iwahori_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → fixed π (iwahori k (Fin n)) ≠ ⊥ → ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  first | exact @GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | exact GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | (intros; apply GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori <;> assumption)
end

