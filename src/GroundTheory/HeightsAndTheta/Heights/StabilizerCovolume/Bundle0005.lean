module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PAPrimeLeviCharts
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic continuousOn_levi)

namespace APrimeLeviCharts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_log_h {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun y => Real.log (A.h y)) z := by
  have h1 : ContDiffAt ℝ 2 A.h z :=
    (hA.contDiffAt (isOpen_blocks.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  exact h1.log (A.pos z hz).ne'

theorem levi_log_h_torus {J : Type} [Fintype J] {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    {τ₁ τ₂ : (J → ℂ) → (Σ k, ι k) → ℂ} {u₀ : J → ℂ} (h₁ : AnalyticAt ℂ τ₁ u₀) (h₂ : AnalyticAt ℂ τ₂ u₀)
    (hrel : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ τ₁ u = torusSmul c (τ₂ u))
    (e : J → ℂ) :
    levi ((fun y => Real.log (A.h y)) ∘ τ₁) u₀ e = levi ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ e := by
  classical
  have hb := hrel.self_of_nhds.1
  choose i hi using hb

  set c : K → (J → ℂ) → ℂ := fun k u => τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ with hcdef
  have hcan : ∀ k, AnalyticAt ℂ (c k) u₀ := fun k =>
    ((analyticAt_pi_iff.1 h₁) ⟨k, i k⟩).div ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩) (hi k)
  have hne : ∀ᶠ u in 𝓝 u₀, ∀ k, τ₂ u ⟨k, i k⟩ ≠ 0 := by
    rw [eventually_all]
    intro k
    exact ((analyticAt_pi_iff.1 h₂) ⟨k, i k⟩).continuousAt.eventually_ne (hi k)
  have hrel' : ∀ᶠ u in 𝓝 u₀, (∀ k, ∃ i, τ₂ u ⟨k, i⟩ ≠ 0) ∧ (∀ k, c k u ≠ 0) ∧
      τ₁ u = torusSmul (fun k => c k u) (τ₂ u) := by
    filter_upwards [hrel, hne] with u hu hn
    obtain ⟨hbl, c', hc'0, hc'⟩ := hu
    have hcc : ∀ k, c k u = c' k := by
      intro k
      show τ₁ u ⟨k, i k⟩ / τ₂ u ⟨k, i k⟩ = c' k
      rw [hc']
      exact mul_div_cancel_right₀ _ (hn k)
    refine ⟨hbl, fun k => by rw [hcc]; exact hc'0 k, ?_⟩
    rw [hc']
    congr 1
    funext k
    exact (hcc k).symm
  have hc0 : ∀ k, c k u₀ ≠ 0 := hrel'.self_of_nhds.2.1

  set H : (J → ℂ) → ℂ := fun u =>
    ∑ k, ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀)) with hHdef
  have hH : AnalyticAt ℂ H u₀ := by
    have hk : ∀ k ∈ Finset.univ, AnalyticAt ℂ
        (fun u => ((A.a k : ℝ) : ℂ) * (Complex.log (c k u / c k u₀) + Complex.log (c k u₀))) u₀ := by
      intro k _
      refine analyticAt_const.mul (AnalyticAt.add ?_ analyticAt_const)
      refine ((hcan k).div analyticAt_const (hc0 k)).clog ?_
      show c k u₀ / c k u₀ ∈ Complex.slitPlane
      rw [div_self (hc0 k)]
      exact Complex.one_mem_slitPlane
    have hs := Finset.analyticAt_sum _ hk
    convert hs using 1
    funext u
    simp only [hHdef, Finset.sum_apply]
  have hHre : ∀ u, (∀ k, c k u ≠ 0) → (H u).re = ∑ k, (A.a k : ℝ) * Real.log ‖c k u‖ := by
    intro u hu
    simp only [hHdef, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re, norm_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.log_div (norm_ne_zero_iff.2 (hu k)) (norm_ne_zero_iff.2 (hc0 k))]
    ring
  have heq : ((fun y => Real.log (A.h y)) ∘ τ₁) =ᶠ[𝓝 u₀]
      fun u => ((fun y => Real.log (A.h y)) ∘ τ₂) u + 1 * (H u).re := by
    filter_upwards [hrel'] with u hu
    obtain ⟨hbl, hcu, hτ⟩ := hu
    have hs := A.smul (fun k => c k u) (τ₂ u) hcu
    have hprod : ∀ k ∈ Finset.univ, ‖c k u‖ ^ A.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.2 (hcu k))
    simp only [Function.comp_apply, one_mul]
    rw [hHre u hcu, hτ]
    show Real.log (A.h (fun p => c p.1 u * τ₂ u p)) = _
    rw [hs, Real.log_mul (Finset.prod_ne_zero_iff.2 hprod) (A.pos _ hbl).ne', Real.log_prod hprod]
    simp only [Real.log_zpow]
    ring
  have hf : ContDiffAt ℝ 2 ((fun y => Real.log (A.h y)) ∘ τ₂) u₀ :=
    (contDiffAt_log_h hA hrel'.self_of_nhds.1).comp u₀ h₂.restrictScalars.contDiffAt
  have hg : ContDiffAt ℝ 2 (fun u => (H u).re) u₀ :=
    Complex.reCLM.contDiff.contDiffAt.comp u₀ hH.restrictScalars.contDiffAt
  rw [levi_congr heq, levi_add_smul 1 hf hg, levi_re_analytic hH]
  ring

section Charts

variable {P : Ideal (MRing ι)} {d : ℕ}

theorem analyticAt_sec (M : CxModel P d) {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)}
    (he : ReciprocityTheory.AnForm.M.IsCompatChart M.atlas e) {U : Set M.Xc} (hU : IsOpen U)
    {s : M.Xc → (Σ k, ι k) → ℂ} (hs : ∀ p, M.atlas.HoloOn U fun y => s y p)
    {u : Fin d → ℂ} (hu : u ∈ e.target) (huU : e.symm u ∈ U) :
    AnalyticAt ℂ (fun u => s (e.symm u)) u := by
  obtain ⟨j, hj⟩ := M.atlas.cover (e.symm u)
  set V : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' (U ∩ (M.atlas.chart j).source) with hV
  have hVo : IsOpen V := e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (hU.inter (M.atlas.chart j).open_source)
  have huV : u ∈ V := ⟨hu, huU, hj⟩
  refine analyticAt_pi_iff.2 fun p => ?_
  have h1 : AnalyticAt ℂ (M.atlas.chart j ∘ e.symm) u := (he j).2 u ⟨hu, hj⟩
  have h2 : AnalyticAt ℂ ((fun y' => s y' p) ∘ (M.atlas.chart j).symm) ((M.atlas.chart j ∘ e.symm) u) := by
    refine hs p j _ ⟨(M.atlas.chart j).map_source hj, ?_⟩
    show (M.atlas.chart j).symm ((M.atlas.chart j) (e.symm u)) ∈ U
    rw [(M.atlas.chart j).left_inv hj]
    exact huU
  refine (h2.comp h1).congr ?_
  filter_upwards [hVo.mem_nhds huV] with u' hu'
  simp only [Function.comp_apply]
  rw [(M.atlas.chart j).left_inv hu'.2.2]

end Charts

end APrimeLeviCharts

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PMUcSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace MUcSmooth

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smoothRepConj_smooth_of {P : Ideal (MRing ι)} {A Z : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRepConj P A) := by
  classical
  unfold smoothRepConj
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact TopNPoly.smoothRep_smooth_of ha hZ hh

end MUcSmooth


open MuRegSmooth TopNPoly NbarSmooth MUcSmooth in
theorem MUcSmooth.proof (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement) : MUcSmooth.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D H M w S B p q t hsm
  have hVS : VertFactorSmooth.Statement := VertFactorSmooth.proof VertFactorPos.proof
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.bregWeight t (M.proj z))) ^ q *
    (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p with hFdef
  have hSB : ∀ p' ∈ D.SB B, p' ∈ D.S := fun p' hp' => (Finset.mem_filter.1 hp').1
  have hMH : IsMultiHomogIdeal P := D.arith.2.1.2.1
  have hpos : ∀ z ∈ mcPts P, 0 < F z := by
    intro z hz
    have h2 : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' z := Finset.prod_pos fun p' hp' =>
      VertFactorPos.proof II Ψ K ι Ω E D p' (hSB p' hp') z hz
    exact mul_pos (mul_pos (pow_pos (mul_pos (S.ref.pos z hz.1) (Real.exp_pos _)) q) (pow_pos h2 q))
      (pow_pos (D.A'.pos z hz.1) p)
  have hhom : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
      F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z := by
    intro z hz c hc
    have hcz : torusSmul c z ∈ mcPts P := mcPts_smul hMH c hc hz
    have hproj : M.proj (torusSmul c z) = M.proj z := ((M.fibre z hz _ hcz).2 ⟨c, hc, rfl⟩).symm
    have href : S.ref.h (torusSmul c z) = (∏ k, ‖c k‖ ^ H.aMu k) * S.ref.h z := by
      have := S.ref.smul c z hc
      rw [S.ref_deg] at this
      exact this
    have hA : D.A'.h (torusSmul c z) = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h z := by
      have := D.A'.smul c z hc
      rw [D.A'_deg] at this
      exact this
    have hV : ∀ p' ∈ D.SB B, D.vertFactor p' (torusSmul c z) =
        (∏ k, ‖c k‖ ^ D.vdeg p' k) * D.vertFactor p' z :=
      fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).1 z hz c hc
    have hk : ∀ k, ‖c k‖ ^ a k = (‖c k‖ ^ (muTwDeg H B) k) ^ q * (‖c k‖ ^ D.a' k) ^ p := by
      intro k
      have hx : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      have hak : a k = (q : ℤ) * (muTwDeg H B) k + (p : ℤ) * D.a' k := by
        simp only [ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hak, zpow_add₀ hx, zpow_mul', zpow_natCast, zpow_mul', zpow_natCast]
    have hprod : (∏ k, ‖c k‖ ^ a k) = ((∏ k, ‖c k‖ ^ H.aMu k) *
        ∏ p' ∈ D.SB B, ∏ k, ‖c k‖ ^ D.vdeg p' k) ^ q * (∏ k, ‖c k‖ ^ D.a' k) ^ p := by
      rw [Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
        muTwDeg, prod_norm_zpow_add_sum hc]
    simp only [hFdef]
    rw [hproj, href, hA, Finset.prod_congr rfl hV, Finset.prod_mul_distrib, hprod]
    ring
  have hsmooth : SmoothAlong (mcPts P) F :=
    smoothAlong_mul (smoothAlong_mul
      (smoothAlong_pow (smoothAlong_mul (smoothAlong_of_contDiffOn S.ref_smooth)
        (smoothAlong_exp (hP II Ψ K ι Ω E D M _ hsm))) q)
      (smoothAlong_pow (smoothAlong_prod _ fun p' hp' => (hVS II Ψ K ι Ω E D p' (hSB p' hp')).2) q))
      (smoothAlong_pow (smoothAlong_of_contDiffOn D.A'_pos.1) p)
  obtain ⟨Z, hZa, hZs, hZh⟩ := hE K ι P a F hMH hpos hhom hsmooth
  show IsSmoothHerm (smoothRepConj P (hermOfFun ι a F))
  exact smoothRepConj_smooth_of (Z := Z) hZa hZs fun z hz =>
    (hZh z hz).trans (hermOfFun_h_of_mem hMH hhom hz (hpos z hz)).symm

end GroundTheory.Heights₂.Heights.NineStatements
end
end

