module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLevi
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)
open scoped ContDiff

theorem continuousOn_levi_of_contDiffOn {n : ℕ} {f : (Fin n → ℂ) → ℝ} {W : Set (Fin n → ℂ)} (hW : IsOpen W)
    (hf : ContDiffOn ℝ 2 f W) :
    ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => levi f p.1 p.2) (W ×ˢ Set.univ) := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) W := hf.fderiv_of_isOpen hW (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) W := h1.continuousOn_fderiv_of_isOpen hW le_rfl
  have hH : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => fderiv ℝ (fderiv ℝ f) p.1) (W ×ˢ Set.univ) :=
    h2.comp continuousOn_fst fun p hp => hp.1
  have hI : ContinuousOn (fun p : (Fin n → ℂ) × (Fin n → ℂ) => Complex.I • p.2) (W ×ˢ Set.univ) :=
    continuousOn_snd.const_smul Complex.I
  unfold levi
  exact (((hH.clm_apply continuousOn_snd).clm_apply continuousOn_snd).add
    ((hH.clm_apply hI).clm_apply hI)).div_const 4

theorem APrimeChartLevi.proof (hL : APrimeChartLeviLocal.Statement) (hV : ChartVelLift.Statement) :
    APrimeChartLevi.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X k
  set e := X.S.R.chart k with he
  have hloc : ∀ y : Fin D.n → ℂ, ∃ W : Set (Fin D.n → ℂ), ∃ f : (Fin D.n → ℂ) → ℝ,
      y ∈ e.target → IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ ∞ f W ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ e.source → e (X.M.proj z) ∈ W → ∀ w v,
          IsChartVel X.M e z w v →
            levi (fun y => Real.log (D.A'.h y)) z w = levi f (e (X.M.proj z)) v := by
    intro y
    by_cases hy : y ∈ e.target
    · obtain ⟨W, hW, hyW, f, hf, hrep⟩ := hL II Ψ K ι Ω E D O Lt X k y hy
      exact ⟨W, f, fun _ => ⟨hW, hyW, hf, hrep⟩⟩
    · exact ⟨∅, 0, fun h => absurd h hy⟩
  choose W f hWf using hloc
  have hagree : ∀ y₁ ∈ e.target, ∀ y ∈ e.target, y ∈ W y₁ → ∀ v, levi (f y₁) y v = levi (f y) y v := by
    intro y₁ hy₁ y hy hyW v
    rcases eq_or_ne v 0 with rfl | hv
    · simp [levi]
    obtain ⟨z, hz, hpz, w, hw, -, -⟩ := hV II Ψ K ι Ω E D O Lt X k y hy v hv
    have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
    have hez : e (X.M.proj z) = y := by rw [hpz]; exact e.right_inv hy
    have h1 := (hWf y₁ hy₁).2.2.2 z hz hs (by rw [hez]; exact hyW) w v hw
    have h2 := (hWf y hy).2.2.2 z hz hs (by rw [hez]; exact (hWf y hy).2.1) w v hw
    rw [hez] at h1 h2
    rw [← h1, ← h2]
  refine ⟨fun y v => levi (f y) y v, ?_, ?_⟩
  · intro p hp
    obtain ⟨hW, hyW, hf, -⟩ := hWf p.1 hp.1
    have hN : W p.1 ∩ e.target ∈ 𝓝 p.1 := inter_mem (hW.mem_nhds hyW) (e.open_target.mem_nhds hp.1)
    have hc : ContinuousAt (fun q : (Fin D.n → ℂ) × (Fin D.n → ℂ) => levi (f p.1) q.1 q.2) p :=
      (continuousOn_levi_of_contDiffOn hW (hf.of_le (WithTop.coe_le_coe.2 le_top))).continuousAt
        (prod_mem_nhds (hW.mem_nhds hyW) univ_mem)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [prod_mem_nhds hN univ_mem] with q hq
    exact hagree p.1 hp.1 q.1 hq.1.2 hq.1.1 q.2
  · intro z hz hs w v hw
    have hy : e (X.M.proj z) ∈ e.target := e.map_source hs
    exact (hWf _ hy).2.2.2 z hz hs (hWf _ hy).2.1 w v hw

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PAPrimeChartLeviLocal
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi levi_comp)
open scoped ContDiff

theorem APrimeChartLeviLocal.proof (hP : ProjHoloLocal.Statement) : APrimeChartLeviLocal.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X kc y₀ hy₀
  classical
  set ψ := X.S.R.chart kc with hψ
  have hcompat : ReciprocityTheory.AnForm.M.IsCompatChart X.M.atlas ψ := X.S.R.compat kc
  have hsm : IsSmoothHerm D.A' := D.A'_pos.1
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (D.A'.h y) with hφ

  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := X.M.sections (ψ.symm y₀)
  set W : Set (Fin D.n → ℂ) := ψ.target ∩ ψ.symm ⁻¹' U with hW
  have hWo : IsOpen W := ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target hUo
  have hy₀W : y₀ ∈ W := ⟨hy₀, hxU⟩
  set g : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (ψ.symm u) with hg
  have hgan : ∀ u ∈ W, AnalyticAt ℂ g u := fun u hu =>
    NineStatements.APrimeLeviCharts.analyticAt_sec X.M hcompat hUo hsh hu.1 hu.2
  have hgC : ∀ u ∈ W, ContDiffAt ℝ ∞ (φ ∘ g) u := by
    intro u hu
    have hb := (hs _ hu.2).1.1
    have h1 : ContDiffAt ℝ ∞ D.A'.h (g u) :=
      (hsm.contDiffAt (NineStatements.APrimeLeviCharts.isOpen_blocks.mem_nhds hb)).of_le
        (WithTop.coe_le_coe.2 le_top)
    exact (h1.log (D.A'.pos _ hb).ne').comp u (hgan u hu).restrictScalars.contDiffAt
  refine ⟨W, hWo, hy₀W, φ ∘ g, fun u hu => (hgC u hu).contDiffWithinAt, ?_⟩
  intro z hz hzs hzW w v hv
  obtain ⟨γ, hγ0, hγw, hγev, hγv⟩ := hv
  obtain ⟨W', hWo', hzW', F, hFd, hF⟩ := hP II Ψ K ι Ω E D X.M ψ hcompat z hz hzs
  set y₁ := ψ (X.M.proj z) with hy₁

  have hWγ : ∀ᶠ t in 𝓝 (0 : ℂ), γ t ∈ W' :=
    hγw.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hWo'.mem_nhds hzW')
  obtain ⟨S, hS, hSp⟩ := (hγev.and hWγ).exists_mem
  have hγan : AnalyticAt ℂ γ 0 :=
    DifferentiableOn.analyticAt (fun t ht => (hSp t ht).1.1.differentiableWithinAt) hS
  set β : ℂ → Fin D.n → ℂ := fun t => F (γ t) with hβ
  have hβan : AnalyticAt ℂ β 0 :=
    DifferentiableOn.analyticAt (fun t ht =>
      ((hFd.differentiableAt (hWo'.mem_nhds (hSp t ht).2)).comp t (hSp t ht).1.1).differentiableWithinAt) hS
  have hβψ : ∀ t ∈ S, X.M.proj (γ t) ∈ ψ.source ∧ ψ (X.M.proj (γ t)) = β t := fun t ht =>
    hF (γ t) ⟨(hSp t ht).2, (hSp t ht).1.2⟩
  have hβ0 : β 0 = y₁ := by
    rw [← (hβψ 0 (mem_of_mem_nhds hS)).2, hγ0]
  have hβv : HasDerivAt β v 0 := by
    refine hγv.congr_of_eventuallyEq ?_
    filter_upwards [hS] with t ht
    exact (hβψ t ht).2.symm

  have hβN : ∀ᶠ t in 𝓝 (0 : ℂ), β t ∈ W :=
    hβan.continuousAt.preimage_mem_nhds (by rw [hβ0]; exact hWo.mem_nhds hzW)
  have hrelC : ∀ᶠ t in 𝓝 (0 : ℂ), (∀ k, ∃ i, g (β t) ⟨k, i⟩ ≠ 0) ∧
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ t = torusSmul c (g (β t)) := by
    filter_upwards [hS, hβN] with t ht htN
    have e₁ := hs _ htN.2
    have hpr : X.M.proj (γ t) = ψ.symm (β t) := by
      rw [← (hβψ t ht).2, ψ.left_inv (hβψ t ht).1]
    exact ⟨e₁.1.1, (X.M.fibre _ e₁.1 _ (hSp t ht).1.2).1 (by rw [e₁.2, hpr])⟩

  set L₁ : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0 with hL₁
  have hL0 : L₁ 0 = 0 := map_zero L₁
  have hLt : Tendsto L₁ (𝓝 0) (𝓝 0) := by
    have h := L₁.continuous.tendsto 0
    rwa [hL0] at h
  set e₁ : Fin 1 → ℂ := fun _ => 1 with he₁
  have hLe : L₁ e₁ = 1 := rfl
  have hτ₁ : AnalyticAt ℂ (γ ∘ L₁) 0 := hγan.comp_of_eq (L₁.analyticAt 0) hL0
  have hβL : AnalyticAt ℂ (β ∘ L₁) 0 := hβan.comp_of_eq (L₁.analyticAt 0) hL0
  have hβL0 : (β ∘ L₁) 0 = y₁ := by simp [hL0, hβ0]
  have hτ₂ : AnalyticAt ℂ (g ∘ (β ∘ L₁)) 0 := (hgan y₁ (hy₁ ▸ hzW)).comp_of_eq hβL hβL0

  have hγD : HasFDerivAt (γ ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).comp L₁) 0 := by
    have h := hγw.hasFDerivAt
    rw [← hL0] at h
    exact h.comp 0 L₁.hasFDerivAt
  have s1 := levi_comp (φ := φ) e₁ hτ₁
    (by simp only [Function.comp_apply, hL0, hγ0]
        exact NineStatements.APrimeLeviCharts.contDiffAt_log_h hsm hz.1)
  rw [hγD.fderiv] at s1
  simp only [Function.comp_apply, hL0, hγ0, ContinuousLinearMap.coe_comp', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, hLe, one_smul] at s1

  have hβD : HasFDerivAt (β ∘ L₁) ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) v).comp L₁) 0 := by
    have h := hβv.hasFDerivAt
    rw [← hL0] at h
    exact h.comp 0 L₁.hasFDerivAt
  have s3 := levi_comp (φ := φ ∘ g) e₁ hβL
    (by rw [hβL0]; exact (hgC y₁ (hy₁ ▸ hzW)).of_le (WithTop.coe_le_coe.2 le_top))
  rw [hβD.fderiv, hβL0] at s3
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, hLe, one_smul] at s3

  have s2 := NineStatements.APrimeLeviCharts.levi_log_h_torus hsm hτ₁ hτ₂ (hLt.eventually hrelC) e₁
  rw [← s1]
  exact s2.trans s3

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

