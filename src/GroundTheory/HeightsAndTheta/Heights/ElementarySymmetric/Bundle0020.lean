module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcEqCoh
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CohMkEqZero
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDSq
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PEulerVarX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem EulerVar.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerVar.proof
    GroundTheory.Heights₂.Heights.Kleiman.KHCechDSq.full
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES.full

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNbarLeviChartReg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm (levi levi_comp levi_add_smul levi_re_analytic levi_congr)

namespace NbarLeviChartReg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem analyticAt_disc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F}
    (hf : AnalyticAt ℂ f 0) : AnalyticAt ℂ (fun u : Fin 1 → ℂ => f (u 0)) 0 :=
  hf.comp_of_eq ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticAt 0) rfl

theorem fderiv_disc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {f : ℂ → F} {d : F}
    (hf : HasDerivAt f d 0) : fderiv ℂ (fun u : Fin 1 → ℂ => f (u 0)) 0 (fun _ => 1) = d := by
  have hL : HasFDerivAt (fun u : Fin 1 → ℂ => u 0)
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).hasFDerivAt
  have h : HasFDerivAt (fun u : Fin 1 → ℂ => f (u 0))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0)) 0 :=
    hf.hasFDerivAt.comp (0 : Fin 1 → ℂ) hL
  rw [h.fderiv]
  simp

theorem levi_const_mul {J : Type} [Fintype J] {f : (J → ℂ) → ℝ} {z : J → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f z) (w : J → ℂ) : levi (fun y => c * f y) z w = c * levi f z w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hf w
  simp only [zero_add] at h
  rw [h, Inter.RegularizedCurvature.levi_const, zero_add]

theorem vertFactor_local (D : ComponentData II Ψ K ι Ω E) {p : ℕ} (hp : p ∈ D.S) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    ∃ T : ((Σ k, ι k) → ℂ) → ℂ, AnalyticAt ℂ T z ∧ T z ≠ 0 ∧
      ∀ᶠ y in 𝓝 z, y ∈ mcPts (mCoordIdeal D.y) → D.vertFactor p y = ‖T y‖ := by
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp hz
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp z hz
  rw [VertFactorSmooth.vertFactor_eq D hp hz hG hH hdeg hrel hHz] at hpos
  have hHa := Inter.RegularizedCurvature.analyticAt_eval_map H z
  refine ⟨fun y => eval y (map (Int.castRingHom ℂ) G) / eval y (map (Int.castRingHom ℂ) H),
    (Inter.RegularizedCurvature.analyticAt_eval_map G z).div hHa hHz, norm_pos_iff.mp hpos, ?_⟩
  filter_upwards [hHa.continuousAt.eventually_ne hHz] with y hy hyP
  exact VertFactorSmooth.vertFactor_eq D hp hyP hG hH hdeg hrel hy


open MuRegSmooth TopNPoly NbarSmooth in
theorem regNbarQ_smooth_eq [DecidableEq Ψ] (hE : HermExtend.Statement) (hP : ProjSmoothAlong.Statement)
    (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D) (S : LogLogRegularisationSetting M D.Xo (muLine H))
    (B p q : ℕ) (t : ℝ) (hsm : M.atlas.Smooth (S.regWeight t)) :
    IsSmoothHerm (regNbarQ H M S B p q t) ∧ ∀ z ∈ mcPts (mCoordIdeal D.y),
      (regNbarQ H M S B p q t).h z = (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p := by
  have hVS := VertFactorSmooth.proof VertFactorPos.proof
  set P := mCoordIdeal D.y with hPdef
  set a : K → ℤ := (q : ℤ) • muTwDeg H B + (p : ℤ) • D.a' with ha
  set F : ((Σ k, ι k) → ℂ) → ℝ := fun z => (S.ref.h z * Real.exp (S.regWeight t (M.proj z))) ^ q *
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
  have hon : ∀ z ∈ mcPts P, (hermOfFun ι a F).h z = F z := fun z hz =>
    hermOfFun_h_of_mem hMH hhom hz (hpos z hz)
  refine ⟨?_, fun z hz => (smoothRep_h _ hz).trans (hon z hz)⟩
  show IsSmoothHerm (smoothRep P (hermOfFun ι a F))
  exact smoothRep_smooth_of (Z := Z) hZa hZs fun z hz => (hZh z hz).trans (hon z hz).symm

end NbarLeviChartReg


end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRefChartDisc
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open ReciprocityTheory.AnForm.M (IsCompatChart FinHolAtlas)

theorem RefChartDisc.log_norm_eq_re {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (h0 : F 0 ≠ 0) :
    ∃ L : ℂ → ℂ, AnalyticAt ℂ L 0 ∧ ∀ᶠ s in 𝓝 (0 : ℂ), Real.log ‖F s‖ = (L s).re := by
  refine ⟨fun s => Complex.log (F s / F 0) + (Real.log ‖F 0‖ : ℂ), ?_, ?_⟩
  · refine ((hF.div analyticAt_const h0).clog ?_).add analyticAt_const
    show F 0 / F 0 ∈ Complex.slitPlane
    rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · filter_upwards [hF.continuousAt.eventually_ne h0] with s hs
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr hs) (norm_ne_zero_iff.mpr h0)]
    ring

theorem RefChartDisc.analyticAt_comp {n : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas n X}
    {e : OpenPartialHomeomorph X (Fin n → ℂ)} (he : IsCompatChart A e) {y : ℂ → X}
    (hy : AnalyticAt ℂ (fun s => e (y s)) 0) (hys : ∀ᶠ s in 𝓝 (0 : ℂ), y s ∈ e.source)
    {V : Set X} {F : X → ℂ} (hF : A.HoloOn V F) (h0 : y 0 ∈ V) :
    AnalyticAt ℂ (fun s => F (y s)) 0 := by
  have h0s : y 0 ∈ e.source := hys.self_of_nhds
  have h1 : AnalyticAt ℂ (F ∘ e.symm) (e (y 0)) :=
    ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat_fun he hF (e.map_source h0s) (by rwa [e.left_inv h0s])
  refine (h1.comp (f := fun s => e (y s)) hy).congr ?_
  filter_upwards [hys] with s hs
  simp [Function.comp, e.left_inv hs]

theorem RefChartDisc.proof (hProj : ProjChartHolo.Statement) : RefChartDisc.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D H M S j γ hγ hmem hsrc
  set x := M.proj (γ 0) with hx
  set e := S.R.chart j with he_def
  have he : IsCompatChart M.atlas e := S.R.compat j
  have hφ : AnalyticAt ℂ (fun s => e (M.proj (γ s))) 0 := hProj II Ψ K ι Ω E D M e he γ hγ hmem hsrc
  have hγ0 : γ 0 ∈ mcPts (mCoordIdeal D.y) := hmem.self_of_nhds
  have hcont : Tendsto (fun s => M.proj (γ s)) (𝓝 0) (𝓝 x) :=
    (M.cont _ hγ0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hγ.continuousAt.tendsto, hmem⟩)
  obtain ⟨U, hUo, hxU, hUsub, σ, hσ, hσh, G1, hG1, hG1eq⟩ := S.th_ref x x (S.R.th.mem_U x)
  obtain ⟨W, hWo, hxW, G2, hG2, hG2eq⟩ := S.R.q_th j x x ⟨S.R.th.mem_U x, hsrc⟩
  have hV : ∀ᶠ s in 𝓝 (0 : ℂ), M.proj (γ s) ∈ U ∩ W ∩ e.source :=
    hcont.eventually (((hUo.inter hWo).inter e.open_source).mem_nhds ⟨⟨hxU, hxW⟩, hsrc⟩)
  have hA : ∀ {V : Set M.Xc} {F : M.Xc → ℂ}, M.atlas.HoloOn V F → x ∈ V →
      AnalyticAt ℂ (fun s => F (M.proj (γ s))) 0 :=
    fun hF hxV => RefChartDisc.analyticAt_comp he hφ (hV.mono fun _ h => h.2) hF hxV

  choose i hi using (hσ x hxU).1.1
  set T : K → ℂ → ℂ := fun b s => γ s ⟨b, i b⟩ / σ (M.proj (γ s)) ⟨b, i b⟩ with hT_def
  have hden : ∀ b, AnalyticAt ℂ (fun s => σ (M.proj (γ s)) ⟨b, i b⟩) 0 := fun b => hA (hσh ⟨b, i b⟩) hxU
  have hT : ∀ b, AnalyticAt ℂ (T b) 0 := fun b =>
    (analyticAt_pi_iff.1 hγ ⟨b, i b⟩).div (hden b) (hi b)
  obtain ⟨c0, hc0, hγc0⟩ := (M.fibre _ (hσ x hxU).1 _ hγ0).1 (hσ x hxU).2
  have hT0 : ∀ b, T b 0 ≠ 0 := fun b => by
    have : γ 0 ⟨b, i b⟩ = c0 b * σ x ⟨b, i b⟩ := by rw [hγc0]; rfl
    simp only [hT_def, ← hx, this]
    exact div_ne_zero (mul_ne_zero (hc0 b) (hi b)) (hi b)
  choose L hL hLeq using fun b => RefChartDisc.log_norm_eq_re (hT b) (hT0 b)
  have hdenev : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ b, σ (M.proj (γ s)) ⟨b, i b⟩ ≠ 0 :=
    eventually_all.2 fun b => (hden b).continuousAt.eventually_ne (hi b)
  refine ⟨fun s => G1 (M.proj (γ s)) + G2 (M.proj (γ s)) - ∑ b, ((S.ref.a b : ℝ) : ℂ) * L b s, ?_, ?_⟩
  · refine ((hA hG1 hxU).add (hA hG2 hxW)).sub ?_
    have := Finset.analyticAt_sum (𝕜 := ℂ) Finset.univ fun b _ => (analyticAt_const (v := ((S.ref.a b : ℝ) : ℂ))).mul (hL b)
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp [Finset.sum_apply]
  filter_upwards [hV, hmem, hdenev, eventually_all.2 hLeq] with s hs hγs hds hLs
  obtain ⟨⟨hsU, hsW⟩, hssrc⟩ := hs
  set y := M.proj (γ s) with hy
  obtain ⟨hσy, hpσy⟩ := hσ y hsU
  obtain ⟨c, hc, hγc⟩ := (M.fibre _ hσy _ hγs).1 (by rw [hpσy])
  have hcT : ∀ b, c b = T b s := fun b => by
    have : γ s ⟨b, i b⟩ = c b * σ y ⟨b, i b⟩ := by rw [hγc]; rfl
    simp only [hT_def, ← hy, this]
    field_simp [hds b]
  have hmet : S.ref.h (γ s) = (∏ b, ‖c b‖ ^ S.ref.a b) * S.ref.h (σ y) := by
    rw [← S.ref.smul c (σ y) hc, hγc]; rfl
  have hpos : 0 < S.ref.h (σ y) := S.ref.pos _ hσy.1
  have hlog : Real.log (S.ref.h (γ s)) = ∑ b, (S.ref.a b : ℝ) * (L b s).re + Real.log (S.ref.h (σ y)) := by
    rw [hmet, Real.log_mul (Finset.prod_ne_zero_iff.2 fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))
      hpos.ne', Real.log_prod (fun b _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc b)))]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Real.log_zpow, hcT b, hLs b]
  have h1 := hG1eq y hsU
  have h2 := hG2eq y ⟨⟨hsW, hUsub hsU⟩, hssrc⟩
  simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul]
  rw [hlog]
  linarith

end GroundTheory.Heights₂.Heights.NineStatements
end
end

