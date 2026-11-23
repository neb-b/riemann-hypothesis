module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0092
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0091
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchInOneBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem isPreconnected_punctured_ball {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by
  have hH : IsPreconnected {z : ℂ | z.re < Real.log R} := (convex_halfSpace_re_lt _).isPreconnected
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)
    · rintro ⟨hw, hw0⟩
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hw0) hw
  rw [← himage]
  exact hH.image _ Complex.continuous_exp.continuousOn

theorem PuncturedBranchInOneBranch.proof (h₁ : BranchImageNhdOffCentre.Statement) :
    PuncturedBranchInOneBranch.Statement := by
  intro n I q m c ν ρ _ hdim hρ hcov hdisj
  obtain ⟨N, hN, hNc⟩ := h₁ n I q hdim
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]
  have hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius := fun τ hτ ↦ by
    rwa [Metric.mem_ball, dist_zero_right, hnorm]
  have h0r : ‖(0 : ℂ)‖ < ν.radius := by simpa using ν.radius_pos

  have hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ := fun τ hτ ↦
    (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp
      (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N :=
    (hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  obtain ⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius :=
    ⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  let D : Set ℂ := Metric.ball 0 R \ {0}
  have hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R := fun τ hτ ↦
    ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩
  have hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q := by
    intro τ hτ h
    have h' := ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)
    exact (norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)

  let Vb : Fin m → Set ℂ := fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVo : ∀ b, IsOpen (Vb b) := by
    intro b
    rw [isOpen_iff_mem_nhds]
    rintro τ ⟨hτD, hτb⟩
    have hτN : ν.toFun (fun _ ↦ τ) ∈ N := hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)
    obtain ⟨U, hU, hUc⟩ := hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)
    filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU]
      with σ hσD hσU
    exact ⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩
  have hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b') := fun b b' hbb ↦
    Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)
  have hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b := fun τ hτ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))
    exact ⟨b, hτ, hb⟩

  have hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp [hR0.ne']
  obtain ⟨b, hb⟩ := hcovD _ hτ₀
  have hsub : D ⊆ Vb b := by
    refine (isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b)
      (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩
    · exact Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')
    · intro τ hτ
      obtain ⟨b', hb'⟩ := hcovD τ hτ
      by_cases h : b' = b
      · exact Or.inl (h ▸ hb')
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)
  refine ⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩
  · rwa [Metric.mem_ball, dist_zero_right]
  · simpa using norm_pos_iff.1 hτ0

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace PuncturedBranchSameOrder

theorem const_mem_ball_iff (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const]

theorem disc_props {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by
  have hι : Differentiable ℂ (fun τ : ℂ ↦ fun _ : Fin 1 ↦ τ) := differentiable_pi.2 fun _ ↦ differentiable_id
  refine ⟨b.differentiableOn.comp hι.differentiableOn fun τ hτ ↦ (const_mem_ball_iff τ _).2 hτ,
    fun s hs t ht h ↦ congrFun (b.injOn ((const_mem_ball_iff s _).2 hs) ((const_mem_ball_iff t _).2 ht) h) 0,
    fun τ hτ ↦ b.mapsTo ((const_mem_ball_iff τ _).2 hτ), b.map_zero, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    refine ⟨t 0, (const_mem_ball_iff _ _).1 ?_, by rw [ht']⟩
    rw [ht']
    exact ht
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (const_mem_ball_iff σ _).2 hσ, rfl⟩

theorem factor_of_punctured {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {C D : ℂ → E} {ψ : ℂ → ℂ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hCd : DifferentiableOn ℂ C (Metric.ball 0 r)) (hCi : Set.InjOn C (Metric.ball 0 r))
    (hDd : DifferentiableOn ℂ D (Metric.ball 0 ρ)) (hDi : Set.InjOn D (Metric.ball 0 ρ)) (h0 : C 0 = D 0)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ \ {0}))
    (hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ψ τ ∈ Metric.ball (0 : ℂ) r ∧ C (ψ τ) = D τ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, D τ = C (g τ)) ∧ 𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = Function.update ψ 0 (limUnder (𝓝[≠] (0 : ℂ)) ψ) := ⟨_, rfl⟩
  have hB : Metric.ball (0 : ℂ) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 ρ) := by
    rw [hg_def]
    refine Complex.differentiableOn_update_limUnder_of_bddAbove hB hψd ⟨r, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hgψ : ∀ τ, τ ≠ 0 → g τ = ψ τ := fun τ hτ ↦ by rw [hg_def]; exact Function.update_of_ne hτ _ _
  have hgc : ContinuousAt g 0 := (hgd.differentiableAt hB).continuousAt
  have hpunct : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
    Filter.mem_of_superset (inter_mem_nhdsWithin _ hB) fun τ h ↦ ⟨h.2, h.1⟩
  have hpt : ∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) ∈ Metric.ball (0 : ℂ) ρ \ {0} := fun s hs hsρ ↦
    ⟨by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsρ, by simpa using hs.ne'⟩
  have hle : ‖g 0‖ ≤ r := by
    refine le_of_tendsto (hgc.norm.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [hgψ τ hτ.2]
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hlt : ‖g 0‖ < r := by
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hmax : IsMaxOn (norm ∘ g) (Metric.ball 0 ρ) 0 := isMaxOn_iff.2 fun τ hτ ↦ by
      show ‖g τ‖ ≤ ‖g 0‖
      by_cases h : τ = 0
      · rw [h]
      · rw [hgψ τ h, heq]
        exact (mem_ball_zero_iff.1 (hψ τ ⟨hτ, h⟩).1).le
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) ρ).isPreconnected
      Metric.isOpen_ball hgd (Metric.mem_ball_self hρ) hmax
    have h1 := hpt (ρ / 2) (by positivity) (by linarith)
    have h2 := hpt (ρ / 4) (by positivity) (by linarith)
    have e1 : D ((ρ / 2 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h1).2, ← hgψ _ h1.2]
      exact congrArg C (hconst h1.1)
    have e2 : D ((ρ / 4 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h2).2, ← hgψ _ h2.2]
      exact congrArg C (hconst h2.1)
    have := Complex.ofReal_injective (hDi h1.1 h2.1 (e1.trans e2.symm))
    linarith
  have hgr : g 0 ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.2 hlt
  have hCg0 : C (g 0) = D 0 := by
    have hC : ContinuousAt C (g 0) := (hCd.differentiableAt (Metric.isOpen_ball.mem_nhds hgr)).continuousAt
    have hD : ContinuousAt D 0 := (hDd.differentiableAt hB).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq ((hC.comp hgc).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hD.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [Function.comp_apply, hgψ τ hτ.2]
    exact (hψ τ hτ).2
  have hg0 : g 0 = 0 := hCi hgr (Metric.mem_ball_self hr) (hCg0.trans h0.symm)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), D τ = C (g τ) := by
    filter_upwards [hB] with τ hτ
    by_cases h : τ = 0
    · rw [h, hCg0]
    · rw [hgψ τ h]
      exact (hψ τ ⟨hτ, h⟩).2.symm
  have hga : AnalyticAt ℂ g 0 := hgd.analyticAt hB
  refine ⟨g, hga, hg0, hev, ?_⟩
  rcases hga.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 (hc.and hev)
    have hm : 0 < min ε ρ := lt_min hε hρ
    have hs : 0 < min ε ρ / 2 := half_pos hm
    have hsε : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hsρ : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have h1 := hpt _ hs hsρ
    obtain ⟨hgc1, hD1⟩ := hεb (by rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsε)
    exact h1.2 (hDi h1.1 (Metric.mem_ball_self hρ) (by rw [hD1, hgc1, hg0, h0]))
  · rwa [hg0] at hc

theorem punctured_factor (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨hCd, hCi, hCm, hC0, hCim⟩ := disc_props c
  obtain ⟨hDd, hDi, hDm, hD0, -⟩ := disc_props d
  obtain ⟨ε, hε, hcutε⟩ := hcut n I q hI hdim
  have hDc : ContinuousAt (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) 0 :=
    (hDd.differentiableAt (Metric.ball_mem_nhds 0 d.radius_pos)).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁ε⟩ := Metric.continuousAt_iff.1 hDc ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = min (min ρ ρ₁) d.radius := ⟨_, rfl⟩
  have hρ'pos : 0 < ρ' := hρ' ▸ lt_min (lt_min hρ hρ₁) d.radius_pos
  have hρ'ρ : ρ' ≤ ρ := hρ' ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ'1 : ρ' ≤ ρ₁ := hρ' ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 d.radius := Metric.ball_subset_ball (hρ' ▸ min_le_right _ _)
  let ψ : ℂ → ℂ := fun τ ↦
    Function.invFunOn (fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (Metric.ball 0 c.radius) (d.toFun fun _ ↦ τ)
  have hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ' \ {0},
      ψ τ ∈ Metric.ball (0 : ℂ) c.radius ∧ (c.toFun fun _ ↦ ψ τ) = d.toFun fun _ ↦ τ := by
    intro τ hτ
    have hex := (hCim _).1 (hcd τ (norm_pos_iff.2 hτ.2) (lt_of_lt_of_le (mem_ball_zero_iff.1 hτ.1) hρ'ρ))
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hopen : IsOpen (Metric.ball (0 : ℂ) ρ' \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ' \ {0}) := by
    intro τ₀ hτ₀
    obtain ⟨hσ₀r, hσ₀⟩ := hψ τ₀ hτ₀
    have hδ : 0 < c.radius - ‖ψ τ₀‖ := sub_pos.2 (mem_ball_zero_iff.1 hσ₀r)
    have hballsub : Metric.ball (ψ τ₀) (c.radius - ‖ψ τ₀‖) ⊆ Metric.ball 0 c.radius :=
      Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have hne : (d.toFun fun _ ↦ τ₀) ≠ q := fun h ↦
      hτ₀.2 (hDi (hsub hτ₀.1) (Metric.mem_ball_self d.radius_pos) (h.trans hD0.symm))
    have hε₀ : (d.toFun fun _ ↦ τ₀) ∈ Metric.ball q ε := by
      have := hρ₁ε (x := τ₀) (by rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hτ₀.1) hρ'1)
      rw [Metric.mem_ball]
      rwa [hD0] at this
    obtain ⟨U, hUo, hUx, Ψ, hΨd, hΨ⟩ := hcutε (fun σ ↦ c.toFun fun _ ↦ σ) (ψ τ₀) (c.radius - ‖ψ τ₀‖) hδ
      (hCd.mono hballsub) (hCi.mono hballsub) (fun σ hσ ↦ hCm (hballsub hσ))
      (by show (c.toFun fun _ ↦ ψ τ₀) ∈ Metric.ball q ε; rw [hσ₀]; exact hε₀)
      (by show (c.toFun fun _ ↦ ψ τ₀) ≠ q; rw [hσ₀]; exact hne)
    have hUD : (d.toFun fun _ ↦ τ₀) ∈ U := by
      have hUx' : (c.toFun fun _ ↦ ψ τ₀) ∈ U := hUx
      rwa [hσ₀] at hUx'
    have hDdiff : DifferentiableAt ℂ (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) τ₀ :=
      hDd.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hτ₀.1))
    have hevU : ∀ᶠ τ in 𝓝 τ₀, (d.toFun fun _ ↦ τ) ∈ U :=
      hDdiff.continuousAt.preimage_mem_nhds (hUo.mem_nhds hUD)
    have heq : ψ =ᶠ[𝓝 τ₀] fun τ ↦ Ψ (d.toFun fun _ ↦ τ) := by
      filter_upwards [hevU, hopen.mem_nhds hτ₀] with τ hτU hτ
      obtain ⟨σ, hσ, hσz, hΨσ⟩ := hΨ (d.toFun fun _ ↦ τ) ⟨hDm (hsub hτ.1), hτU⟩
      rw [hΨσ]
      exact hCi (hψ τ hτ).1 (hballsub hσ) ((hψ τ hτ).2.trans hσz.symm)
    have hdiff : DifferentiableAt ℂ (fun τ ↦ Ψ (d.toFun fun _ ↦ τ)) τ₀ :=
      (hΨd.differentiableAt (hUo.mem_nhds hUD)).comp τ₀ hDdiff
    exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  exact factor_of_punctured (C := fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (D := fun τ : ℂ ↦ d.toFun fun _ ↦ τ)
    c.radius_pos hρ'pos hCd hCi (hDd.mono hsub) (hDi.mono hsub) (hC0.trans hD0.symm) hψd hψ

end PuncturedBranchSameOrder

theorem PuncturedBranchSameOrder.proof (hcut : PuncturedCurveDiscInverse.Statement) :
    PuncturedBranchSameOrder.Statement := by
  intro n I q c d ρ hI hdim hρ hcd f
  obtain ⟨g, hga, hg0, hev, hmap⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim c d ρ hρ hcd
  have hBd : Metric.ball (0 : ℂ) d.radius ∈ 𝓝 0 := Metric.ball_mem_nhds 0 d.radius_pos
  have hdc : ∃ ρ'' > 0, ∀ σ : ℂ, 0 < ‖σ‖ → ‖σ‖ < ρ'' → c.toFun (fun _ ↦ σ) ∈ d.image := by
    have hA : {τ : ℂ | τ ∈ Metric.ball 0 d.radius ∧ (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ} ∈ 𝓝 0 :=
      Filter.Eventually.and hBd hev
    obtain ⟨ρ'', hρ'', hball⟩ := Metric.mem_nhds_iff.1 (hmap (Filter.image_mem_map hA))
    refine ⟨ρ'', hρ'', fun σ _ hσ ↦ ?_⟩
    obtain ⟨τ, ⟨hτd, hτeq⟩, rfl⟩ := hball (mem_ball_zero_iff.2 hσ)
    exact ((PuncturedBranchSameOrder.disc_props d).2.2.2.2 _).2 ⟨τ, hτd, hτeq⟩
  obtain ⟨ρ'', hρ'', hdc'⟩ := hdc
  obtain ⟨k, hka, hk0, hev', -⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim d c ρ'' hρ'' hdc'
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    have := hka.continuousAt.tendsto
    rwa [hk0] at this
  have hid : (fun τ ↦ k (g τ)) =ᶠ[𝓝 0] id := by
    filter_upwards [hgt.eventually hev', (hkt.comp hgt).eventually hBd, hev, hBd] with τ h1 h2 h3 h4
    exact (PuncturedBranchSameOrder.disc_props d).2.1 h2 h4 (h1.symm.trans h3.symm)
  have hgd : deriv g 0 ≠ 0 := by
    intro hz
    have hk' : HasDerivAt k (deriv k 0) (g 0) := by
      rw [hg0]
      exact hka.differentiableAt.hasDerivAt
    have e1 : HasDerivAt (fun τ ↦ k (g τ)) (deriv k 0 * deriv g 0) 0 :=
      hk'.comp 0 hga.differentiableAt.hasDerivAt
    have e2 : HasDerivAt (fun τ ↦ k (g τ)) 1 0 := (hasDerivAt_id 0).congr_of_eventuallyEq hid
    have := e1.unique e2
    rw [hz, mul_zero] at this
    exact zero_ne_one this
  have hcong : (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) =ᶠ[𝓝 0]
      (fun σ : ℂ ↦ eval (c.toFun fun _ ↦ σ) f) ∘ g := by
    filter_upwards [hev] with τ hτ
    rw [Function.comp_apply, hτ]
  show analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0 =
    analyticOrderAt (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) 0
  rw [analyticOrderAt_congr hcong, analyticOrderAt_comp_of_deriv_ne_zero hga hgd, hg0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFixedBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegFixedBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_weight_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {w w' : (Fin n → ℂ) → ℝ} (hw : ∀ x, w x ≤ w' x)
    (y : Fin (d + 1) → ℂ) :
    chartDens J A w (vecCons (logReg u ε) fun _ => euclPot) y ≤
      chartDens J A w' (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with h
  · have h0 := hN n d J A u ε x h.choose hε h.choose_spec
    rw [hx.2] at h0
    exact mul_le_mul_of_nonneg_right (hw x) h0
  · exact le_rfl

end RegFixedBallMass


open RegFixedBallMass in
theorem RegFixedBallMass.proof (hN : RegDensNonneg.Statement) (hS : StokesOnChart.Statement)
    (hL : LogIntegrable.Statement) (hC : ChartMassCompact.Statement) : RegFixedBallMass.Statement := by
  intro n d J A u R hJ hdim hA hu
  obtain ⟨θ, hθs, hθ01, hθU, V, -, hBV, hθV⟩ :=
    exists_cutoff_near (S := Metric.closedBall (0 : Fin n → ℂ) R) Metric.isClosed_closedBall
      Metric.isOpen_ball (Metric.closedBall_subset_ball (lt_add_one R))
  have hθR : tsupport θ ⊆ Metric.closedBall 0 (R + 1) := hθU.trans Metric.ball_subset_closedBall
  have hθc : HasCompactSupport θ :=
    (isCompact_closedBall (0 : Fin n → ℂ) (R + 1)).of_isClosed_subset (isClosed_tsupport θ) hθR
  have hθw : ∀ x, (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x ≤ θ x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Fin n → ℂ) R
    · rw [Set.indicator_of_mem hx, hθV x (hBV hx)]
    · rw [Set.indicator_of_notMem hx]
      exact (hθ01 x).1
  have hηs : ∀ i : Fin d, SmoothNear (zeroSet J) ((fun _ => euclPot) i) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
  have hθη : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons θ (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hθs
    · simpa using hηs i
  have hu2 : linForm ((2 : ℂ) • u) ∉ J := by
    have he : linForm ((2 : ℂ) • u) = C 2 * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, C_mul]
    intro hm
    apply hu
    have := J.mul_mem_left (C (1 / 2 : ℂ)) (he ▸ hm)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1, one_mul] at this
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hA hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J A y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx h0
    exact hy (hPy y x hx h0)
  have hTi := (hL n (d + 1) J A u _ (R + 1) hJ hdim hA hu hθη).add
    (hL n (d + 1) J A ((2 : ℂ) • u) _ (R + 1) hJ hdim hA hu2 hθη)
  refine ⟨∫ y, (chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator fun x => Real.log ‖linEval u x‖)
      (vecCons θ fun _ => euclPot) + chartAbsDens J A ((Metric.closedBall 0 (R + 1)).indicator
        fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖) (vecCons θ fun _ => euclPot)) y, fun ε hε => ?_⟩
  have hgs : ∀ i : Fin (d + 1), SmoothNear (zeroSet J) (vecCons (logReg u ε) (fun _ => euclPot) i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε.1)
    · simpa using hηs i
  have hGi : Integrable (chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot)) :=
    (hC n (d + 1) J A θ _ hJ hdim hA hθs.continuous.continuousOn hgs (Or.inl hθc)).mono'
      (SheetSumMeasurable.proof n (d + 1) J A θ _ hJ hdim hA hθs.continuous.measurable
        hgs).1.aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le J A θ _ y)
  have hFi : Integrable (chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => euclPot)) :=
    hGi.mono' (RegBallMass.measurable_chartDens_indicator hJ hdim hA u hε.1
        Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        have h0 := (RegBallMass.chartDens_indicator_mono hN hA u hε.1
          (subset_refl (Metric.closedBall (0 : Fin n → ℂ) R)) y).1
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact chartDens_weight_mono hN hA u hε.1 hθw y)
  refine ⟨hFi, ?_⟩
  calc ∫ y, chartDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
        (vecCons (logReg u ε) fun _ => euclPot) y
      ≤ ∫ y, chartDens J A θ (vecCons (logReg u ε) fun _ => euclPot) y :=
        integral_mono hFi hGi fun y => chartDens_weight_mono hN hA u hε.1 hθw y
    _ = ∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y :=
        hS n d J A θ (logReg u ε) (fun _ => euclPot) hJ hdim hA (smoothNear_of_contDiff hθs)
          (smoothNear_of_contDiff (contDiff_logReg u hε.1)) hηs (Or.inl hθc)
    _ ≤ ‖∫ y, chartDens J A (logReg u ε) (vecCons θ fun _ => euclPot) y‖ := Real.le_norm_self _
    _ ≤ _ := norm_integral_le_of_norm_le hTi (by
        filter_upwards [hgood] with y hy
        exact LelongRegularise.norm_chartDens_le hA _ hθR hε.1 hε.2 hy)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem isRadicalAt_of_associatedPrimes {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (hA : ∀ P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I),
      P ≤ RingHom.ker (eval q) → P ∈ I.minimalPrimes ∧ P ≠ RingHom.ker (eval q))
    (hB : ∀ P : Ideal (MvPolynomial (Fin n) ℂ), P.IsPrime → I ≤ P → P ≠ RingHom.ker (eval q) →
      ∀ g ∈ I.radical, ∃ s ∉ P, s * g ∈ I) :
    IsRadicalAt I q := by
  intro g hg
  by_contra hno
  simp only [not_exists, not_and] at hno
  have : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  set N : Submodule (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Submodule.span _ {Ideal.Quotient.mk I g}
  have hK : ∀ s, s ∈ Module.annihilator (MvPolynomial (Fin n) ℂ) N ↔ s * g ∈ I := by
    intro s
    change s ∈ N.annihilator ↔ _
    rw [Submodule.mem_annihilator_span_singleton]
    change Ideal.Quotient.mk I s * Ideal.Quotient.mk I g = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hKq : Module.annihilator (MvPolynomial (Fin n) ℂ) N ≤ RingHom.ker (eval q) := by
    intro s hs
    by_contra h
    exact hno s h ((hK s).1 hs)
  obtain ⟨P, hPmin, hPq⟩ := Ideal.exists_minimalPrimes_le hKq
  have hPass : P ∈ associatedPrimes (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    associatedPrimes.subset_of_injective (f := N.subtype) Subtype.val_injective
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes _ _ hPmin)
  obtain ⟨hPI, hPne⟩ := hA P hPass hPq
  obtain ⟨s, hsP, hsg⟩ := hB P hPI.1.1 hPI.1.2 hPne g hg
  exact hsP (hPmin.1.2 ((hK s).2 hsg))

theorem SliceReducedGeneral.proof (hU : SliceUnmixedGeneral.Statement)
    (hB : SliceReducedAway.Statement) : SliceReducedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hU n d J W u hJ hdim hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf q hq hfq
  obtain ⟨O₂, hO₂o, hO₂d, hO₂⟩ := hB n d J q hJ.isRadical
  exact ⟨O₁ ∩ O₂, hO₁o.inter hO₂o, hO₁d.inter_of_isOpen_left hO₂d hO₁o,
    fun L hL => isRadicalAt_of_associatedPrimes (hO₁ L hL.1) (hO₂ L hL.2)⟩

end GroundTheory.Heights₂.Heights
end

