module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasDerivAtLpOfDominated
section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil Filter Topology
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

theorem lp_two_norm_sq {E : Type*} [MeasurableSpace E] {μ : Measure E} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  simp_rw [inner_self_eq_norm_sq]

theorem hasDerivAt_Lp_of_dominated {E : Type*} [MeasurableSpace E] {μ : Measure E}
    (F : ℝ → Lp ℂ 2 μ) (G : Lp ℂ 2 μ) (f f' : ℝ → E → ℂ) (b : E → ℝ) (t₀ δ : ℝ) (hδ : 0 < δ)
    (hF : ∀ t, F t =ᵐ[μ] f t) (hG : G =ᵐ[μ] f' t₀) (hb : MemLp b 2 μ)
    (hd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, HasDerivAt (fun s => f s x) (f' t x) t)
    (hbd : ∀ x, ∀ t ∈ Metric.ball t₀ δ, ‖f' t x‖ ≤ b x) :
    HasDerivAt F G t₀ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set d : ℝ → E → ℂ := fun s x => (s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x) - f' t₀ x with hd_def
  have hD : ∀ s : ℝ, ((s⁻¹ • (F (t₀ + s) - F t₀) - G : Lp ℂ 2 μ) : E → ℂ) =ᵐ[μ] d s := by
    intro s
    filter_upwards [Lp.coeFn_sub (s⁻¹ • (F (t₀ + s) - F t₀)) G,
      Lp.coeFn_smul s⁻¹ (F (t₀ + s) - F t₀), Lp.coeFn_sub (F (t₀ + s)) (F t₀),
      hF (t₀ + s), hF t₀, hG] with x h1 h2 h3 h4 h5 h6
    simp only [hd_def, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  have hsq : ∀ s : ℝ, ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2 = ∫ x, ‖d s x‖ ^ 2 ∂μ := by
    intro s
    rw [lp_two_norm_sq]
    exact integral_congr_ae ((hD s).mono fun x hx => by simp only [hx])
  have hlim : Tendsto (fun s : ℝ => ∫ x, ‖d s x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => (2 * b x) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun s =>
        (((Lp.aestronglyMeasurable _).congr (hD s)).norm.pow 2)
    · have hs : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 ∧ |s| < δ := by
        have h1 : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := eventually_mem_nhdsWithin
        have h2 : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| < δ := by
          refine nhdsWithin_le_nhds ?_
          have : ∀ᶠ s : ℝ in 𝓝 0, s ∈ Metric.ball (0 : ℝ) δ := Metric.ball_mem_nhds _ hδ
          exact this.mono fun s hs => by simpa using hs
        exact h1.and h2
      refine hs.mono fun s hs => Eventually.of_forall fun x => ?_
      obtain ⟨hs0, hsδ⟩ := hs
      have hmem : t₀ + s ∈ Metric.ball t₀ δ := by simpa [Metric.mem_ball, dist_eq_norm] using hsδ
      have h0 : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδ
      have hmv : ‖f (t₀ + s) x - f t₀ x‖ ≤ b x * ‖(t₀ + s) - t₀‖ :=
        (convex_ball t₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := fun r => f r x) (f' := fun r => f' r x)
          (fun r hr => (hd x r hr).hasDerivWithinAt) (fun r hr => hbd x r hr) h0 hmem
      have hb0 : 0 ≤ b x := (norm_nonneg _).trans (hbd x t₀ h0)
      have hq : ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ ≤ b x := by
        rw [norm_smul, norm_inv]
        have hn : 0 < ‖s‖ := norm_pos_iff.2 hs0
        rw [add_sub_cancel_left] at hmv
        rw [inv_mul_le_iff₀ hn]
        linarith [mul_comm (b x) ‖s‖]
      have hdn : ‖d s x‖ ≤ 2 * b x := by
        calc ‖d s x‖ ≤ ‖(s⁻¹ : ℝ) • (f (t₀ + s) x - f t₀ x)‖ + ‖f' t₀ x‖ := norm_sub_le _ _
          _ ≤ 2 * b x := by linarith [hbd x t₀ h0]
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdn 2
    · simpa [mul_pow] using hb.integrable_sq.const_mul (2 ^ 2)
    · refine Eventually.of_forall fun x => ?_
      have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hd x t₀ (Metric.mem_ball_self hδ))
      have h2 : Tendsto (fun s : ℝ => d s x) (𝓝[≠] 0) (𝓝 (f' t₀ x - f' t₀ x)) :=
        h1.sub tendsto_const_nhds
      have h3 := (h2.norm).pow 2
      simpa using h3
  have hlim0 : Tendsto (fun s : ℝ => ‖s⁻¹ • (F (t₀ + s) - F t₀) - G‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [hsq]
    simpa using hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h4 := (Real.continuous_sqrt.tendsto 0).comp hlim0
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h4

variable {l : Type} [Fintype l]

end GlobalTheory.CompanionTheory.Hypotheses₂.GaussCurve

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.KaehlerBasisOnLocalizationAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_basis_on_localization_away : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ} (x : Fin n → Γ(Y, U.1)), (letI := secAlgebra g U.1; ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) → IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  first | exact @GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | exact GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away | (intros; apply GlobalTheory.CompanionTheory.Glob.ResKCoords.isCoords_basicOpen_of_away <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentialsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_ring_free_differentials : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | exact GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime <;> assumption)
end

