module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0218
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

theorem PositivityTheory.Xgp.t_c_bm_exists_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) (tie : FlagTie M 𝔐), ∀ (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F → ∀ (τ : CMType H) (w : (Σ k, baseIdx ι M.blk k) → ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z w → 𝔐.Interior z → M.GoodAt F (mCoordIdeal w) → 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) (HodgeMetric.gramFn 𝔐 (gb tie F τ) w) ∧ (HodgeMetric.gramFn 𝔐 (gb tie F τ) w).PosDef ∧ ∀ a b, tie.omFrame F τ a (dualFam tie F τ b) = if a = b then 1 else 0 := by
  intro E _ _ _ H D Xo l c Y S K _ ι _ Φ _ y M 𝔐 tie F hF τ w z hw hi hg
  have hq : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre z, 𝔐.all _⟩) := by
    rw [ptIdeal_centre hw (𝔐.all _)]; exact hg
  have hfr := PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ _ hq
  have hpol := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi
  obtain ⟨Γ, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx.exists_gramAt_posDef E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) (D.p + D.q)
    (gbS tie F τ) z (𝔐.all _) hpol hfr
  have tp := _root_.GlobalTheory.CompanionTheory.Ar.tie_points 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have hgb : (fun k => ((gbS tie F τ k : ↥(𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ))) : 𝔐.Li)) = gb tie F τ := rfl
  rw [hgb] at h1
  have hfn : HodgeMetric.gramFn 𝔐 (gb tie F τ) w = Γ := by
    have hex : ∃ (Γ : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
        CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z (gb tie F τ) Γ := ⟨Γ, z, hw, hi, h1⟩
    unfold HodgeMetric.gramFn
    rw [dite_eq_left hex]
    obtain ⟨z₀, hw₀, -, hΓ₀⟩ := hex.choose_spec
    have hz : z₀ = z := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw₀⟩ ⟨𝔐.all _, hw⟩
    rw [hz] at hΓ₀
    exact _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.gramAt_unique_of_polarisedAt E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _ hpol hΓ₀ h1
  rw [hfn]
  refine ⟨h1, h2, ?_⟩
  obtain ⟨hex, -⟩ := omBundle_dualFrame 𝔐 τ _ (tie.frameO _ F hF hq τ)
  have hex' : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 := hex
  unfold dualFam
  rw [dite_eq_left hex']
  exact hex'.choose_spec
