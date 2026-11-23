module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0020
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.MhChange
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0019
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0015
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HoloMapProj

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentHeightLowerBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt

theorem ph_usc {n : ℕ} {X : Type} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas n X}
    (B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A) (x : X) (r : ℝ) (hr : B.ph x < r) :
    ∀ᶠ x' in 𝓝 x, B.ph x' < r := by
  obtain ⟨j, hj⟩ := B.cover x
  have hs : x ∈ (B.chart j).source :=
    B.toPotentialCharts.mid_subset_source j (B.toPotentialCharts.inner_subset_mid j hj)
  have ht := (B.chart j).map_source hs
  have hn : (B.chart j).target ∈ 𝓝 (B.chart j x) := (B.chart j).open_target.mem_nhds ht
  have h1 : ∀ᶠ y in 𝓝[(B.chart j).target] (B.chart j x),
      B.q j y + B.ph ((B.chart j).symm y) < B.q j (B.chart j x) + B.ph x + (r - B.ph x) / 2 :=
    (B.u_psh j).1 _ ht _ (by
      show B.q j (B.chart j x) + B.ph ((B.chart j).symm (B.chart j x)) < _
      rw [(B.chart j).left_inv hs]; linarith)
  rw [nhdsWithin_eq_nhds.2 hn] at h1
  have h2 : ∀ᶠ y in 𝓝 (B.chart j x), B.q j (B.chart j x) - (r - B.ph x) / 2 < B.q j y :=
    ((B.q_smooth j).continuousOn.continuousAt hn).eventually (lt_mem_nhds (by linarith))
  have hc := (B.chart j).continuousAt hs
  filter_upwards [hc.eventually h1, hc.eventually h2, (B.chart j).open_source.mem_nhds hs] with y a b c
  rw [(B.chart j).left_inv c] at a
  linarith

theorem Xo_dense {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type}
    [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
    (D : ComponentData II Ψ K J Ω W) {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal D.y)) :
    (𝓝[D.Xo] w).NeBot := by
  classical
  obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover w hw
  have ht1 : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
    mem_ball_zero_iff.2 (by linarith)
  let e : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ := fun i => if t i = 0 then 1 else 0
  have h0 : Tendsto (fun s : ℝ => t + (s : ℂ) • e) (𝓝[>] 0) (𝓝 t) := by
    have : Continuous fun s : ℝ => t + (s : ℂ) • e := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hγ := ((D.chart a).analytic t ht1).continuousAt
  have hT : Continuous fun z : (Σ k, J k) → ℂ => torusSmul c z := by
    unfold torusSmul; fun_prop
  have h1 : Tendsto (fun s : ℝ => torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) (𝓝[>] 0)
      (𝓝[D.Xo] (torusSmul c ((D.chart a).γ t))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(hT.tendsto _).comp (hγ.tendsto.comp h0), ?_⟩
    filter_upwards [h0.eventually (Metric.isOpen_ball.mem_nhds ht1), self_mem_nhdsWithin] with s hs hs0
    have hm := (D.chart a).mem _ hs
    refine ⟨mcPts_smul D.arith.2.1.2.1 c hc hm, fun hb => ?_⟩
    have hb' := D.bd_torus _ hb (fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
    have he : torusSmul (fun k => (c k)⁻¹) (torusSmul c ((D.chart a).γ (t + (s : ℂ) • e))) =
        (D.chart a).γ (t + (s : ℂ) • e) := by
      funext p
      simp [torusSmul, hc]
    rw [he, (D.chart a).boundary _ hs] at hb'
    obtain ⟨i, -, hi⟩ := hb'
    have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hs0)
    by_cases h : t i = 0 <;> simp [e, h, hs'] at hi
  exact h1.neBot

end LevelTowerAlt
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.GoodOriginTowerHeight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem LevelTowerAlt.good_origin_tower_height : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → ∃ (K₃ : Type) (_ : Fintype K₃) (ι₃ : K₃ → Type) (_ : ∀ k, Fintype (ι₃ k)) (κ : K → K₃) (v : (Σ k, J k) → Σ k, ι₃ k) (P₃ : Ideal (MRing ι₃)) (e r : ℕ) (cf : Fin r → ℝ) (Mt : ℝ → HermLine ι₃) (Nt : ℝ → Fin r → Fin e → HermLine ι₃) (δ : ℝ), IsBlockMap κ v ∧ IsArithVar P₃ (Dc.n + 1 + e) ∧ imageZ v P₃ = mCoordIdeal Dc.y ∧ 0 < δ ∧ (∀ t m i, (Nt t m i).a = (Nt 1 m i).a) ∧ (∀ t m i, IsSmoothHerm (Nt t m i)) ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IsPullHerm κ v (muReg X.H X.S B t) (Mt t)) ∧ Tendsto (fun t => ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m))) (𝓝[>] 0) (𝓝 (δ * T.PPc II B a (Top.testPoly T.j))) ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * ptsIntegral (e := Dc.n + e) P₃ (fun i z => Real.log ((Fin.append (fun _ : Fin Dc.n => Mt t) (Nt 1 m) i).h z)) (fun _ => 1) = δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) :=
  LevelTowerAlt.Comparison₂.tie_of (LevelTowerAlt.Comparison₂.common LevelTowerAlt.Comparison₂.levelFree LevelTowerAlt.Comparison₂.muHodge) LevelTowerAlt.Comparison₂.replace (LevelTowerAlt.Comparison₂.baseSide LevelTowerAlt.Comparison₂.regUnif)
end

