module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0226
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartLogPeriodFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0170
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianFamilyHodgeLattice
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0243
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPrincipal
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0017
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Imports
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ChartCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace LevelTowerAlt.Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem chart_centre (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts) (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)
    (ht₀ : t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1)) (z₀ : Sp ℂ ⟶ Or.𝔐.X) (hz₀ : CoordsAt Or.𝔐.ξ Dc.y z₀ ((Dc.chart a).γ t₀))
    (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (hsm : Or.IsSmallPart d s)
    (ν : ℝ) (hν : Or.𝔐.GeoPhi Or.sm z₀ s ν) :
    ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) ∧
      ∃ I : Submodule (𝓞 E) Λ, IsSaturated I ∧ IsIsoSub L.toLogPeriods.E I ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ‖GroundTheory.Heights₂.Heights.Regular.expCover a₀ w‖ < δ →
        Real.log ν - ε ≤ (Fintype.card (CMType H) : ℝ) * (((Dc.N - Dc.j : ℕ) : ℝ) * Real.log Real.pi) +
          (L.riem w hw).logDet (fun τ i => b τ i (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) -
            Real.log ((L.riem w hw).nz σ I) := by
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpq : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  have hfr := (((_root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀).2 d).2 s hsm).1
  have hval0 : ∀ i : CMType H × Fin (Dc.N - Dc.j), ∃ v : epsAt z₀ ⟶ Or.𝔐.t.G, Or.𝔐.M.ValAt z₀ (s i.1 i.2) v := fun i =>
    _root_.GlobalTheory.CompanionTheory.Ar.HodgeVal.frame_valAt E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 z₀ (Or.sm i.1) _ (s i.1) (Or.𝔐.all _) (hfr i.1 _) i.2
  obtain ⟨a₀, π, ρ₁, σ₀, C, jj, m, sc, hρ₁, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SncBdry.exists_bdryChart_at hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 _ Dc.Bd (Dc.chart a) t₀
    d.c d.f (CMType H × Fin (Dc.N - Dc.j)) (fun i => s i.1 i.2) z₀ Or.bd ht₀ hz₀ d.inDom hval0
  obtain ⟨ρ₂, Λ, _, L₀, e, hρ₂, hρ₂1, hper, hRiem⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.Conj.exists_logPeriods_famExp_isRiem E H D l (Xo l) σ₀ _ a₀ C hpq
  obtain ⟨Bf, hBd, hBe⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ActFam.exists_action_family E H C.R C.t C.g _ C.M ρ₂ C.ψ e hρ₂
  have hnorm : ∀ u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ, ‖(ρ₂ : ℂ) • u‖ = ρ₂ * ‖u‖ := fun u => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ₂.le]
  have hsmρ : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ρ₂ := fun u hu => by
    rw [mem_ball_zero_iff] at hu ⊢
    rw [hnorm]
    nlinarith
  have hsm1 : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (ρ₂ : ℂ) • u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := fun u hu =>
    Metric.ball_subset_ball hρ₂1 (hsmρ u hu)
  have hsmd : DifferentiableOn ℂ (fun u : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ => (ρ₂ : ℂ) • u)
      (Metric.ball 0 1) := (differentiable_id.fun_const_smul _).differentiableOn
  have hBhol : ∀ c x, DifferentiableOn ℂ (fun z => Bf ((ρ₂ : ℂ) • z) c x) (Metric.ball 0 1) := fun c x =>
    (hBd c x).comp hsmd hsmρ
  have hpb : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le,
      GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := fun w hw => ChartFree.expCover_mem_punct L₀.a_le hw
  have hclosed : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, ∀ c x, ∃ y, L₀.P w y =
      Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) c (L₀.P w x) := by
    intro w hw c x
    have hb := hsmρ _ (hpb w hw).1
    have h1 : e.ex _ (L₀.P w x) = 1 := ((hper w hw _).2 ⟨x, rfl⟩ : _)
    refine (hper w hw _).1 ?_
    show e.ex _ _ = 1
    rw [hBe _ hb, h1]
    haveI := C.t.act.hom c
    simp
  obtain ⟨instM, hact⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action E _ a₀ C.g Λ L₀ (fun z => Bf ((ρ₂ : ℂ) • z)) hBhol hclosed
  have hInt : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1,
      (Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ u ∈ Flat.punct _ a₀ 1) := by
    intro u hu
    obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 u hu)
    have h5 := Or.bd _ _ h3
    have h6 : Or.𝔐.Interior (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj) ↔ (ρ₂ : ℂ) • u ∈ Flat.punct _ a₀ 1 := by
      rw [← h4, h5, not_not]
    rw [h6]
    have hne : (ρ₂ : ℂ) ≠ 0 := by exact_mod_cast hρ₂.ne'
    constructor
    · rintro ⟨-, h⟩
      exact ⟨hu, fun i hi h0 => h i hi (by simp [h0])⟩
    · rintro ⟨-, h⟩
      exact ⟨hsm1 u hu, fun i hi => by simpa [hne] using h i hi⟩
  have hF : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, _ := fun w hw =>
    _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ChartUnif.exists_unif_of_interior hG E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 σ₀ _ a₀ C jj m (Metric.ball 0 ρ₂) e
      ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) (Bf ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w))
      (L₀.H (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) hpq (hsmρ _ (hpb w hw).1)
      ((hInt _ (hpb w hw).1).2 (hpb w hw)) (hRiem _ (hpb w hw)) (hBe _ (hsmρ _ (hpb w hw).1))
  have hinj : ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le, Function.Injective (L₀.P w) := by
    intro w hw
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    refine L₀.unimod.1 ?_
    ext y
    have h := L₀.im w hw x y
    rw [hx] at h
    simpa using h.symm
  have hw₀ : ∃ w₀, w₀ ∈ GroundTheory.Heights₂.Heights.Regular.logCover L₀.a_le := by
    refine ⟨fun k => if (k : ℕ) < a₀ then -1 else 0, fun i => ?_, fun k hk => ?_⟩
    · simp
    · simp [not_lt.2 hk]
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hadj : ∀ c c' : 𝓞 E, (c' : E) = IsCMField.complexConj E (c : E) → ∀ x y, L₀.E (c • x) y = L₀.E x (c' • y) := by
    intro c c' hc x y
    obtain ⟨A, _, φ, u, χ', -, -, -, -, -, h⟩ := hF w₀ hw₀
    have h1 := L₀.im w₀ hw₀ (c • x) y
    have h2 := L₀.im w₀ hw₀ x (c' • y)
    rw [hact w₀ hw₀] at h1
    rw [hact w₀ hw₀] at h2
    have h3 := h c c' hc (L₀.P w₀ x) (L₀.P w₀ y)
    have h4 : ((L₀.E (c • x) y : ℤ) : ℝ) = ((L₀.E x (c' • y) : ℤ) : ℝ) := by
      rw [← h1, ← h2]
      exact congrArg Complex.im h3
    exact_mod_cast h4
  let L : ActPeriods E _ a₀ C.g Λ :=
    { toLogPeriods := L₀
      adj := hadj
      B := fun z => Bf ((ρ₂ : ℂ) • z)
      B_hol := hBhol
      act := hact }
  obtain ⟨σa, hσ, hinl, hinr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R jj _ C.ψ C.hol
  have hcm : IsCMFam (fun τ => σa (Or.sm τ)) := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h]
    · exact hinr
    · exact hinl
  have hdiffb : ∀ (r : C.R), DifferentiableOn ℂ (fun u => C.ψ ((ρ₂ : ℂ) • u) r) (Metric.ball 0 1) := fun r =>
    (C.hol.2 r).comp hsmd hsm1
  have hframe : ∀ u ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∀ τ
      (h : genPt Or.𝔐.ξ ⤳ centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj)),
      (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre (spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj), h⟩ := by
    intro u hu τ h
    obtain ⟨-, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    have h4 := (_root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or _ _ h3).2 { d with inDom := h2 }
    exact (h4.2 s hsm).1 τ h
  have hEig : IsEigFrames (Metric.ball 0 1) L.B (fun τ => σa (Or.sm τ))
      (fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i)) := by
    refine ⟨fun τ k => differentiableOn_pi.2 fun i => hdiffb _, fun t ht τ => ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R C.t jj m C.g _ C.M (Metric.ball 0 ρ₂) C.ψ e ((ρ₂ : ℂ) • t)
      (Bf ((ρ₂ : ℂ) • t)) (Or.sm τ) _ (s τ) (fun k => sc (τ, k)) σa (hsmρ t ht) (hBe _ (hsmρ t ht))
      (hσ _ (hsm1 t ht)) (hframe t ht τ) (fun k => (hA _ (hsm1 t ht)).2.2.2.2 (τ, k))
  refine ⟨a₀, C.g, Λ, inferInstance, instM, L, π, ρ₁ * ρ₂, fun τ => σa (Or.sm τ),
    fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj, fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i),
    mul_pos hρ₁ hρ₂, hcm, hEig, fun u hu => ?_, fun w hw => ?_, ?_⟩
  · have heq : t₀ + (((ρ₁ * ρ₂ : ℝ)) : ℂ) • (u ∘ π) = t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • u) ∘ π) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      push_cast
      ring
    rw [heq]
    obtain ⟨h1, h2, h3, -, -⟩ := hA _ (hsm1 u hu)
    exact ⟨h1, h2, h3, fun i a' => hσ _ (hsm1 u hu) (Or.sm i) a', hInt u hu⟩
  · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, hdv, -⟩ := hF w hw
    have hbρ := hsmρ _ (hpb w hw).1
    choose v hv1 hv2 using (hA _ (hsm1 _ (hpb w hw).1)).2.2.2.2
    refine ⟨v, fun i => hv1 i, ?_⟩
    refine ⟨A, instA, φ, u, χ', hgp, hAH, fun a' p => ?_, hinj w hw, fun p => ?_, fun i => ?_⟩
    · show (u.ex (Bf _ a' p)).left ≫ φ = _
      have e1 : (u.ex p).left ≫ φ ≫ (Or.𝔐.t.act.act a').left = ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ (Or.𝔐.t.act.act a').left := by
        rw [← hex p, Category.assoc]
      rw [hex, e1, hBe _ hbρ, Over.comp_left, Category.assoc, Category.assoc, m.act]
    · rw [hlat p]
      exact hper w hw p
    · obtain ⟨v', h1, h2⟩ := hdv _ _ (Flat.FrameDeriv.isDerivAt0_pt e hbρ (sc i))
      exact ⟨v', by rw [h1, hv2 i, Category.assoc], h2⟩

  · have h0 : (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1 := Metric.mem_ball_self one_pos
    obtain ⟨-, -, co0, -, hv0⟩ := hA _ (hsm1 0 h0)
    have hT0 : t₀ + (ρ₁ : ℂ) • (((ρ₂ : ℂ) • (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ)) ∘ π) = t₀ := by
      funext i; simp
    rw [hT0] at co0
    have hz : z₀ = spMap (C.ψ ((ρ₂ : ℂ) • 0)) ≫ jj :=
      _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt _ Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie Or.𝔐.normal Or.𝔐.all _ _ _ hz₀ co0
    rw [hz] at hν
    obtain ⟨P, V, _, _, MV, ρV, I₀, hf, σ', bz, g1, g2, g3, g4, g5, g6⟩ := hν
    have hσ' : σ' = fun τ => σa (Or.sm τ) := funext fun τ => RingHom.ext fun a' =>
      WeightSheet.valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (g3 τ a') (hσ _ (hsm1 0 h0) (Or.sm τ) a')
    rw [hσ'] at g6
    refine centre_phi C m hρ₂ hρ₂1 e L (fun w hw => ⟨hper w hw, fun N ζ x x' hN hc => ?_⟩) (hBe _ (hsmρ 0 h0)) _ _
      (fun τ k => sc (τ, k)) (fun _ _ => rfl) hcm hEig P MV ρV I₀ hf g1 g2 g4 bz (fun τ k => ?_) g6
    · obtain ⟨A, instA, φ, u, χ', hgp, hAH, hex, hlat, -, -⟩ := hF w hw
      have hpp : (ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := by
        obtain ⟨-, -, h3, h4, -⟩ := hA _ (hsm1 _ (hpb w hw).1)
        exact h4.1 fun hb => (Or.bd _ _ h3).1 hb ((hInt _ (hpb w hw).1).2 (hpb w hw))
      obtain ⟨tB, mB, hP⟩ := exists_principal C m hpp
      have hw' : ∀ p, ((e.ex ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w) p).left ≫ m.φ) ≫ Or.𝔐.t.G.hom =
          spMap (C.ψ ((ρ₂ : ℂ) • GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ≫ jj := fun p => by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (e.ex _ p)]
        rfl
      have h1 := cubWeil_push m _ (x₀ := Over.homMk _ (hw' _)) (y₀ := Over.homMk _ (hw' _)) rfl rfl hc
      have h2 := weil_fibre Or.𝔐.t _ A φ _ u _ χ' hgp hAH tB mB hP N ζ (L₀.P w x) (L₀.P w x') hN
        ((hlat _).2 ((hper w hw _).2 ⟨x, rfl⟩)) ((hlat _).2 ((hper w hw _).2 ⟨x', rfl⟩)) _ _ (hex _).symm (hex _).symm h1
      rw [L₀.im w hw] at h2
      exact_mod_cast h2
    · obtain ⟨v, hv1, hv2⟩ := g5 τ k
      obtain ⟨v', hv1', hv2'⟩ := hv0 (τ, k)
      rw [hv2, LieModel.ValAt.unique Or.𝔐.tie.gen hv1 hv1', hv2']

end LevelTowerAlt.Val
end
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.HodgeCompactCoverPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_root (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (hpos : 0 < D.p + D.q)
    (p : ℕ) (hp : p ∈ S) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p) := by
  obtain ⟨s0, o, ⟨m0⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ObjAt.exists_obj_at E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
  let q : Cpt A.ξ := ⟨_, specializes_rfl⟩
  exact (_root_.GlobalTheory.CompanionTheory.Ar.OmLink.htOm_eq_htLat E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) q A.tie.gen
    (pow_pos (A.S_prime p hp).pos _) (A.tors p hp) (A.normal q.1).2
    (HcptPull.noeth_stalk A.tie.gen q ((GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1 q))).2.1 hpos

theorem exists_flagged (hW : Out.WeilSt) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (dg : ℕ)
    (hcov : A.IsCover dg) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hHT : ∀ p ∈ S, HT.HTFree A p) :
    ∃ (Ω' : Type) (_ : Field Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k))
      (y' : (Σ k, J' k) → Ω') (B : HodgeCpt Y S y') (Fl : B.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Ω') (i : Ω →+* Ω') (g : B.X ⟶ A.X) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)),
      Nonempty K' ∧ Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧
      GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ g i ∧ B.f = g ≫ A.f ∧ B.R = A.R ∧ (∀ p ∈ S, HT.HTFree B p) ∧
      Fl.RootLines xdeg e := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · have hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A.ξ (𝟙 _) (RingHom.id Ω) := by
      unfold GlobalTheory.CompanionTheory.Ar.Dominates
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, hne, hinj, hy, hT⟩ := exists_join A.tie A.tie (𝟙 _) (RingHom.id Ω) hd
    obtain ⟨Fl⟩ := flag_zero (reTie A hT) dg hcov h0
    haveI : IsEmpty (CMType H × Fin (D.p + D.q)) := ⟨fun r => by have := r.2.2; omega⟩
    exact ⟨Ω, _, K₃, _, J₃, inferInstance, y₃, reTie A hT, Fl, fun _ => 0, fun _ => 1, RingHom.id Ω, 𝟙 _, bk, bx, hne, hinj, hy, hd,
      (Category.id_comp _).symm, rfl, hHT, isEmptyElim⟩
  · have hζ := exists_root A x hx hpos
    obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
      GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K J y A x dg hx hS hHT hζ hcov
    have hBy : B.ξ ≫ B.f = (spMap i ≫ x) ≫ Y.j := by
      rw [hBf, ← Category.assoc, hg₂, Category.assoc, hx, Category.assoc]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, ⟨k₀⟩, hinj, hy, hT⟩ := exists_join A.tie B.tie g₂ i hg₂
    obtain ⟨K₄, _, J₄, _, y₄, bk', bx', C, g₃, Fl, xdeg, e, hinj', hy', hg₃, hCf, hCR, -, hC, -, -, hroot, -⟩ :=
      GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₃ J₃ y₃ (reTie B hT) (spMap i ≫ x) b Li₀ a₀ m₀ M₀ j V₀ dg hBy hS hB
        (fun p hp => by
          obtain ⟨ζ, hζ'⟩ := hζ p hp
          exact ⟨i ζ, by rw [show (reTie B hT).R = A.R from hBR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
    refine ⟨Ω', _, K₄, _, J₄, inferInstance, y₄, C, Fl, xdeg, e, i, g₃ ≫ g₂, bk' ∘ bk, fun k => (bx k).trans (bx' (bk k)),
      ⟨bk' k₀⟩, hinj'.comp hinj, fun k a => (hy' _ _).trans (hy k a), ?_, ?_, hCR.trans hBR, hC, hroot⟩
    · have h3 : C.ξ ≫ g₃ = B.ξ := by
        have h := hg₃
        unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
        rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show C.ξ ≫ g₃ ≫ g₂ = _
      rw [← Category.assoc, h3]
      exact hg₂
    · rw [Category.assoc, ← hBf]; exact hCf

end

theorem hodge_compact_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  intro hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y A dg inst hcov hS hHT
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l (Xo l) c _ _ Y S Ω K J y A hβ
  obtain ⟨Ω', _, K', _, J', _, y', B, Fl, xdeg, e, i, g, bk, bx, hne, hinj, hy, hd, hf, hR, hB, hroot⟩ :=
    exists_flagged hW A x hx dg hcov hS hHT
  obtain ⟨j, hext, hV⟩ := exists_pull A B g i x hx hS (fun p hp => (hHT p hp).2) hd hf hR
  obtain ⟨hbir, har⟩ := _root_.GlobalTheory.CompanionTheory.Ar.flagged_model_dim E H D l (Xo l) c _ _ Y S Ω' K' J' y' B Fl hβ
  have har' : IsArithVar (mCoordIdeal y') (@Fintype.card (CMType H) inst * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
    convert har
  choose L hL using _root_.GlobalTheory.CompanionTheory.Relay.exists_smooth_conj_invariant_metric K' J'
  exact ⟨{ K := K', «ι» := J', Ω := Ω', y := y', arith := har', birational := hbir, xdeg := xdeg,
           x := fun _ r => L (xdeg r), x_deg := fun _ _ => (hL _).1, x_smooth := fun _ _ => (hL _).2.1,
           x_conj := fun _ _ => (hL _).2.2, kA := 1, kA_pos := one_pos, A := L 0, A_smooth := (hL _).2.1,
           A_conj := (hL _).2.2, δ := 1, δ_pos := one_pos },
    B, Fl, e, i, g, bk, bx, j, hinj, hy, hd, hB, hroot, hext.1, hext.2, hV⟩

end LevelTowerAlt
end
end

