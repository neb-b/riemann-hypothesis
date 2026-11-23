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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0110
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeConstantRank
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0241
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree

theorem expCover_mem_punct {n a : ℕ} (h : a ≤ n) {w : Fin n → ℂ} (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover h) :
    GroundTheory.Heights₂.Heights.Regular.expCover a w ∈ Flat.punct n a 1 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
    intro k
    by_cases hk : k.val < a
    · have hre := hw.1 ⟨k.val, hk⟩
      have hcast : Fin.castLE h ⟨k.val, hk⟩ = k := Fin.ext rfl
      rw [hcast] at hre
      simp only [GroundTheory.Heights₂.Heights.Regular.expCover, if_pos hk]
      rw [Complex.norm_exp, ← Real.exp_zero]
      exact Real.exp_lt_exp.2 hre
    · simp only [GroundTheory.Heights₂.Heights.Regular.expCover, if_neg hk]
      exact hw.2 k (not_lt.mp hk)
  · simp only [GroundTheory.Heights₂.Heights.Regular.expCover, if_pos hi]
    exact Complex.exp_ne_zero _

theorem exists_actPeriods_chart : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (a : Fin Dc.nCharts), ∀ t₀ ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), ∃ (a₀ g : ℕ) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (L : ActPeriods E (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ g Λ) (π : Equiv.Perm (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)))) (ρ : ℝ) (σ : CMType H → (𝓞 E →+* ℂ)) (pt : (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → (Sp ℂ ⟶ Or.𝔐.X)) (d : MuFrameAt Hd ((Dc.chart a).γ t₀)) (s : CMType H → Fin (Dc.N - Dc.j) → Or.𝔐.Li) (b : CMType H → Fin (Dc.N - Dc.j) → (Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) → Fin g → ℂ), 0 < ρ ∧ IsCMFam σ ∧ Or.IsSmallPart d s ∧ IsEigFrames (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) L.B σ b ∧ (∀ u ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1), t₀ + (ρ : ℂ) • (u ∘ π) ∈ (Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) ∧ InFrameDomain Dc.y d.c d.f ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ CoordsAt Or.𝔐.ξ Dc.y (pt u) ((Dc.chart a).γ (t₀ + (ρ : ℂ) • (u ∘ π))) ∧ Or.𝔐.LabVal (pt u) Or.sm σ ∧ (Or.𝔐.Interior (pt u) ↔ u ∈ Flat.punct _ a₀ 1)) ∧ (∀ w (hw : w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le), ∃ v : CMType H × Fin (Dc.N - Dc.j) → (epsAt (pt (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) ⟶ Or.𝔐.t.G), (∀ i, Or.𝔐.M.ValAt _ (s i.1 i.2) (v i)) ∧ FibreLatVec Or.𝔐.t _ (L.riem w hw) (fun i => b i.1 i.2 (GroundTheory.Heights₂.Heights.Regular.expCover a₀ w)) v) := by
  intro hG E _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or a t₀ ht₀
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hpq : 1 ≤ D.p + D.q := by
    have h1 := Or.N_eq
    have h2 := Dc.two_le_N
    omega
  obtain ⟨z₀, -, hz₀⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie ((Dc.chart a).γ t₀)).1 ((Dc.chart a).mem t₀ ht₀)
  obtain ⟨⟨d⟩, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.PhMuFree.phMu_small hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or z₀ _ hz₀
  obtain ⟨⟨s, hsm⟩, hsall⟩ := hd d
  have hfr := (hsall s hsm).1
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
      GroundTheory.Heights₂.Heights.Regular.expCover a₀ w ∈ Flat.punct _ a₀ 1 := fun w hw => expCover_mem_punct L₀.a_le hw
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
  refine ⟨a₀, C.g, Λ, inferInstance, instM, L, π, ρ₁ * ρ₂, fun τ => σa (Or.sm τ),
    fun u => spMap (C.ψ ((ρ₂ : ℂ) • u)) ≫ jj, d, s, fun τ k u i => C.ψ ((ρ₂ : ℂ) • u) (sc (τ, k) i),
    mul_pos hρ₁ hρ₂, hcm, hsm, ⟨fun τ k => differentiableOn_pi.2 fun i => hdiffb _, fun t ht τ => ?_⟩, fun u hu => ?_, fun w hw => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.ChartEig.values_eig E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 C.R C.t jj m C.g _ C.M (Metric.ball 0 ρ₂) C.ψ e ((ρ₂ : ℂ) • t)
      (Bf ((ρ₂ : ℂ) • t)) (Or.sm τ) _ (s τ) (fun k => sc (τ, k)) σa (hsmρ t ht) (hBe _ (hsmρ t ht))
      (hσ _ (hsm1 t ht)) (hframe t ht τ) (fun k => (hA _ (hsm1 t ht)).2.2.2.2 (τ, k))
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

end GlobalTheory.CompanionTheory.Ar.Cusp.ChartFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeDedekindTwist
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcVb

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

theorem isVBOn_of_isVB {L : Lat ξ Li} {r : ℕ} {V : Submodule Ω Li} (h : L.IsVB r V) (T : Set (Cpt ξ)) :
    L.IsVBOn T r V := fun p _ => by
  obtain ⟨U, hU, b, hb, hf⟩ := h p trivial
  exact ⟨U, hU, b, hb, fun q _ hq => hf q trivial hq⟩

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem unitAt_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q ((discr F : ℤ) : Ω) := by
  have hu := unitAt_natAbs_discr h
  rcases Int.natAbs_eq (discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simp only [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    exact ⟨neg_ne_zero.2 hu.1, neg_mem hu.2.1, by rw [inv_neg]; exact neg_mem hu.2.2⟩

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

variable {G : Over X} [GrpObj G]

theorem lat_stable (M : LieModel G ξ Li) (a : G ⟶ G) [IsMonHom a] (A : Li →ₗ[Ω] Li) (h : M.IsDiffOf a A)
    (p : Cpt ξ) (e : Li) (he : e ∈ M.lat p) : A e ∈ M.lat p := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    refine Submodule.subset_span ⟨v ≫ a, ?_, ?_⟩
    · have h1 := hv.1
      unfold IsTanAt at h1 ⊢
      rw [Over.comp_left, ← Category.assoc, h1, ← Over.comp_left]
      simp [Hom.one_def]
    · rw [h x, Over.comp_left, hv.2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | smul c x _ hx =>
    have : A (c • x) = c • A x := by
      show A ((c : Ω) • x) = (c : Ω) • A x
      rw [map_smul]
    rw [this]
    exact (M.lat p).smul_mem c hx

end GlobalTheory.CompanionTheory.Ar.HcVb

namespace GlobalTheory.CompanionTheory.Ar.HcVb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

theorem exists_genWeil (hW : Out.WeilSt) {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c)
    (t : SAB H X) (m : SABMap t Y.t f) (hj : ξ ≫ f = y₀ ≫ Y.j) (n : ℕ) (hn : 1 ≤ n)
    (ht : FullTorsion t.G ξ n) (hζ : ∃ ζ : Ω, IsPrimitiveRoot ζ n) : ∃ e, GenWeil t.G t.PP.L ξ n e := by
  obtain ⟨PP', cub, sym, adj, prim, n₁, -⟩ := sabPull Out.proved_CubePullSt ξ t
  obtain ⟨n₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m n₁
  rw [hj] at n₂
  obtain ⟨n₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m n₂
  have := _root_.GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj hW E H D l _ _ _ X _ (GlobalTheory.ModelCompare.objOfSABMap Y.oF n₃) t ξ n₁ Ω (𝟙 _) n hn
    (by rwa [Category.id_comp]) hζ
  rwa [Category.id_comp] at this

end GlobalTheory.CompanionTheory.Ar.HcVb

namespace GlobalTheory.CompanionTheory.Ar

theorem hodgeLattices_isVB : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (f : X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c) (t : SAB H X) (m : SABMap t Y.t f) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (ρ : 𝓞 E →+* Module.End Ω Li) (cst : c.F →+* Ω) (S : Finset ℕ) (R : ℕ → ℕ) [IsLocallyNoetherian X], ξ ≫ f = y₀ ≫ Y.j → ξ ≫ f ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → M.IsActOf t.act.act ρ → IsCptGen ξ → Flat.NormalCpt ξ → (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ R p)) → (∀ p ∈ S, ∀ s, ((M.htOm t.PP.L (p ^ R p)).map (eigSp ρ (cst.comp (labelEmb c s))).dualRestrict).IsVB (labelRk D s) ⊤) → ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s))) fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s) (eigSp ρ (cst.comp (labelEmb c s))) := by
  intro hW E _ _ _ H D l Xo c Y X Ω _ _ ξ f y₀ t m Li _ _ M ρ cst S R _ hj hs hact hgen hN hSp hdisc htors hζ hVB s
  classical
  have hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨hLat, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_isVB_of_smooth X Ω ξ t.G Li M hgen hsm
  obtain ⟨hfd, hrk⟩ := _root_.GlobalTheory.CompanionTheory.Ar.EigRank.eig_finrank_label E H D l Xo c Y X Ω ξ f y₀ t m Li M ρ cst hj hs hact
  obtain ⟨hinj, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  haveI := hfd
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω) := fun s' => cst.comp (labelEmb c s')
  have hσinj : Function.Injective σ := fun a b hab => hinj (RingHom.ext fun x => cst.injective (RingHom.congr_fun hab x))
  have hreg : ∀ (τ : 𝓞 E →+* Ω) (q : Cpt ξ) (a : 𝓞 E), τ a ∈ regAt ξ q :=
    fun τ q a => HcVb.integers_regular hN τ q a
  letI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _

  have hA : (M.eigLat ρ (σ s)).IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} (labelRk D s) (eigSp ρ (σ s)) := by
    have h := (_root_.GlobalTheory.CompanionTheory.Ar.EigSplit.isVBOn_eigSp X Ω ξ Li E ρ M.lat {q | ∀ l ∈ S, ¬ InFibre ξ l q} (Module.finrank Ω Li)
      (CMType H ⊕ CMType H) σ hgen hσinj (by rw [← Nat.card_eq_fintype_card]; exact hcard)
      (HcVb.isVBOn_of_isVB hLat _)
      (fun p _ a e he => by
        haveI := t.act.hom a
        exact HcVb.lat_stable M (t.act.act a) (ρ a) (hact a) p e he)
      (fun p _ s' a => hreg _ p a)
      (fun p hp => HcVb.unitAt_discr fun r hr hd => not_not.1 (hp r (hdisc r hr hd)))).1 s
    rw [hrk s] at h
    exact h

  have hDual : ∀ p ∈ S, ∀ (T : Set (Cpt ξ)) (s' : CMType H ⊕ CMType H),
      (M.htDual t.PP.L (p ^ R p) ρ (σ s')).IsVBOn T (labelRk D s') (eigSp ρ (σ s')) := by
    intro p hp T s'
    have e : M.htDual t.PP.L (p ^ R p) ρ (σ s') = (M.htOm t.PP.L (p ^ R p)).predualIn (eigSp ρ (σ s')) := by
      funext q
      ext v
      exact M.mem_htDual_iff t.PP.L (p ^ R p) ρ (σ s') q v
    rw [e]
    exact _root_.GlobalTheory.CompanionTheory.Ar.Lat.predualIn_isVBOn X Ω ξ Li _ T _ _ (HcVb.isVBOn_of_isVB (hVB p hp s') T)
  have hB : ∀ p ∈ S, ∀ (T : Set (Cpt ξ)),
      (htLabel M t.PP.L (p ^ R p) ρ σ s).IsVBOn T (labelRk D s) (eigSp ρ (σ s)) := by
    intro p hp T
    cases s with
    | inr τ => exact hDual p hp T (.inr τ)
    | inl τ =>
      have hσ1 : Function.Injective (σ (.inl τ)) := by
        intro a b hab
        have h1 := cst.injective hab
        have h2 : τ.1 (a : E) = τ.1 (b : E) := congrArg Subtype.val h1
        exact RingOfIntegers.ext (τ.1.injective h2)
      exact _root_.GlobalTheory.CompanionTheory.Relay.ideal_saturated_vector_bundle X Ω ξ Li (𝓞 E) (σ (.inl τ)) (differentIdeal ℤ (𝓞 E)) _ T _ _
        hσ1 differentIdeal_ne_bot (fun q _ a => hreg _ q a) (hDual p hp T (.inl τ))

  have hC : ∀ p ∈ S, ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) →
      htLabel M t.PP.L (p ^ R p) ρ σ s q = M.eigLat ρ (σ s) q := by
    intro p hp q hq
    have hpp := hSp p hp
    have hn : 1 ≤ p ^ R p := Nat.one_le_pow _ _ hpp.pos
    obtain ⟨e, he⟩ := HcVb.exists_genWeil hW Y ξ f y₀ t m hj (p ^ R p) hn (htors p hp) (hζ p hp)
    have hco := _root_.GlobalTheory.CompanionTheory.Ar.HTCoh.htOm_coherent X Ω ξ hgen hN t.G t.semi t.PP.L (p ^ R p) hn (htors p hp) e he Li M
    obtain ⟨h1, h2, -⟩ := hco.2 q
    have hu : unitAt ξ q ((p ^ R p : ℕ) : Ω) := by
      rw [Nat.cast_pow]
      exact Flat.ZUnit.pow (not_not.1 (hq p hpp)) _
    have heq : M.htOm t.PP.L (p ^ R p) q = M.omLat q := le_antisymm h2 fun u hu' => by
      have h3 := (M.htOm t.PP.L (p ^ R p) q).smul_mem (⟨((p ^ R p : ℕ) : Ω)⁻¹, hu.2.2⟩ : regAt ξ q) (h1 u hu')
      have e2 : (⟨((p ^ R p : ℕ) : Ω)⁻¹, hu.2.2⟩ : regAt ξ q) • ((p ^ R p) • u) = u := by
        show ((p ^ R p : ℕ) : Ω)⁻¹ • ((p ^ R p) • u) = u
        rw [← Nat.cast_smul_eq_nsmul Ω, inv_smul_smul₀ hu.1]
      rwa [e2] at h3
    obtain ⟨g1, g2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieModel.htDual_htW_eq_eigLat_of_htOm_eq_omLat X Ω ξ t.G Li M t.PP.L (p ^ R p) (Module.finrank Ω Li) (𝓞 E) ρ (σ s) q
      (HcVb.isVBOn_of_isVB hLat _) heq
    rcases s with τ | τ
    · refine g2 _ (fun a => hreg _ q a) ⟨_, HcVb.natAbs_discr_mem_different E, ?_⟩
      rw [map_natCast]
      exact HcVb.unitAt_natAbs_discr fun r hr _ => not_not.1 (hq r hr)
    · exact g1
  obtain ⟨L, hL, hL0, hLp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lat_glue X Ω ξ Li S (M.eigLat ρ (σ s))
    (fun p => htLabel M t.PP.L (p ^ R p) ρ σ s) (labelRk D s) (eigSp ρ (σ s)) hgen hSp hA
    (fun p hp => hB p hp _) hC
  have e : Lat.patch S (M.eigLat ρ (σ s)) (fun p => htLabel M t.PP.L (p ^ R p) ρ σ s) = L := by
    funext q
    by_cases h : ∃ p ∈ S, InFibre ξ p q
    · obtain ⟨p, hp, hq⟩ := h
      rw [Lat.patch_of_unique S _ _ hp hq fun p' hp' h' => inFibre_unique (hSp _ hp) (hSp _ hp') hq h',
        hLp p hp q hq]
    · have h' : ∀ p ∈ S, ¬ InFibre ξ p q := fun p hp hf => h ⟨p, hp, hf⟩
      rw [Lat.patch_of_not S _ _ h', hL0 q h']
  show (Lat.patch S (M.eigLat ρ (σ s)) fun p => htLabel M t.PP.L (p ^ R p) ρ σ s).IsVB (labelRk D s) (eigSp ρ (σ s))
  rw [e]
  exact hL

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularRelayStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_relay : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay | exact GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiProjectiveProperCover
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_proper_qproj_cover : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → ∃ (n : ℕ) (Y : Fin n → Scheme.{0}) (π : ∀ i, Y i ⟶ X), (∀ i, IsProper (π i) ∧ IsQProjOver (π i ≫ p)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (π i) := by
  intro k _ _ X p hs hl hq
  have hLN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hC : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hN : IsNoetherian X := { }
  obtain ⟨n, Z, j, hj, hcov⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Approx.exists_integral_closed_cover X
  have key : ∀ i, ∃ (X' : Scheme.{0}) (π : X' ⟶ Z i), IsProper π ∧ Surjective π ∧
      IsQProjOver (π ≫ j i ≫ p) := by
    intro i
    have := (hj i).1
    have := (hj i).2
    exact _root_.GlobalTheory.CompanionTheory.Ar.Approx.exists_isProper_surjective_isQProjOver k (Z i) (j i ≫ p) inferInstance inferInstance inferInstance
  choose Y π hp hsurj hqp using key
  refine ⟨n, Y, fun i => π i ≫ j i, fun i => ?_, fun x => ?_⟩
  · have := (hj i).2
    have := hp i
    refine ⟨inferInstance, ?_⟩
    rw [Category.assoc]
    exact hqp i
  · obtain ⟨i, z, rfl⟩ := hcov x
    obtain ⟨y, rfl⟩ := (hsurj i).surj z
    exact ⟨i, y, by simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

