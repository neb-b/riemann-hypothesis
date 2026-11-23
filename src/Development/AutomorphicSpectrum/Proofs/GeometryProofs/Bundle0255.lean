module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0037
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0076
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceTestFunction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeChartDualRankBound
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.NonemptyComponentModel
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsTiedRegularSetting
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0250
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0252
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GagaLineGeneratorEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperPullbackLineBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0153
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeDegree
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq

theorem isCp_dvd_sq (Ω : Type) [Field Ω] (A : Subring Ω) (p : ℕ) [hp : Fact p.Prime] (κ : Ω) (hκA : κ ∈ A)
    (hκ : HT.IsCp p κ) : ∃ u ∈ A, (p : Ω) ^ 2 = κ * u := by
  unfold HT.IsCp at hκ
  split_ifs at hκ with h2
  · exact ⟨1, A.one_mem, by rw [hκ, h2]; norm_num⟩
  · obtain ⟨ζ, hζ, rfl⟩ := hκ
    have hζA : ζ ∈ A := by simpa using A.add_mem hκA A.one_mem
    have hsum : ∑ i ∈ Finset.range p, ζ ^ i = 0 := hζ.geom_sum_eq_zero hp.out.one_lt
    have hp' : (p : Ω) = ∑ i ∈ Finset.range p, (1 - ζ ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    have hterm : ∀ i, (1 : Ω) - ζ ^ i = (1 - ζ) * ∑ j ∈ Finset.range i, ζ ^ j := fun i => by
      rw [mul_comm, geom_sum_mul_neg]
    have hv : (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) ∈ A :=
      A.sum_mem fun i _ => A.sum_mem fun j _ => A.pow_mem hζA j
    have hpv : (p : Ω) = -(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j := by
      rw [hp', Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      ring
    refine ⟨-(p : Ω) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j,
      A.mul_mem (A.neg_mem (natCast_mem A p)) hv, ?_⟩
    calc (p : Ω) ^ 2 = p * p := sq _
      _ = p * (-(ζ - 1) * ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, ζ ^ j) := by rw [← hpv]
      _ = _ := by ring

theorem generatesDiff_one {O Ω E : Type} [CommRing O] [Field Ω] [Algebra O Ω] [Field E] [NumberField E]
    (R : Subalgebra O Ω) (σ : E →+* Ω) (h1 : ∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E))
    (h2 : ∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * σ (x : E) = 1) :
    HT.GeneratesDiff σ (1 : R) := by
  have hmem : ∀ a : 𝓞 E, σ (a : E) ∈ R := fun a => by
    obtain ⟨o, ho⟩ := h1 a
    rw [← ho]
    exact R.algebraMap_mem o
  obtain ⟨x, hx, o, ho⟩ := h2
  unfold HT.GeneratesDiff
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, map_one]
    have : (1 : Ω) = (algebraMap O R o) • σ (x : E) := by
      rw [← ho]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨z, -, rfl⟩
    have : σ (z : E) = (⟨σ (z : E), hmem z⟩ : R) • algebraMap R Ω 1 := by
      rw [map_one]; exact (_root_.mul_one _).symm
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem seq_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (t : CMType H ⊕ CMType H), ∃ i : (Fin (labelRk D t) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p t) (b t) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p t.swap) (b t.swap) c')) i (qMap P (b t.swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb t a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p t) (b t) c') (b t) i := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hA hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _
    _ _ _ _ w hw G c' hc' P t
  obtain ⟨hchar, hN, hI, hFr, hreg, hpt⟩ := _root_.PositivityTheory.Xgn.sequence_ring_exists E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O c' hc'
  haveI := hchar
  haveI := hN
  haveI := hI
  haveI := hFr
  have hc : ∀ x, HT.cmConj E (HT.cmConj E x) = x := fun x => by simp [HT.cmConj]
  obtain ⟨σ, hσ, hσ', huniq⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab.exists_labelEmbedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  have hd := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.Diff.embedding_integers_and_different_unit E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hdisc A m hpm O
  have hgd : ∀ τ : E →+* Ω, HT.GeneratesDiff τ (1 : CR O y c') := fun τ =>
    generatesDiff_one _ τ (hd τ).1 (hd τ).2
  have hloc := _root_.PositivityTheory.Xgn.sequence_localization_exists E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS A m hpm O G c' hc' P
  obtain ⟨hpO, hpH⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_om_eigQuot_projective E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hfree hdisc A m hpm O G c' hc' P hN hpt hloc
  have htest := _root_.PositivityTheory.Xgn.sequence_test_function hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS hp2 A m hpm O w hw G c' hc' P
  have hR := 𝔐.R_ge p hpS
  obtain ⟨n, hn⟩ : ∃ n, 𝔐.R p = (n + 2) + 2 := ⟨𝔐.R p - 4, by omega⟩
  have hm : 𝔐.R p - 2 = n + 2 := by omega
  obtain ⟨u, huR, hu⟩ := isCp_dvd_sq Ω (CR O y c').toSubring p (algebraMap O Ω w)
    ((CR O y c').algebraMap_mem w) hw
  have hdiv : algebraMap O (CR O y c') w * (p : CR O y c') ^ (𝔐.R p - 2) ∣ (p : CR O y c') ^ (𝔐.R p) := by
    refine ⟨⟨u, huR⟩, Subtype.ext ?_⟩
    rw [hm, hn]
    push_cast
    rw [pow_add (p : Ω) (n + 2) 2, hu]
    ring
  obtain ⟨-, hseq⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence (CR O y c') Ω E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li) P.Dh
    (algebraMap O (CR O y c') w) (𝔐.R p - 2) hdiv htest hpO
  obtain ⟨i₀, hDm, hEx⟩ := hseq σ 1 1 (hgd σ) (hgd _) (hpH t σ hσ) (hpH t.swap _ hσ')
  have hact : ∀ (a : 𝓞 E) (w : Module.Dual Ω 𝔐.Li), P.Dh.ρΩ a w = w ∘ₗ 𝔐.ρ (RingOfIntegers.mapRingEquiv (HT.cmConj E) a) :=
    fun a w => by
      rw [HT.ModelTest.bar_eq H a]
      exact P.Dh_act a w
  have hV : ∀ (s : CMType H ⊕ CMType H) (τ : E →+* Ω), (∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) →
      Submodule.span Ω (Set.range (b s)) = HT.eigSp 𝔐.ρ τ := by
    intro s τ hτ
    rw [(hb s).2]
    unfold HodgeCpt.Vgen GlobalTheory.CompanionTheory.Ar.eigSp HT.eigSp
    refine iInf_congr fun a => ?_
    rw [hτ a]
    rfl
  have hcoord := fun (s : CMType H ⊕ CMType H) (τ : E →+* Ω) (hτ : ∀ a : 𝓞 E, τ (a : E) = 𝔐.emb s a) =>
    _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hA hpq p hpS b hb A m hpm O G c' hc' P s
      (fun a => by rw [← hτ a]; exact (hd τ).1 a)
      (by
        obtain ⟨x, hx, o, ho⟩ := (hd τ).2
        exact ⟨x, hx, o, by rw [← hτ x]; exact ho⟩) hreg hpt hloc
  have hwu : ∃ v ∈ CR O y c', (p : Ω) ^ (𝔐.R p - 2) = algebraMap O Ω w * v := by
    refine ⟨u * (p : Ω) ^ n, (CR O y c').mul_mem huR ((CR O y c').pow_mem (natCast_mem _ p) n), ?_⟩
    rw [hm, pow_add, mul_comm ((p : Ω) ^ n), hu]
    ring
  obtain ⟨i, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.SeqPure.seqHyp_chart O Ω 𝔐.Li (CR O y c') E (HT.cmConj E) hc p (𝔐.R p) (D.p + D.q) _ _ (𝔐.R p - 2) P.Dh 𝔐.ρ hact σ
    i₀ hEx hDm (hpH t σ hσ) (b t) (b t.swap) (hb t).1 (hV t σ hσ) (hb t.swap).1 (hV t.swap _ hσ') _ _
    (hcoord t σ hσ) (hcoord t.swap _ hσ') (algebraMap O Ω w) ((CR O y c').algebraMap_mem w) hwu
  refine ⟨i, h1, fun σE hσE a ha j => ?_⟩
  rw [huniq σE hσE]
  exact h2 a ha j

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Seq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspWeightRegularisationsTied
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.cusp_weight_regularisations_tied : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd), ∃ (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S : LogLogRegularisationSetting M Dc.Xo (muLine Hd)) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), Or.𝔐.IsCuspWeight Or.sm U ∧ (∀ z, 0 ≤ U z) ∧ (∀ z ∈ Dc.Xo, ∀ t : K → ℂ, (∀ k, t k ≠ 0) → U (torusSmul t z) = U z) ∧ S.IsTied ∧ S'.IsTied ∧ ConjU S' := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or
  obtain ⟨U, hU, h0, hT, hC, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.WeightEx.exists_cuspWeight hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or
  obtain ⟨hp1, -, hp2, hc2⟩ := GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨hb, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd.corr_bdd hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU
  obtain ⟨-, -, hL, hO⟩ := _root_.LevelTowerAlt.mu_frame_norm_line K J II (CMType H) Ω W Dc Hd
  obtain ⟨M⟩ := _root_.LevelTowerAlt.nonempty_component_model K J II (CMType H) Ω W Dc
  obtain ⟨S, hS⟩ := _root_.LevelTowerAlt.exists_tied_regular_setting K J II (CMType H) Ω W Dc Hd M hp1
  obtain ⟨S', hS', hJ⟩ := _root_.GlobalTheory.CompanionTheory.Relay.exists_regularization_setting K J II (CMType H) Ω W Dc Hd M (corrW Hd U)
    (fun z hz a ha => by
      have := hL z hz a ha
      simp only [corrW, hT z a ha, this]
      ring)
    hp2 hc2 hb
    (fun z hz => by
      have := hO z hz
      simp only [corrW, hC z, this])
  exact ⟨U, M, S, S', hU, h0, fun z _ t ht => hT z t ht, hS, hS', hJ⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenOnModel

theorem isPreimmersion_fst {O K : Type} [CommRing O] [Field K] (β : O →+* K) {X : Scheme.{0}} (s : X ⟶ Sp O)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : K, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion (pullback.fst s (spMap β)) := by
  obtain ⟨hi, -, hx⟩ := hβ
  have hdom : IsDomain O := hi.isDomain β
  letI : Algebra O K := β.toAlgebra
  haveI : FaithfulSMul O K := (faithfulSMul_iff_algebraMap_injective O K).2 hi
  have hloc : IsLocalization (nonZeroDivisors O) K := by
    refine IsFractionRing.of_field O K fun z => ?_
    obtain ⟨a, b, hb, e⟩ := hx z
    exact ⟨a, b, by
      change z = β a / β b
      rw [← e]; field_simp⟩
  have h : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := K) (nonZeroDivisors O)
  infer_instance

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) (π : X ⟶ X') :
    genPt (ξ ≫ π) = π (genPt ξ) := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.GenOnModel

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GenOnModel

theorem exists_gen_of_unitAn : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → Z.IsGeom → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → ∃ (f : Z.Ω) (κ : ℂ) (W : (Xo.XF c).Opens), κ ≠ 0 ∧ genPt Z.ξ₀ ∈ W ∧ IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (f • exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) Z.genFib ∧ ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap σ → ⊤ ≤ y ⁻¹ᵁ W → Set.range y ⊆ U → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed U τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) f (κ * Φ y v w) := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ hβ hpq hτ hσ hgeom hΦ hi₁ hs₁ hi₂ hs₂
  classical
  have hξ : IsCptGen (Z.ξ₀ ≫ Y.j) := Z.gen
  obtain ⟨hA, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ hβ hτ
  have hη : (⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨W₁, hW₁, hf₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt _ _ _ _ (Z.eig τ) Z.genFib D.p _ b₁ hξ hη hA hi₁ hs₁
  obtain ⟨W₂, hW₂, hf₂⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen.isFrameAt_near_genPt _ _ _ _ (Z.eig (ComplexEmbedding.conjugate τ)) Z.genFib D.q _ b₂ hξ hη hB hi₂ hs₂
  obtain ⟨hwA, ha⟩ := GlobalTheory.T.wedge_lattice_generator _ _ _ _ (Z.eig τ) D.p b₁ _ (hf₁ _ hη hW₁)
  obtain ⟨hwB, hb⟩ := GlobalTheory.T.wedge_lattice_generator _ _ _ _ (Z.eig (ComplexEmbedding.conjugate τ)) D.q b₂ _ (hf₂ _ hη hW₂)
  have hcoef : IsCoeffAt (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)
      ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩ 1 :=
    ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul]; exact hwA, by rw [one_smul]; exact hwB, by simp⟩
  obtain ⟨hLvb, hLgen, hLfr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.lineLat_isVBOn_gen_frames _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _
    Z.genFib _ _ hA hB ha hb ⟨_, hη, 1, hcoef⟩
  have hW₀gen : ∀ x ∈ Z.genFib, x.1 ∈ W₁ ⊓ W₂ → (lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).IsGenAt x 1 := fun x hx hxW => by
    have := hLfr x hx b₁ b₂ 1 1 (hf₁ x hx hxW.1) (hf₂ x hx hxW.2) (by rw [one_smul]) (by rw [one_smul])
    simpa using this
  have hpre : IsPreimmersion (pullback.fst Y.s (spMap β)) := isPreimmersion_fst β Y.s hβ
  obtain ⟨hnoeth, X', f, d, W', jW, hiso, hjW, hfP, hsP, hsm, hsnc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_resolution_genericFibre hRes E H D l Xo c O β Y hβ
  have hjQo : IsOpenImmersion Y.jQ := Y.jQ_open
  have hmono : Mono Y.j := by
    unfold Model.j
    infer_instance

  have hsurj := _root_.GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part _ _ _ _ (pullback.fst Y.s (spMap β)) f W' jW Y.jQ hpre hjQo hiso hjW
  obtain ⟨π, hπ⟩ : ∃ π, π = f ≫ pullback.fst Y.s (spMap β) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = f ≫ pullback.snd Y.s (spMap β) := ⟨_, rfl⟩
  rw [← hπ] at hsurj
  rw [← hs'] at hsP hsm hsnc
  have hιf : inv jW ≫ W'.ι ≫ f = Y.jQ := by rw [← hjW, IsIso.inv_hom_id_assoc]
  have hιf' : ∀ {Z' : Scheme.{0}} (t : pullback Y.s (spMap β) ⟶ Z'), inv jW ≫ W'.ι ≫ f ≫ t = Y.jQ ≫ t := by
    intro Z' t
    rw [← hιf]; simp only [Category.assoc]
  have hιπ : inv jW ≫ W'.ι ≫ π = Y.j := by rw [hπ, hιf']; rfl
  have hιs : inv jW ≫ W'.ι ≫ s' = pullback.snd _ _ := by rw [hs', hιf', Y.jQ_over]
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = Z.ξ₀ ≫ inv jW ≫ W'.ι := ⟨_, rfl⟩
  have h1 : ξ' ≫ f = Z.ξ₀ ≫ Y.jQ := by simp only [hξ', Category.assoc, hιf]
  have h2 : ξ' ≫ π = Z.ξ₀ ≫ Y.j := by simp only [hξ', Category.assoc, hιπ]
  have h3 : ξ' ≫ s' = spMap Z.inc := by
    simp only [hξ', Category.assoc, hιs]; exact Z.over_inc
  have hgW' : genPt ξ' ∈ W' := by
    rw [hξ', ← Category.assoc, genPt_comp]
    exact (genPt (Z.ξ₀ ≫ inv jW)).2
  have hsm' : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hξg : IsCptGen ξ' := _root_.GlobalTheory.CompanionTheory.Ar.CptLift.isCptGen_of_smooth_of_surjective c.F _ _ _ _ ξ' π s' hsm' h2 hξ (hsurj _ hgW')
  have hdom : Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    unfold Dominates
    rw [h2]
    simp
  obtain ⟨L, hLd⟩ : ∃ L, L = lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q
      (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂) := ⟨_, rfl⟩
  rw [← hLd] at hLvb hLgen hW₀gen
  have hcpt : ∀ p' : Cpt ξ', ∃ h : genPt (Z.ξ₀ ≫ Y.j) ⤳ π p'.1, (⟨π p'.1, h⟩ : Cpt _) ∈ Z.genFib := fun p' => by
    obtain ⟨h, -, -⟩ := pull_reg_and_gen _ _ _ _ _ ξ' π (RingHom.id _) hdom p'
    exact ⟨h, ⟨f p'.1, by subst hπ; rfl⟩⟩
  have hL'vb : (L.pull ξ' π (AddMonoidHom.id _)).IsVB 1 ⊤ := by
    intro p' _
    obtain ⟨h, hT⟩ := hcpt p'
    obtain ⟨N, hN, bb, hbb, hfr⟩ := hLvb _ hT
    refine ⟨π ⁻¹ᵁ N, hN, bb, hbb, fun q' _ hq' => ?_⟩
    obtain ⟨h', hT'⟩ := hcpt q'
    have hfr' := hfr _ hT' hq'
    exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.Lat.pull_isFrameAt_comp _ _ (Z.ξ₀ ≫ Y.j) _ _ ξ' π (RingHom.id _) Z.Ω Z.Ω (AddMonoidHom.id _) hdom
      (fun a e => rfl) L 1 bb q' h' hfr'.1 hfr'
  obtain ⟨W, hWd⟩ : ∃ W : X'.Opens, W = (π ⁻¹ᵁ (W₁ ⊓ W₂)) ⊓ W' := ⟨_, rfl⟩
  have hWW' : W ≤ W' := by rw [hWd]; exact inf_le_right
  have hgW : genPt ξ' ∈ W := by
    rw [hWd]
    refine ⟨?_, hgW'⟩
    show π (genPt ξ') ∈ W₁ ⊓ W₂
    rw [← genPt_comp, h2]
    exact ⟨hW₁, hW₂⟩
  have hgenW : ∀ p : Cpt ξ', p.1 ∈ W → (L.pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1 := fun p hp => by
    obtain ⟨h, hr, hg⟩ := pull_reg_and_gen _ _ _ _ _ ξ' π (RingHom.id _) hdom p
    have hpW : π p.1 ∈ W₁ ⊓ W₂ := by rw [hWd] at hp; exact hp.1
    obtain ⟨h', hT⟩ := hcpt p
    exact hg L 1 (hW₀gen _ hT hpW)

  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → Prop, ∀ y v w, Q y v w ↔
      (IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧
        ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w')) := ⟨_, fun _ _ _ => Iff.rfl⟩
  have hex : ∀ y : Sp ℂ ⟶ Xo.XF c, ∃ r : ℂ, (∃ v w, Q y v w) → ∃ v w, Q y v w ∧ r = Φ y v w := fun y => by
    by_cases h : ∃ v w, Q y v w
    · obtain ⟨v, w, hq⟩ := h
      exact ⟨Φ y v w, fun _ => ⟨v, w, hq, rfl⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Φ₀ hΦ₀ using hex
  have hexF : ∀ y' : Sp ℂ ⟶ X', ∃ r : ℂ, ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ Y.j = y' ≫ π → r = Φ₀ y := fun y' => by
    by_cases h : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Y.j = y' ≫ π
    · obtain ⟨y, hy⟩ := h
      refine ⟨Φ₀ y, fun y₂ h₂ => ?_⟩
      rw [(cancel_mono Y.j).1 (hy.trans h₂.symm)]
    · exact ⟨0, fun y hy => absurd ⟨y, hy⟩ h⟩
  choose F hF using hexF
  have H1 : ∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' →
      y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q),
        IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧
        ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w := by
    intro y' y _ hW hsp hy hys
    have hc : centre (y ≫ Y.j) = π (centre y') := by rw [hy]; rfl
    have h₀ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
      rw [hc, ← h2, genPt_comp]
      exact hsp.map π.continuous
    have hT : (⟨_, h₀⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), rfl⟩
    have hcW : centre y' ∈ W := hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    have hxW : centre (y ≫ Y.j) ∈ W₁ ⊓ W₂ := by
      rw [hc]
      rw [hWd] at hcW
      exact hcW.1
    obtain ⟨v, w, hf, hv, hw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FrameVal.exists_framed_values E H D l Xo c O β Y U Z τ σ b₁ b₂ y h₀ hβ hτ hσ hys
      (hf₁ _ hT hxW.1) (hf₂ _ hT hxW.2)
    obtain ⟨v₂, w₂, hq, hr⟩ := hΦ₀ y ⟨v, w, (hQ y v w).2 ⟨hf, hv, hw⟩⟩
    obtain ⟨q1, q2⟩ := (hQ y v₂ w₂).1 hq
    exact ⟨v₂, w₂, q1, q2, by rw [hF y' y hy, hr]⟩
  have hπs : π ≫ Y.s = s' ≫ spMap β := by
    rw [hπ, hs', Category.assoc, Category.assoc, pullback.condition]
  have hj1 : jW ≫ Y.j = W'.ι ≫ π := by
    rw [hπ]
    show jW ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hjW, Category.assoc]
  have hj2 : jW ≫ pullback.snd _ _ = W'.ι ≫ s' := by
    rw [hs', ← Y.jQ_over, ← Category.assoc, hjW, Category.assoc]
  letI : Algebra c.F Z.Ω := Z.inc.toAlgebra
  have hconst : ConstClosed c.F Z.Ω := fun a ha => by
    obtain ⟨p, hp0, hp⟩ := ha
    obtain ⟨x, rfl⟩ := hgeom a ⟨p, hp0, by rwa [Polynomial.aeval_def] at hp⟩
    exact ⟨x, 1, one_ne_zero, by simp; rfl⟩
  subst hLd
  have hext := _root_.GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution E H D l Xo c O β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ
    hi₁ hs₁ hi₂ hs₂ hπs hsm hsnc h2 hξg hj1 hj2 hWW' H1 hgenW
  obtain ⟨f₀, κ, hκ, hgen, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.gaga_rat hGaga c.F σ X' s' Z.Ω ξ' _ W F hsP hsm' h3 hξg hconst hL'vb hgW
    hgenW hext
  have hnorm : NormalCpt (Z.ξ₀ ≫ Y.j) := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen hξ Y.normal
  have hall := _root_.GlobalTheory.CompanionTheory.Ar.Flat.PushLoc.gen_descends _ _ _ _ (Z.ξ₀ ≫ Y.j) (Z.ξ₀ ≫ Y.jQ) ξ' (pullback.fst Y.s (spMap β)) f _ Z.genFib f₀ hpre hfP
    hnoeth (by simp [Model.j]) h1 hξ hnorm (fun x => Iff.rfl) hLvb (by rw [← hπ]; exact hgen)
  have hf0 : f₀ ≠ 0 := (hall _ hη).1
  refine ⟨f₀, κ, Y.j ⁻¹ᵁ (W₁ ⊓ W₂), hκ, ⟨hW₁, hW₂⟩, ⟨smul_ne_zero hf0 ha, hb, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨-, α, β', hα, hβ', hwa, hwb, e⟩ := (hLgen x hx f₀).1 (hall x hx)
    refine ⟨α / f₀, β', div_ne_zero hα hf0, hβ', ?_, hwb, ?_⟩
    · rw [smul_smul, div_mul_cancel₀ _ hf0]
      exact hwa
    · rw [_root_.one_mul, ← e]
      field_simp
  · intro y hys hyW hyU
    obtain ⟨y', hy'⟩ : ∃ y', y' = y ≫ inv jW ≫ W'.ι := ⟨_, rfl⟩
    have e1 : y' ≫ π = y ≫ Y.j := by simp only [hy', Category.assoc, hιπ]
    have e2 : y' ≫ s' = spMap σ := by simp only [hy', Category.assoc, hιs]; exact hys
    have hpt : ∀ pt, y' pt ∈ W := fun pt => by
      have hp : y pt ∈ Y.j ⁻¹ᵁ (W₁ ⊓ W₂) := hyW (show pt ∈ (⊤ : (Sp ℂ).Opens) from trivial)
      rw [hWd]
      refine ⟨?_, ?_⟩
      · show π (y' pt) ∈ W₁ ⊓ W₂
        have : π (y' pt) = Y.j (y pt) := by
          rw [← Scheme.Hom.comp_apply, e1, Scheme.Hom.comp_apply]
        rw [this]
        exact hp
      · rw [hy']
        exact ((y ≫ inv jW) pt).2
    have hyW' : ⊤ ≤ y' ⁻¹ᵁ W := fun pt _ => hpt pt
    have hsp : genPt ξ' ⤳ centre y' := by
      rw [hξ', hy']
      exact ((Z.closure _).1 (hyU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)).map (inv jW ≫ W'.ι).continuous
    obtain ⟨v, w, hf, hv, hFe⟩ := H1 y' y e2 hyW' hsp e1.symm hys
    refine ⟨v, w, ⟨hf.1, hyU, hf.2.2.1, hf.2.2.2⟩, hv, ?_⟩
    have hv' := hval y' e2 hyW' hsp
    have hs := hsurj (centre y') (hWW' (hpt _))
    have h := _root_.GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective _ _ _ _ _ ξ' π y' f₀ _ h2 hs hv'
    rw [e1, hFe] at h
    exact h

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | exact GlobalTheory.CompanionTheory.Ar.ChgField.exists_field | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgField.exists_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveHodgePrimeStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_hodge_prime : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameCombinedStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_combined : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_combined <;> assumption)
end

