module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0174
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0197
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfMain
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeight

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedOfGenericFiberSmoothProper
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem dense_range_fst_generic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsOpenMap p) :
    Dense (Set.range (pullback.fst p (spMap (algebraMap R K)))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let y : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hy : ∀ z : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap R K) y ⤳ z := by
    intro z
    rw [← PrimeSpectrum.le_iff_specializes]
    intro a ha
    have h0 : algebraMap R K a = 0 := ha
    have : a = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact z.asIdeal.zero_mem
  have hyy : (spMap (algebraMap R K)) y = PrimeSpectrum.comap (algebraMap R K) y := rfl
  rw [Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  have hmem : (spMap (algebraMap R K)) y ∈ p '' U := by
    rw [hyy]
    exact (hy (p x)).mem_open (hp U hU) ⟨x, hx, rfl⟩
  obtain ⟨x', hx'U, hx'⟩ := hmem
  exact ⟨x', hx'U, ⟨y, hx'.symm⟩⟩

theorem geometricallyConnected_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  intro R K _ _ _ _ _ G _ _ hsm hpr hgc
  set f := spMap (algebraMap R K) with hf
  let F := Over.pullback f
  let GK := F.obj G
  have hab : IsAbelianScheme GK := by
    refine IsAbelianScheme.mk inferInstance ?_ ?_ hgc
    · show Smooth (pullback.snd G.hom f)
      infer_instance
    · show IsProper (pullback.snd G.hom f)
      infer_instance
  refine _root_.GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow (Sp R) G inferInstance inferInstance ?_
  intro n hn
  have hK := _root_.GlobalTheory.CompanionTheory.Ar.Approx.surjective_pow_of_isAbelianScheme K GK hab n hn
  have hmap : F.map (𝟙 G ^ n) = 𝟙 GK ^ n := by
    rw [← F.map_id]
    exact (Functor.homMonoidHom F (X := G) (M := G)).map_pow _ n
  set φ := (𝟙 G ^ n).left with hφ
  have hsq : (𝟙 GK ^ n).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ φ := by
    rw [← hmap]
    simp [F, φ] <;> exact pullback.lift_fst _ _ _
  have hw : φ ≫ G.hom = G.hom := Over.w (𝟙 G ^ n)
  have hcomp : IsProper (φ ≫ G.hom) := by rw [hw]; exact hpr
  have hsep : IsSeparated G.hom := inferInstance
  have hprop : UniversallyClosed φ := by
    first
    | exact (MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) φ G.hom hsep hcomp).toUniversallyClosed
    | exact MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated) φ G.hom hsep inferInstance
    | exact UniversallyClosed.of_comp_of_isSeparated φ G.hom
    | exact (IsProper.of_comp φ G.hom).toUniversallyClosed
  have hcl : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hop : IsOpenMap G.hom := G.hom.isOpenMap
  have hdense := dense_range_fst_generic R K G.hom hop
  have hsub : Set.range (pullback.fst G.hom f) ⊆ Set.range φ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hK.surj z
    refine ⟨pullback.fst G.hom f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have huniv : Set.range φ = Set.univ :=
    (hdense.mono hsub).closure_eq ▸ hcl.closure_eq.symm
  exact ⟨fun x => by
    have : x ∈ Set.range φ := huniv ▸ Set.mem_univ x
    exact this⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_frame_relay_bound :
    GlobalTheory.CompanionTheory.Ar.Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | exact GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semi_abelian_pullback_torus_extension : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopPt.main | exact GlobalTheory.CompanionTheory.Ar.TopPt.main | (intros; apply GlobalTheory.CompanionTheory.Ar.TopPt.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionOne
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_hopf_main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La), ∃ (U : ∀ n, (X.Γ n).G.left.Opens) (H : ∀ n, Subgroup (LevGrp La p n)), (∀ n, (X.Γ n).IsFinOpenSub (U n)) ∧ (∀ n (g : (X.Γ n).G.left), (X.Γ n).G.hom g = IsLocalRing.closedPoint O → g ∈ U n) ∧ (∀ n t, t ∈ H n ↔ ∀ z, ((X.Γ n).pt t).left z ∈ U n) ∧ (∀ n, IsHopfOrder ((X.Γ n).btOrder ⊤)) ∧ (∀ n, IsHopfOrder (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n, (X.Γ n).btOrder ⊤ = indOrder (H n).subtype (resOrder (H n).subtype ((X.Γ n).btOrder ⊤))) ∧ (∀ n (a : La), lev p n a ∈ H n ↔ lev p (n + 1) (p • a) ∈ H (n + 1)) ∧ ∀ n (a : La), lev p n a ∈ H n → ∃ b : La, lev p (n + 1) b ∈ H (n + 1) ∧ lev p n b = lev p n a :=
  PositivityTheory.HtPt.Twhopf.tw_hopf

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieMetricHeightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_lie_metric_height : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y), ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK), letI := τ.addCommGroup; IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier, (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) → ∀ (σ : L →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.torus_unif <;> assumption)
end

