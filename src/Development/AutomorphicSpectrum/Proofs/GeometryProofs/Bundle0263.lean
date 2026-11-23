module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0262
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsReferenceGeometrySameGeneric
public import Development.WeilBound.CoreStatements.CentralCharts.ReferenceGeometryHolomorphicInverse
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSection
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.HeightComparisonGlobalModel
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Rt0ConjNegNeZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0261
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemSpan
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTowerStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_setting_of_good_tower : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : _root_.GlobalTheory.CompanionTheory.Ar.Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  exact _root_.GlobalTheory.CompanionTheory.Ar.Cusp.TopBase.base_setting_of_good_origin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGoodRootTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopTower

theorem comp_data (hG : Top.Given) (hA0 : Flat.FlatLineGenerator) (hA1 : Flat.FlatLineGeneratorComponent)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l)
    (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
    (hgl : Top.IsGlobal Xo l c Y) (hsp : SplitComps Y) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q)
    (x : Y.X) (hx : ∀ x' : Y.X, x' ⤳ x → x' = x) :
    ∃ (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
      (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx),
      genPt Fx.ξf = x ∧
      (∀ r : RootIx D, (Fx.n r : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-((r.2 : ℕ) : ℝ))) ∧
      o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧
      Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧
      (∀ τ (i : Fin (D.p + D.q)), (i : ℕ) + 1 = D.p + D.q → ∀ t,
        ReciprocityTheory.AnForm.M.IsPsh Sys.A ((Sys.potT (some (τ, i)) t).rsmul (-1)) ∧
          ReciprocityTheory.AnForm.M.IsPsh Sys.A (Sys.potT (some (τ, i)) t)) ∧
      (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
        (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧
        ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source →
          (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p)
            (Sys.A.chart j x)).ker = ⊥) := by
  have hdom : ∀ x, IsDomain (Y.X.presheaf.stalk x) := fun x => (Y.normal x).1
  have hcg := GlobalTheory.T.isCptGen_residue_field_generic Y.X hdom x hx
  obtain ⟨G, hG0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_refGeo hG.2.2.2.2.1 E H D l (Xo l) c Y _ (Y.X.fromSpecResidueField x) hcg
  obtain ⟨A, hinv⟩ := _root_.AnalyticReference.reference_geometry_holomorphic_inverse hG hA0 hA1 E H D Xo l c Y hgl hsp hp hq G
  let ν : RootIx D → ℤ := fun r => -((r.2 : ℕ) : ℤ)
  have hν : ∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i) := by
    intro τ i k hik
    simp only [ν, neg_lt_neg_iff]
    exact_mod_cast hik
  obtain ⟨k, q', s, hk, hq', hs, heff⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff hG E H D Xo l c Y hgl hp hq G ⟨A⟩ ν hν
  obtain ⟨Fx, R, o, hgen, hkA, hq'', hn, hdeg, hJ, hamp, hemb, hbij, hlam⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot E H D l (Xo l) c Y G A ν k q' s hinv hsp hk hq' hs heff
  refine ⟨A.Sys, Fx, R, o, ?_, ?_, hdeg, hJ, hamp, hemb, hbij, A.flat, hlam⟩
  · rw [hgen, hG0]
    exact Scheme.fromSpecResidueField_apply x _
  · intro r
    rw [hn r, hkA, hq'']
    simp [ν]

theorem level_data (hG : Top.Given) (hW : Out.WeilSt)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} (Fx : FixedData Y Sys)
    (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx)
    (hdeg : o.Fl.deg = 1) (hemb : Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift)
    (hbij : Function.Bijective o.Re.π)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) :
    ∃ (RM : Top.RootModel (CMType H) (D.p + D.q)) (o' : RootOrigin Y S RM Fx), o'.𝔐.OmVB ∧
      (∀ p ∈ S, o'.𝔐.R p = 4) ∧ o'.Re.J = ⊤ ∧ ∃ _ : Algebra ℚ RM.Ω, SmoothGenericFibreM RM.y := by
  obtain ⟨Ω, _, _, K, _, J, _, y, bk, bx, i, 𝔐, h, Fl, xdeg, e, hbk, hy, hd, hf, hcst, hfl, hfin, hlines,
    hom, hsm, hR⟩ := GlobalTheory.T.root_origin_good_primes_finite hG hW E H D l Xo c Y Sys Fx R o S hS hdisc hdeg
  obtain ⟨RM, o', h1, h2, h3, h4⟩ := GlobalTheory.T.root_origin_coords_over_field hG E H D l Xo c Y Sys Fx R o S Ω K J y bk bx i 𝔐 h Fl
    xdeg e hdeg hemb hbij hbk hy hd hf hcst hfl hfin hlines hom hsm
  refine ⟨RM, o', h1, fun p hp => ?_, h3, h4⟩
  rw [h2]
  exact hR p hp

theorem exists_good_tower : Top.Given → Out.WeilSt → Flat.FlatLineGenerator → Flat.FlatLineGeneratorComponent → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)], Top.IsGlobal Xo l c Y → SplitComps Y → 1 ≤ D.p → 1 ≤ D.q → ∃ (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T), (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) ∧ ∀ B a, ∀ p ∈ o.S B, (o.Or B a).𝔐.R p = 4 := by
  intro hG hW hA0 hA1 E _ _ _ H D Xo l c Y _ hgl hsp hp hq
  obtain ⟨hfin, hne⟩ := GlobalTheory.T.generic_points_finite_nonempty hG E H D l (Xo l) c Y
  let Smax : Set Y.X := {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}
  haveI : Fintype Smax := Set.Finite.fintype hfin
  haveI : Nonempty Smax := hne.to_subtype
  choose Sys Fx R o hgen hnu hdeg hJ hamp hemb hbij hflat hlam using
    fun a : Smax => comp_data hG hA0 hA1 Xo l c Y hgl hsp hp hq a.1 a.2
  have hM' : l.M' ≠ 0 := by
    show Nat.lcm l.M l.A ≠ 0
    exact Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have hn0 : 2 * (discr E).natAbs * l.M' ≠ 0 := by
    exact Nat.mul_ne_zero (Nat.mul_ne_zero two_ne_zero (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E))) hM'
  let bad : Finset ℕ := (2 * (discr E).natAbs * l.M').primeFactors
  have hbad : ∀ r : ℕ, r ∈ bad ↔ r.Prime ∧ (r : ℤ) ∣ 2 * discr E * l.M' := by
    intro r
    simp only [bad, Nat.mem_primeFactors, Int.natCast_dvd, Int.natAbs_mul]
    simp [hn0]
  let SB : ℕ → Finset ℕ := fun B => (Finset.range (B + 1)).filter Nat.Prime ∪ bad
  have hSB : ∀ B r, r ∈ SB B ↔ r.Prime ∧ (r ≤ B ∨ r ∈ bad) := by
    intro B r
    simp only [SB, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h2, Or.inl (by omega)⟩
      · exact ⟨((hbad r).1 h).1, Or.inr h⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact Or.inl ⟨by omega, h1⟩
      · exact Or.inr h2
  have hSBp : ∀ B, ∀ p ∈ SB B, p.Prime := fun B p hp => ((hSB B p).1 hp).1
  have hSBd : ∀ B, ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ SB B := by
    intro B p hp hd
    refine (hSB B p).2 ⟨hp, Or.inr ((hbad p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
  choose RM o' hom hR hJ' hsm using fun (B : ℕ) (a : Smax) =>
    level_data hG hW Y (Fx a) (R a) (o a) (hdeg a) (hemb a) (hbij a) (SB B) (hSBp B) (hSBd B)
  let T : Top.RootTower (CMType H) (D.p + D.q) :=
    { j := D.p
      j_pos := hp
      j_lt := by omega
      Comp := Smax
      bad := bad
      two_mem := (hbad 2).2 ⟨Nat.prime_two, Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _⟩
      nu := fun _ i => -((i : ℕ) : ℝ)
      nu_rat := fun _ i => ⟨-((i : ℕ) : ℚ), by push_cast; rfl⟩
      M := RM }
  let tor : TowerOrigin Y T :=
    { j_eq := rfl
      bad_iff := hbad
      S := SB
      S_iff := hSB
      Sys := Sys
      Fx := Fx
      comp_inj := fun a a' h => Subtype.ext (by rw [← hgen a, ← hgen a']; exact h)
      comp_onto := fun x hx => ⟨⟨x, hx⟩, hgen _⟩
      nu_eq := fun a r => hnu a r
      Or := o' }
  let go : Top.GoodOrigin Y T :=
    { toTowerOrigin := tor
      omVB := hom
      smooth := fun B a => ⟨hJ' B a, hsm B a⟩
      flat := hflat
      R := R
      refOr := o
      ref_deg := hdeg
      ref_top := hJ
      ample := hamp }
  exact ⟨T, go, fun a => hlam a, fun B a p hp => hR B a p hp⟩

end GlobalTheory.CompanionTheory.Ar.TopTower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PhiDegFibLatLeOfIsOFamilyOfIsAdapted
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
namespace GlobalTheory.CompanionTheory.Ar.Cusp.U4

open LevelTowerAlt GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flat_point_of_principal_sign (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) {L : Type} [Field L] [NumberField L] (t : SAB H (Sp L)) (ht : IsPrincipal t) (ρ : L) (p' q' : ℕ)
    (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult t.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult t.act (spMap g) τ q'))
    (h1 : 1 ≤ p' + q') (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    ∃ (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (_ : NumberField c.F) (F : Type) (_ : Field F)
      (_ : NumberField F) (β : c.F →+* F) (e : L →+* F) (io : F →+* ℂ) (tK : SAB H (Sp F)) (_ : SABMap tK t (spMap e))
      (y : Sp F ⟶ Xo.XF c) (_ : SABMap tK Xo.univ.t (under y)) (U : Set (Xo.XF c)) (φ : FrameFn Xo c)
      (N : LogNorms c.F), D.p = p' ∧ D.q = q' ∧ (∀ x, io (β x) = (x : ℂ)) ∧ (∀ x, io (e x) = σ x) ∧
      y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧ IsLineFn U τ φ ∧ (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧
      (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) ∧ N.IsAdelic ∧
      N.deg = ((p' : ℝ) - q') / 2 * (GlobalTheory.CM.logOm E χ).re := by
  obtain ⟨⟨hP, hN, -, -⟩, -, -, -, hResK, -, -, hGaga, -⟩ := hG
  obtain ⟨D, rfl, rfl, ⟨I⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.SabModel.datum_tate E H L t ht σ p' q' fun τ => by
    have := hs ℂ σ τ
    rwa [hσ] at this
  let Xo : ∀ l : Level H, Moduli D l := fun l => (hN E H D l h1).some
  obtain ⟨l, hA, hg⟩ := GlobalTheory.GlobalModelGuards.exists_good_level H
  obtain ⟨c₀⟩ := GlobalTheory.ModuliProbe.coeff_nonempty l
  obtain ⟨-, c, -, hc⟩ := GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed E H D l (Xo l) c₀ h1
  haveI := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨F, hfin, hF', e, o, he, ⟨m⟩⟩ := SabModel.exists_obj_ext E H D l L t ht hA ρ σ hσ hs I c.F c.fin c.le
  haveI : NumberField F := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨f, ⟨hf, ⟨mf⟩⟩, -⟩ := (Xo l).rep (Sp F) _ inferInstance o
  let bF : c.F →+* F := (IntermediateField.inclusion hF').toRingHom
  let y : Sp F ⟶ (Xo l).XF c := pullback.lift f (spMap bF) (by
    rw [hf, ← Spec.map_comp]
    rfl)
  have hy1 : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hy2 : y ≫ pullback.snd _ _ = spMap bF := pullback.lift_snd _ _ _
  let x₀ : (Xo l).XF c := y (IsLocalRing.closedPoint F)
  let Z : Formalism.L2.Pj.Comp (Xo l) c := ⟨irreducibleComponent x₀, irreducibleComponent_mem_irreducibleComponents x₀⟩
  have hyZ : Set.range y ⊆ (Z : Set ((Xo l).XF c)) := by
    rintro _ ⟨s, rfl⟩
    rw [Subsingleton.elim s (IsLocalRing.closedPoint F)]
    exact mem_irreducibleComponent
  obtain ⟨V, hV, -⟩ := GlobalTheory.UnifFamily.exists_unf_family E H D l (Xo l) c h1
  obtain ⟨g, ty, FU, i, hty, hper⟩ := GlobalTheory.T.exists_family_uniformisation E H D l (Xo l) c Z (D.p + D.q) (V c.F.val.toRingHom).toPj h1
    (hV c.F.val.toRingHom (show Formalism.L2.Pj.GoodEmb c c.F.val.toRingHom from rfl)).1 (hc c le_rfl Z)
  have hclo : IsClopen (Z : Set ((Xo l).XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj (Xo l) c) Z
  obtain ⟨φ, N, hfg, hn, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI hResK hGaga hP E H D Xo l c (Z : Set ((Xo l).XF c)) τ g ty FU i h1 hτ hg
    hty hclo Z.2.1 hper
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ +
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  obtain ⟨had, hdeg⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames hF E H D l (Xo l) c g ty FU i _ τ φ N' χ hχ hty hτ hfg hn.1 hn.2
  exact ⟨D, l, Xo l, c, inferInstance, F, inferInstance, inferInstance, bF, e, F.val.toRingHom, o.t, m, y,
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast mf.toSABMap hy1.symm, Z, φ, N', rfl, rfl, fun _ => rfl, he, hy2, hyZ, hfg.line, hn.1,
    hn.2, had, hdeg⟩

theorem flat_hermitian_fibre_signature (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) (H : Host E) {L : Type} [Field L] [NumberField L]
    {t' : SAB H (Sp (𝓞 L))} {tB : SAB H (Sp L)} (m' : SABMap tB t' (spMap (algebraMap (𝓞 L) L)))
    {B : HermitianBundle.{0} L} (MB : LieModel t'.G (𝟙 _) B.carrier) {ρM : 𝓞 E →+* Module.End (𝓞 L) B.carrier}
    (s₁ s₂ : 𝓞 E →+* 𝓞 L) (hP : IsPrincipal tB) (hfib : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B MB)
    (hρ : MB.IsActOf t'.act.act ρM) (ρ : L) (p' q' : ℕ) (σ : L →+* ℂ) (hσ : σ ρ = H.rt0)
    (hs : ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k),
      (τ H.rt = g ρ → LieMult tB.act (spMap g) τ p') ∧ (τ H.rt ≠ g ρ → LieMult tB.act (spMap g) τ q'))
    (τ : E →+* ℂ) (hτ : τ (H.rt : E) = H.rt0) (h₁ : ∀ a, σ (s₁ a : L) = τ (a : E))
    (h₂ : ∀ a, σ (s₂ a : L) = starRingEnd ℂ (τ (a : E))) [NeZero H.d] (χ : DirichletCharacter ℂ H.d)
    (hχ : GlobalTheory.IsKroneckerChar χ) :
    |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
  have r₁ : B.rank (eigSp ρM s₁) = p' := rank_eig MB hρ m' σ s₁ ((hs ℂ σ _).1 ((h₁ _).trans (hτ.trans hσ.symm)))
  have r₂ : B.rank (eigSp ρM s₂) = q' := rank_eig MB hρ m' σ s₂ ((hs ℂ σ _).2 fun h => by
    have h3 := (h₂ H.rt).symm.trans (h.trans hσ)
    rw [hτ, (rt0_conj_neg_ne_zero H).1] at h3
    exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h3))
  rcases Nat.eq_zero_or_pos (p' + q') with h0 | h0
  · have e₁ : eigSp ρM s₁ = ⊥ := Submodule.finrank_eq_zero.1 (r₁.trans (by omega))
    have e₂ : eigSp ρM s₂ = ⊥ := Submodule.finrank_eq_zero.1 (r₂.trans (by omega))
    rw [e₁, e₂, sub_self, abs_zero]
    positivity
  obtain ⟨D, l, Xo, c, _, F, _, _, β, e, io, tK, mo, y, mf, U, φ, N, rfl, rfl, hβ, he, hy, hU, hφ, hinf, hfin, had,
    hdeg⟩ := flat_point_of_principal_sign hG hF H tB hP ρ p' q' σ hσ hs h0 τ hτ χ hχ
  obtain ⟨n₀, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m' mo
  let n : SABMap tK t' (spMap (e.comp (algebraMap (𝓞 L) L))) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.sabMapCast n₀ (LevelTowerAlt.spMap_comp _ _).symm
  have hs₁ : β.comp (tauIn c τ) = (e.comp (algebraMap (𝓞 L) L)).comp s₁ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₁ a)).symm)
  have hs₂ : β.comp (tauIn c (ComplexEmbedding.conjugate τ)) = (e.comp (algebraMap (𝓞 L) L)).comp s₂ :=
    RingHom.ext fun a => io.injective ((hβ _).trans ((he _).trans (h₂ a)).symm)
  obtain ⟨vK, vec, k1, k2, -, k4, k5⟩ := exists_vec MB hρ n mf _
    (e.injective.comp (IsFractionRing.injective (𝓞 L) L)) (𝟙 _) (Category.id_comp _) (under y)
    (Category.id_comp _).symm
  obtain ⟨x₁, hx₁⟩ := exists_smul_mem_span B _ r₁
  obtain ⟨x₂, hx₂⟩ := exists_smul_mem_span B _ r₂
  obtain ⟨N₁, a₁, d₁, i₁, f₁⟩ := exists_logNorms B _ x₁ hx₁.1 hx₁.2.1 r₁
  obtain ⟨N₂, a₂, d₂, i₂, f₂⟩ := exists_logNorms B _ x₂ hx₂.1 hx₂.2.1 r₂
  have hfr : IsFramed U τ β y (fun k => vec (x₁ k)) fun k => vec (x₂ k) :=
    ⟨hy, hU, hs₁ ▸ k4 s₁ _ x₁ hx₁.1 hx₁.2.1 hx₁.2.2, hs₂ ▸ k4 s₂ _ x₂ hx₂.1 hx₂.2.1 hx₂.2.2⟩
  have key := deg_eq_sub β e N N₁ N₂ _ (hφ.ne F β y _ _ hfr) had a₁ a₂
    (fun s => by
      rw [i₁, i₂]
      exact inf_norm MB hρ hfib n mf hy hU hφ hs₁ hs₂ k1 k2 hx₁ hx₂ hfr s (hinf _))
    fun p j => by
      obtain ⟨y₁, u₁, T₁, a1, a2, a3, a4, a5, a6, a7⟩ := f₁ p (j.comp e)
      obtain ⟨y₂, u₂, T₂, b1, b2, b3, b4, b5, b6, b7⟩ := f₂ p (j.comp e)
      rw [a7, b7]
      exact fin_norm MB hρ n mf hy hU hφ hs₁ hs₂ k1 k2 k4 k5 hfr p j a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 (hfin p _)
  rw [← d₁, ← d₂, ← key, hdeg, r₁, r₂, abs_mul]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
    linarith [(Nat.cast_nonneg D.p : (0 : ℝ) ≤ D.p), (Nat.cast_nonneg D.q : (0 : ℝ) ≤ D.q)]

theorem flat_saturation_of_degree (hG : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given) (hF : FlatDegree) : FlatSat := by
  obtain ⟨C, hC, hlog⟩ := logOm_bound
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ H L _ _ t' tB m' B MB ρM s₁ s₂ hP hfib hρ ⟨ρ, p', q', hρ2, hs⟩ hinj hconj
  obtain ⟨_, χ, hχ, hb⟩ := hlog E H
  obtain ⟨σ, hσ⟩ := SabModel.exists_embedding_rt0 H ρ hρ2
  have hi : Function.Injective ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) :=
    (σ.injective.comp (IsFractionRing.injective (𝓞 L) L)).comp hinj
  let τ : E →+* ℂ := IsFractionRing.lift hi
  have hτ : ∀ a : 𝓞 E, σ (s₁ a : L) = τ (a : E) := fun a => (IsFractionRing.lift_algebraMap hi a).symm
  have hsq : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [← hτ, H.sqrt_neg_disc_sq]
    have := congrArg ((σ.comp (algebraMap (𝓞 L) L)).comp s₁) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have h : |B.normDegree (eigSp ρM s₁) - B.normDegree (eigSp ρM s₂)| ≤
      ((B.rank (eigSp ρM s₁) : ℝ) + B.rank (eigSp ρM s₂)) * |(GlobalTheory.CM.logOm E χ).re| := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact flat_hermitian_fibre_signature hG hF H m' MB s₁ s₂ hP hfib hρ ρ p' q' σ hσ hs τ h hτ (fun a => by rw [hconj, hτ]) χ hχ
    · rw [abs_sub_comm, add_comm]
      refine flat_hermitian_fibre_signature hG hF H m' MB s₂ s₁ hP hfib hρ ρ p' q' σ hσ hs ((starRingEnd ℂ).comp τ) ?_
        (fun a => by rw [hconj, hτ]; rfl) (fun a => by rw [hτ]; exact (Complex.conj_conj _).symm) χ hχ
      rw [RingHom.comp_apply, h, map_neg, (rt0_conj_neg_ne_zero H).1, neg_neg]
  refine h.trans ?_
  rw [_root_.mul_comm C, _root_.mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end GlobalTheory.CompanionTheory.Ar.Cusp.U4


set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.phiDeg_fibLat_le_of_isOFamily_of_isAdapted : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → Fl.FlatDegree → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), admitted Xo l c Y Or B₁ → 4 * Dc.f * Dc.N ^ 2 ≤ B → Or.𝔐.IsLinPtOf z P MV A → Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) → r + k = Dc.j' → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q ≤ C * Dc.f * Dc.j' * abelian₂ B (hostRd E) (hostLval H) :=
  LevelTowerAlt.height_comparison_global_model GlobalTheory.CompanionTheory.Ar.Cusp.U4.flat_saturation_of_degree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueScalingByMonomial
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

theorem prod_pow_toNat {K : Type} [Fintype K] {F : Type} [Field F] (u : K → F) (hu : ∀ k, u k ≠ 0) (a : K → ℤ) :
    ∏ k, u k ^ (a k).toNat = (∏ k, u k ^ a k) * ∏ k, u k ^ (-a k).toNat := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h := hu k
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h]
  congr 1
  omega

theorem hasVal_twist : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω]
    (y : (Σ k, J k) → Ω) (L : Type) [Field L] (z : (Σ k, J k) → L) (a : K → ℤ) (s : Ω) (w : L),
    Small.HasVal y (0 : K → ℤ) s z w → w ≠ 0 → ∀ c : (k : K) → J k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (∀ k, z ⟨k, c k⟩ ≠ 0) → ∃ v : L, v ≠ 0 ∧ Small.HasVal y a (s * ∏ k, y ⟨k, c k⟩ ^ a k) z v := by
  intro K _ J _ Ω _ y L _ z a s w h hw c hy hz
  obtain ⟨dg, dh, g, f, hg, hf, hd, e, hn, ev⟩ := h
  have hM : ∀ m : K → ℕ, aeval z (cMon c m) ≠ 0 := fun m => by
    rw [aeval_cMon]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k)
  refine ⟨w * ∏ k, z ⟨k, c k⟩ ^ a k,
    mul_ne_zero hw (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hz k)),
    dg + fun k => (a k).toNat, dh + fun k => (-a k).toNat,
    g * cMon c fun k => (a k).toNat, f * cMon c fun k => (-a k).toNat,
    homog_mul hg (homog_cMon c _), homog_mul hf (homog_cMon c _), fun k => ?_, ?_,
    by rw [map_mul]; exact mul_ne_zero hn (hM _), ?_⟩
  · have h1 := hd k
    simp only [Pi.add_apply, Pi.zero_apply] at h1 ⊢
    push_cast
    omega
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, e,
      prod_pow_toNat (fun k => y ⟨k, c k⟩) hy a]
    ring
  · rw [map_mul, map_mul, aeval_cMon, aeval_cMon, ev,
      prod_pow_toNat (fun k => z ⟨k, c k⟩) hz a]
    ring

end GlobalTheory.CompanionTheory.Ar.ChartTwist
end
end

