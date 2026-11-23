module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0150
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0131
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCSqsys
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2278
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0253
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem flatDegreeSt_of_resK_gaga : Geo.ResK.ResKStatement → GagaSections → GlobalTheory.FlatCore.FlatDegreeSt := by
  intro hR hG E _ _ _ H _ _ χ hχ Dw l Xo c r U x hL Z τ
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec hR hG E H Dw l Xo c r U x hL χ hχ Z τ
  let t : GlobalTheory.FlatLine.FlatSec U x Z τ := s.relat (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
    (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
  have ht : t.deg = GlobalTheory.FlatLine.flatDegVal Dw (GlobalTheory.CM.logOm E χ).re := by
    have h2 := GlobalTheory.FlatLine.ConstSec.deg_relat s (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
      (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
    simp only [Pi.zero_apply, zero_sub, neg_mul, finsum_neg_distrib, GlobalTheory.FlatLine.sum_flDefect_vw] at h2
    show (s.relat _ _).deg = _
    rw [h2, hs, GlobalTheory.FlatLine.flatDegVal]; ring
  refine ⟨⟨t⟩, fun s' => ?_⟩
  rw [GlobalTheory.FlatLine.ConstSec.deg_eq hL.unf hL.geo t s', ht, neg_neg]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8Identity
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem full_intersection_tower_I8_relation : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @SquareStatements.good_tower_antisymmetry

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HeightProjectionOfInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem heightProjection_of_int : (∀ (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℤ) (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h → (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))) → GlobalTheory.Published.HeightProjection := by
  intro H k _ X Y _ p q D e hp hq π hπ hdim hdeg L h hL
  haveI : Module.Finite ℤ k := hp.finite
  have hc : ∀ τ : ℤ →+* ℂ, (wZ L (p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k X p (p ≫ spMap (Int.castRingHom k)) L
  have hc' : ∀ τ : ℤ →+* ℂ,
      (wZ (L.pull π hπ) (π ≫ p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k Y q (π ≫ p ≫ spMap (Int.castRingHom k)) (L.pull π hπ)
  have htX : GlobalTheory.IsArithVar (p ≫ spMap (Int.castRingHom k)) D :=
    isArithVar_int k X p _ D hp
  have htY : GlobalTheory.IsArithVar (π ≫ p ≫ spMap (Int.castRingHom k)) e :=
    isArithVar_int k Y q _ e hq
  have hLZ : (toZ L (p ≫ spMap (Int.castRingHom k)) hc).IsArithHeight h :=
    (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p _ D hp L hc h).mpr hL
  have key := H X Y (p ≫ spMap (Int.castRingHom k)) (π ≫ p ≫ spMap (Int.castRingHom k)) D e
    htX htY π rfl hdim hdeg (toZ L (p ≫ spMap (Int.castRingHom k)) hc) h hLZ
  have iso := _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isometric_toZ_pull k X Y p q (p ≫ spMap (Int.castRingHom k))
    (π ≫ p ≫ spMap (Int.castRingHom k)) π hπ rfl L hc hc'
  obtain ⟨h', hh', hv⟩ := GlobalTheory.HermLB.Isometric.isSelfInter htY iso.symm key
  exact ⟨h', (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k Y q _ e hq (L.pull π hπ) hc' h').mp hh', hv⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArFun_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ),
    IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (hL : ∀ i τ, (wZ (L i) t τ).IsCInf)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun (fun i => toZ (L i) t (hL i)) D Φ ↔ IsArFun L D Φ := by
  intro k _ X _ p t D hX ι _ L hL Φ
  have : Module.Finite ℤ k := hX.finite
  have H : ∀ (M : HermLB p) (τ : ℤ →+* ℂ), (wZ M t τ).IsCInf := fun M τ => _root_.GlobalTheory.CompanionTheory.Ar.BaseZ.wZ_isCInf k X p t M τ
  have hZ : IsArithVar t D := isArithVar_int k X p t D hX
  have key : ∀ (n : ι → ℤ) (a : ℝ),
      (comb (fun i => toZ (L i) t (hL i)) n).IsSelfInter a ↔ (comb L n).IsSelfInter a := by
    intro n a
    have e : (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (hL i)) n) :=
      (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.toZ_pow_comb k X p t H).2 ι L n
    constructor
    · intro h₀
      obtain ⟨h, h₁, h₂⟩ := e.symm.isSelfInter hZ h₀
      exact ⟨h, (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p t D hX (comb L n) (H _) h).1 h₁, h₂⟩
    · rintro ⟨h, h₁, h₂⟩
      exact e.isSelfInter hZ ⟨h, (_root_.GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff k X p t D hX (comb L n) (H _) h).2 h₁, h₂⟩
  exact ⟨fun h => ⟨fun n => (key n _).1 (h.1 n), h.2⟩, fun h => ⟨fun n => (key n _).2 (h.1 n), h.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

