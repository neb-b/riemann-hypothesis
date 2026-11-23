module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecialization
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsIncl

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOpenGeometricallyConnectedFibers
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isOpen_geometricallyConnected_fibres :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      IsOpen {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hs hp
  have hgen := _root_.GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre k G.left G.hom (η[G]).left (Over.w η[G]) hs hp
  have hspec := _root_.GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected k G hs hp
  exact GlobalTheory.T.isOpen_of_stable_under_generalization_specialization k _ hgen hspec

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionTwo
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem btOrder_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (n : ℕ), (∀ g : LevGrp La p n → O, g ∈ (X.Γ n).btOrder ⊤ ↔ ∃ f ∈ (X.Γ (n + 1)).btOrder ⊤, ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) ∧ ∀ f : (X.Γ (n + 1)).btOrder ⊤, (∀ a : La, f.1 (lev p (n + 1) (p • a)) = 0) → f ∈ Ideal.span {g : (X.Γ (n + 1)).btOrder ⊤ | ∃ h ∈ (X.Γ (n + 1)).btOrder ⊤, ∀ t, g.1 t = h (t ^ p ^ n) - h 1} :=
  @PositivityTheory.HtPt.Gi.tw_res

end GlobalTheory.CompanionTheory.Ar.HT
end

