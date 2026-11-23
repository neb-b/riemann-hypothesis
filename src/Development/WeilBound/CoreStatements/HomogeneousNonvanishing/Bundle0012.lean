module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0007
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtHopf
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.UnitarySelfGeneration

theorem bt_sub_eq_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ :=
  PositivityTheory.HtPt.Htat.bt_sub_eq_top_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

theorem bt_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  PositivityTheory.HtPt.Htat.bt_hopf_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

end PositivityTheory.UnitarySelfGeneration
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HtExists
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.UnitarySelfGeneration

theorem ht_char_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) :=
  PositivityTheory.HtPt.Htat.ht_char_section_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

theorem ht_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ), ∃ w : Module.Dual R L, Γ.IsHT i M N χ w :=
  PositivityTheory.HtPt.Htat.ht_exists_of PositivityTheory.HtPt.Htat.hens_normal PositivityTheory.UnitarySelfGeneration.bt_exists_bc PositivityTheory.HtPt.Htat.reg_pull

end PositivityTheory.UnitarySelfGeneration
end

