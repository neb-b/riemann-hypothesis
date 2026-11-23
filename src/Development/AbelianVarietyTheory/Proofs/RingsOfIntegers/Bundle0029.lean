module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionCommutesPullbackCmEndoFourLeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_commutes_pullback_cmEndo_four_le : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ k : ℕ, 4 ≤ k → ∀ (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k), P.U.Expands k s F → ∀ s' : P.U.SecK (k * N), IsPullByEnd P.U (t.act.act a) k N s s' → ∃ F' : Fam P.D.toPre (FractionRing V) (k * N), P.U.Expands (k * N) s' F' ∧ PullAl P.D (FractionRing V) P.oD a k N F F' := by
  first | exact @GlobalTheory.PullExpansion.expands_pull_of_four_le | exact GlobalTheory.PullExpansion.expands_pull_of_four_le | (intros; apply GlobalTheory.PullExpansion.expands_pull_of_four_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsMore
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PelUnifPowerDvr

theorem main : Laws → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (j : ℕ), ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P' : Geo.Tor.PELUnif (maximalIdeal V) t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hL hT V _ _ _ E _ _ _ H t P j
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ P.A j
  exact GlobalTheory.exists_pelUnif_pow hL.globalFns V _ E H t P j
    (GlobalTheory.UnifPower.main hL (GlobalTheory.UnitBallFree.main hL.globalFns hT) V)
    (GlobalTheory.PowDegData.main hL.globalFns V _ P.D j) ⟨A', ⟨pA⟩⟩

end GlobalTheory.PelUnifPowerDvr
end

