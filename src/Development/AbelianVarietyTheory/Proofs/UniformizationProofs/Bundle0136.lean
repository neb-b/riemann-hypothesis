module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0126
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUBalanced
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem allU_balanced : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Balanced U := by
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  intro R _ _ _ I hI D A G _ _ hG U
  exact ⟨GlobalTheory.RingActData.exists_oAct GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U,
    GlobalTheory.PsiPrim.traceFormTwistIso_of_primitive_lineBundle GlobalTheory.firstFiveLaws h1 h2 h3 h4 R I hI D A G hG U⟩

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem torsion_clause :
    AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Torsion U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ k hk
  obtain ⟨f, hf⟩ := exists_tors_closed R I hI D A G hG U F k hk
  refine ⟨f, hf, fun p => ?_⟩
  obtain ⟨w, hw⟩ := U.toUnifPre.ext
  exact ((hf.1 p (f p)).2 rfl w hw).1

end GlobalTheory.TorsionIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem torsionIso_of_pelUnif : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  intro hL h1 h2 h3 h4 E _ _ _ H R _ _ _ I hI t P F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f, hf⟩ := _root_.GlobalTheory.TorsionIso.torsion_eq hL R I hI P.D P.A t.G t.semi P.U F k hk
  have hadj : ∀ a : NumberField.RingOfIntegers E,
      LBIso (cubeLB t.G ![fst t.G t.G ≫ t.act.toRingAct.act a, snd t.G t.G] P.U.LG.L)
        (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.toRingAct.act (star a)] P.U.LG.L) := by
    intro a
    rw [P.bundle]
    exact t.adj a
  have hlin := _root_.GlobalTheory.UT.OLinTors.main hL h1 h2 h3 h4 R I hI P.D P.A t.G t.semi P.U F
    (NumberField.RingOfIntegers E) P.oD P.oA t.act.toRingAct P.lin hadj k hk f hf
  exact ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hlin, hf.2.2.2.2⟩
end GlobalTheory.UT
end

