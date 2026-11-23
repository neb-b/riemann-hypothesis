module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiCompEndomorphismEqPowOfPullbackIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_comp_endomorphism_eq_pow_of_pullback_iso : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → Function.Injective E.h → ∀ ν : ℕ, 1 ≤ ν → (∀ y, E.h (E'.h y) = ν • y) → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(ν : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen) → ∀ κ : LB.Gen (kapLB D.toPre E.aB ν 1), Normd κ → ∀ y (z : (TK R).left) J, Good D.toPre.P.L z J → val (D.toPre.psi (E'.h y)) (𝟙 _) z J * rigV D.toPre (TK R).hom z J = val (D.toPre.psi y) (𝟙 _) z J ^ ν * val κ (D.toPre.xK y) z J * rigV D.toPre (TK R).hom z J ^ ν := by
  first | exact @GlobalTheory.UT.PsiPull.psi_pull | exact GlobalTheory.UT.PsiPull.psi_pull | (intros; apply GlobalTheory.UT.PsiPull.psi_pull <;> assumption)
