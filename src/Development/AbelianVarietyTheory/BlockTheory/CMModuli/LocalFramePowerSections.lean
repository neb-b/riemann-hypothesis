module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections

abbrev PowSec {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (N : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (N : ℤ)))

def IsTrait {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W)
    (κ : FractionRing R₁ →+* FractionRing W) : Prop :=
  GlobalTheory.UU.CDVR W ∧ κ.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap W (FractionRing W)).comp ρ

section Frames

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G)


end Frames

section Data

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  (Xo : Moduli D l) {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end Data

end GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
end
