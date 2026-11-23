module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj

def ringActOf {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    (a : Geo.Tor.OAct O G) : RingAct G O where
  act := a.act
  hom := a.hom
  map_one := a.one
  map_mul := fun x y => by rw [_root_.mul_comm x y]; exact a.mul y x
  map_add := fun x y => a.add x y

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]

structure OData (H : Host E) (I : Ideal R) where

  D : DegData R I

  [mod : Module (𝓞 E) D.toPre.X]

  ac : letI := hostStar H; D.OAct (𝓞 E)
  through : PsiThroughHost H ac

attribute [instance] OData.mod

variable {H : Host E} {I : Ideal R}

structure OUnif (t : SAB H (Spec (CommRingCat.of R))) (Δ : OData H I) where

  A : PolAV (Spec (CommRingCat.of (FractionRing R)))

  actA : letI := hostStar H; A.OAct (𝓞 E)

  U : Unif I Δ.D A t.G
  LG_eq : U.LG = t.PP
  cub_eq : HEq U.cubG t.cub
  lin : letI := hostStar H; U.toUnifPre.OLinear (𝓞 E) Δ.ac actA (ringActOf t.act)

section Points

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

namespace OUnif

variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

end OUnif

end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
