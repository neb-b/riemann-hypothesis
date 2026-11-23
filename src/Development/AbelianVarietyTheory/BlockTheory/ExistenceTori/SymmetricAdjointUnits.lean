module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle0001

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

section Gen

variable {X Y : Scheme.{0}} (L : LB X)

end Gen

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

section Group

variable (G : Over X₀) [GrpObj G] [IsCommMonObj G]

variable (x : Sp S ⟶ X₀) {d : ℕ}


omit [GrpObj G] [IsCommMonObj G] in
def jPt (j : JetPts G x d) (n m : ℕ) (k : Fin n) : algO x (Jet S (Fin n × Fin d) m) ⟶ G :=
  algMap x (jetIn k) ≫ j m

abbrev FrameFam (L : LB G.left) (j : JetPts G x d) : Type :=
  ∀ m : ℕ, LB.Gen (cubeLB G (jPt G x j 2 m) L)

variable {G x}

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws
