module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def Form.toAf {G : HTGroup p} (P : Form G) : grp G P.β →* G.GAf :=
  toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec

abbrev Form.Pts {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (Kf : Subgroup G.GAf)
    (K' : Subgroup (Gr G 1)) : Type :=
  GlobalTheory.LKCx.Pts G v P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf K'

abbrev Form.Stab {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (Kf : Subgroup G.GAf)
    (K' : Subgroup (Gr G 1)) (a : Dat G v P.β) : Type :=
  GlobalTheory.LKCx.Stab G v P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf K' a

abbrev AllPts (G : HTGroup p) (v : InfinitePlace G.F) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  Σ q : FCls G, Form.Pts v (Quot.out q) Kf K'

end GlobalTheory.LKCx
