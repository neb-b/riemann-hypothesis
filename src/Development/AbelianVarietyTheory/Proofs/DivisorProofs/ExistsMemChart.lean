module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.LB (toMod)
open Limits (pullback)

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}


variable (p) in
def ratFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))

namespace ratFibre

variable (p)

def fst : ratFibre p ⟶ X := pullback.fst _ _

def snd : ratFibre p ⟶ Sp ℚ := pullback.snd _ _

instance algebra : Algebra ℚ Γ(ratFibre p, ⊤) := algebraΓOfHom (snd p)

theorem isPullback : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom ℚ)) := IsPullback.of_hasPullback _ _

theorem strHom_eq : strHom ℚ (ratFibre p) = snd p := GlobalTheory.strHom_eq fun _ => rfl

end ratFibre


variable (p) in
def ratDeg (L : LB X) : ℤ := degOfRank ℚ (toMod (L.pull (ratFibre.fst p))) 1

abbrev CxPts.pt (y : CxPts p σ) : X := y.1 (IsLocalRing.closedPoint ℂ)

def germOrd {W : X.Opens} (f : Γ(X, W)) {x : X} (hx : x ∈ W) : ℕ :=
  (Ring.ord (X.presheaf.stalk x) (X.presheaf.germ W x hx f)).toNat

theorem exists_mem_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i :=
  Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))

def secOrd {L : LB X} (hL : L.IsLB) (s : L.Sec) (x : X) : ℕ :=
  germOrd (s.f (exists_mem_chart hL x).choose) (exists_mem_chart hL x).choose_spec

end GlobalTheory
