module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory GlobalTheory.AV GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo

namespace GlobalTheory.DrinLev.HT.MulModel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}

theorem comp_pow' {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem pow_comp' {S : Scheme.{0}} {G G' Z : Over S} [MonObj G] [MonObj G'] (φ : G ⟶ G')
    [IsMonHom φ] (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom (𝟙 A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift (𝟙 A ^ n) (𝟙 A) ≫ μ[A]))

variable {G : HTGroup p} (L : Link D G)

end GlobalTheory.DrinLev.HT.MulModel
