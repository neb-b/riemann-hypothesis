module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Generic

variable {R : Type} [CommRing R] [IsDomain R]

def OverGen (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Over (Sp R)) (x : Sp F ⟶ T.left) : Prop :=
  x ≫ T.hom = jFK (R := R) F ≫ jK R

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

def IsImage (P : PELUnif I t) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (q : QkPt P.D.toPre F k)
    (v : Sp F ⟶ t.G.left) : Prop :=
  ∃ a : TFK (R := R) F ⟶ P.A.A, a.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = v ∧ P.ToA F k q a

def AllFlat (p : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) {W : (Sp R).Opens},
    PsiOn P.D.toPre W → ℕ → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [CharZero R], AdmBase R (maximalIdeal R) → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : (Sp R).Opens),
    (W : Set (Sp R)).Nonempty → IsProper (t.G.hom ∣_ W) → ∀ (ψW : PsiOn P.D.toPre W) (k : ℕ), 1 ≤ k → p P ψW k

end GlobalTheory.FlatTors
