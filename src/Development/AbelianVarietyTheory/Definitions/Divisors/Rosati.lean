module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure Pre (b : Base D R) (s : S ⟶ Sp R) where
  A : Over S
  [grp : GrpObj A]
  [comm : IsCommMonObj A]
  ab : IsAbelianScheme A
  act : OActN D.O A
  P : LB (G2 A).left
  isLB : P.IsLB
  rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen
  rig₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen
  symm : LBIso P (P.pull (lift (snd A A) (fst A A)).left)
  ample : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left)
  kerP : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A),
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1
  rosati : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
    (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)

attribute [instance] Pre.grp Pre.comm

end GlobalTheory.UPel.HT
