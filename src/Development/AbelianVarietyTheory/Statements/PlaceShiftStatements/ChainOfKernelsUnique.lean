module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel

def QuotGlobal : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (H : Over S) [GrpObj H] (i : H ⟶ A),
    IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom →
    ∃ (B : Over S) (_ : GrpObj B) (q : A ⟶ B), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧
      Flat q.left ∧ Surjective q.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q

def InSub {S : Scheme.{0}} {A K T : Over S} (i : K ⟶ A) (x : T ⟶ A) : Prop :=
  ∃ y : T ⟶ K, y ≫ i = x

end GlobalTheory.IwLevel
