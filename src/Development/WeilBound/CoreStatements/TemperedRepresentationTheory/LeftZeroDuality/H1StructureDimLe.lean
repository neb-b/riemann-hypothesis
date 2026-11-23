module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.ObstructionTrivialLocus

def H1StructureDimLe : Prop :=
  ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    Module.Finite k (GlobalTheory.CechDR.HO1 A.hom) ∧ Module.finrank k (GlobalTheory.CechDR.HO1 A.hom) ≤ g

def IsTrivLocus {S : Scheme.{0}} (A : Over S) {Y Z : Over S} (N : LB (A ⊗ Y).left) (i : Z ⟶ Y) : Prop :=
  IsClosedImmersion i.left ∧
    ∀ (T : Over S) (y : T ⟶ Y), Triv (ev N (fst A T) (snd A T ≫ y)) ↔ ∃ z : T ⟶ Z, z ≫ i = y

def TrivLocus : Prop :=
  ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → IsLocallyNoetherian Y.left →
    ∀ N : LB (A ⊗ Y).left, N.IsLB → Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∃ (Z : Over S) (i : Z ⟶ Y), IsTrivLocus A N i

def LeftFinite {S : Scheme.{0}} (A B : Over S) (P : LB (A ⊗ B).left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
    Set.Finite {x : Over.mk t ⟶ A | Triv (ev P (fst (Over.mk t) B ≫ x) (snd (Over.mk t) B))}

def KFinite : Prop :=
  ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L →
    LeftFinite A A (abelian₂ A L)

end PositivityTheory.ObstructionTrivialLocus
