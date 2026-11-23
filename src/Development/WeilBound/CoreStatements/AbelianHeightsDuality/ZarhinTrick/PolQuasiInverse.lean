module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}}

def prj (G : Over S) : Fin 4 → (G4 G ⟶ G)
  | 0 => fst _ _
  | 1 => snd _ _ ≫ fst _ _
  | 2 => snd _ _ ≫ snd _ _ ≫ fst _ _
  | 3 => snd _ _ ≫ snd _ _ ≫ snd _ _

variable {A B : Over S} [GrpObj A] [GrpObj B]

def zcPair {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ)
    {Y : Over S} (u u' : Y ⟶ G4 (A ⊗ B)) : Pic Y.left :=
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ i ≫ fst A B ≫ lm)) +
  (∑ i, ∑ j, α i j • (evc hP (u ≫ prj _ i ≫ fst A B) (u' ≫ prj _ j ≫ snd A B) +
      evc hP (u' ≫ prj _ i ≫ fst A B) (u ≫ prj _ j ≫ snd A B))) +
  (∑ i, 2 • evc hP (u ≫ prj _ i ≫ snd A B ≫ mu) (u' ≫ prj _ i ≫ snd A B ≫ mu ≫ lm))

def zc {P : LB (A ⊗ B).left} (hP : P.IsLB) (lm : A ⟶ B) (mu : B ⟶ A) (α : Matrix (Fin 4) (Fin 4) ℤ) :
    Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left :=
  zcPair hP lm mu α (fst _ _) (snd _ _)

end PositivityTheory.PrwZar
