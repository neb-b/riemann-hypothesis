module

public import Mathlib
public import Formalism.LocalRingCardinality.DataDIV
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.VB

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase

section Surface

variable (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)]

def IsProjSurface : Prop :=
  IsIntegral T ∧ topologicalKrullDim T = 2 ∧ IsProjOver (strHom k (X := T))

variable {T}

def degCh2 (E : T.Modules) (r : ℕ) : ℚ :=
  ((chi k E + chi k (VB.dual E) - 2 * r * chi k (structureModule T) : ℤ) : ℚ) / 2

variable {k}

end Surface

section Abelian

variable {S S' : Scheme.{0}} (A : Over S)

def toBase (s : S' ⟶ S) {Y : Over S'} (x : Y ⟶ (Over.pullback s).obj A) :
    Over.mk (Y.hom ≫ s) ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom s) (by
    have := Over.w x
    simp only [Over.mk_hom, Category.assoc, pullback.condition]
    rw [← this]; simp)

def sqToBase (s : S' ⟶ S) :
    ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).left ⟶ (A ⊗ A).left :=
  (lift (toBase A s (fst _ _)) (toBase A s (snd _ _))).left

variable [GrpObj A]

def IsPrincipalPol (c : Pic (A ⊗ A).left) : Prop :=
  pull (lift (1 : A ⟶ A) (𝟙 A)).left c = 0 ∧ pull (lift (𝟙 A) (1 : A ⟶ A)).left c = 0 ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S),
      ∃ (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB),
        Out.RelAmple ((Over.pullback s).obj A) L ∧ Out.KTriv ((Over.pullback s).obj A) L ∧
          pull (sqToBase A s) c = lam (cls L hL) (fst _ _) (snd _ _)

theorem isPrincipalPol_of_polAV (P : Out.PolAV S) :
    IsPrincipalPol P.A (lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A)) := by
  have := P.isAb.comm
  refine ⟨?_, ?_, fun Ω _ _ s => ?_⟩
  · rw [pull_lam, lift_fst, lam_one_left]
  · rw [pull_lam, lift_snd, lam_one_right]
  · have h := isGrpPullback_pullback P.A s
    have hL := pull_isLB P.isLB (pullback.fst P.A.hom s)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL hL).1 rfl
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
      (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
    refine ⟨_, hL, relAmple_pull h.1 P.isLB hL ((isGen_iff w).1 hw) U hU
      (fun y => by rwa [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]) P.ample,
      kTriv_pull h P.isLB hL ((isGen_iff w).1 hw) P.ktriv, ?_⟩
    rw [sqToBase, pull_lam, lift_fst, lift_snd, cls_pull P.isLB, lam_pull_of_isGrpPullback h]
    rfl

end Abelian

open Formalism.BasicNotions

end GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase
