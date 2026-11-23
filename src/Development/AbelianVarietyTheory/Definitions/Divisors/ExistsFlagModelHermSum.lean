module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

structure IsRegSurf (p : X ⟶ Sp k) : Prop extends IsArithVar p 1 where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

structure RegCover (p : X ⟶ Sp k) [IsIntegral X] where

  Y : Scheme.{0}

  ρ : Y ⟶ X

  reg : IsRegSurf (ρ ≫ p)

  generic : haveI := reg.isIntegral; ρ (genericPoint Y) = genericPoint X

  finite : haveI := reg.isIntegral; ρ.residueDegree (genericPoint Y) ≠ 0

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

end RegCover

namespace HermLB

variable [IsIntegral X] [IsLocallyNoetherian X] (L M : HermLB p)

variable {L M}

end HermLB

section Sum

variable {E₁ E₂ : X.Modules} {r s : ℕ}

end Sum

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}




end VMetric





def sqMap {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
  pullback.map A'.hom A'.hom A.hom A.hom φ φ f w.symm w.symm

structure PPAS (S : Scheme.{0}) where

  A : Over S

  [grp : GrpObj A]

  isAb : IsAbelianScheme A

  g : ℕ

  smoothDim : SmoothOfRelativeDimension g A.hom

  c : Pic (A ⊗ A).left

  isPol : IsPrincipalPol A c

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

def ofPolAV (Q : Out.PolAV S) : PPAS S where
  A := Q.A
  isAb := Q.isAb
  g := Q.g
  smoothDim := Q.smoothDim
  c := _
  isPol := IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV Q

structure RiemannData (y : Sp ℂ ⟶ S) where

  B : Over (Sp ℂ)

  [grp : GrpObj B]

  φ : B.left ⟶ P.A.left

  isPull : IsGrpPullback B P.A y φ

  L : LB B.left

  isLB : L.IsLB

  pol : CechPic.pull (sqMap isPull.1.w) P.c = lam (cls L isLB) (fst B B) (snd B B)

  u : HolUnif B L P.g

  H : Matrix (Fin P.g) (Fin P.g) ℂ

  χ : u.Λ → ℂ

  isAH : u.IsAH H χ

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

end RiemannData

theorem pull_sqMap_lam {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : Pic A.left) :
    CechPic.pull (sqMap h.1.w) (lam c (fst A A) (snd A A)) =
      lam (CechPic.pull φ c) (fst A' A') (snd A' A') := by
  let m : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A ⊗ A := Over.homMk (sqMap h.1.w) (by
    change sqMap h.1.w ≫ pullback.fst _ _ ≫ A.hom = (pullback.fst _ _ ≫ A'.hom) ≫ f
    rw [sqMap, pullback.lift_fst_assoc, Category.assoc, Category.assoc, h.1.w])
  rw [CechPic.lam_pull_of_isGrpPullback h]
  refine (CechPic.pull_lam m c _ _).trans ?_
  congr 1 <;> refine Over.OverMorphism.ext ?_
  exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]

theorem nonempty_riemannData (Q : Out.PolAV S) (y : Sp ℂ ⟶ S) :
    Nonempty ((ofPolAV Q).RiemannData y) := by
  have h := isGrpPullback_pullback Q.A y
  have hL := pull_isLB Q.isLB (pullback.fst Q.A.hom y)
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj Q.A,
    PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h, Q.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim, _, hL,
    PolBaseChange.rigidified_pull h Q.rigid, PolBaseChange.sym_pull h Q.sym,
    relAmple_pull h.1 Q.isLB hL ((isGen_iff w).1 hw) U hU
      (fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]) Q.ample,
    kTriv_pull h Q.isLB hL ((isGen_iff w).1 hw) Q.ktriv⟩
  obtain ⟨rig, hr⟩ := Q'.rigid
  obtain ⟨u, H, χ, -, hH, -⟩ := thetaUnifAV_all Q' rig hr
  exact ⟨⟨Q'.A, _, h, Q'.L, hL, (pull_sqMap_lam h _).trans
    (congrArg (lam · _ _) (CechPic.cls_pull Q.isLB _ hL).symm), u, H, χ, hH⟩⟩

variable (P : PPAS X)

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

variable (P p) [IsIntegral X]


variable {P p} {a b : ℝ}

end PPAS

end GlobalTheory
