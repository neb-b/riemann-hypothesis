module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsGrpObjIsAddLawHom
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)

variable [W.IsElliptic]

theorem appLE_originSec_eq_zero_iff_eSec (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left)
    (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
      t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := by
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact appLE_originSec_eq_zero_iff W t i h

theorem rigidified_originLB : Out.Rigidified (schemeOver W) (originLB W) := by
  unfold Out.Rigidified
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact ⟨_, isGen_one_pull_zero W⟩

theorem sym_originLB : Out.Sym (schemeOver W) (originLB W) := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  have : IsIso (GrpObj.inv : schemeOver W ⟶ schemeOver W).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : schemeOver W ⟶ schemeOver W)))
  have hreg := fun i V h => ((isRegularSec_originSec W i).resG (V := V) h).mem
  refine SameZeroScheme.exists_isGen_linComb (schemeOver W).left _ (originLB W) (originSec W) _ _
    (originLB_isLB W)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [appLE_originSec_eq_zero_iff_eSec, appLE_originSec_eq_zero_iff_eSec, ← Category.assoc t]
  exact SymOfZeroDivisor.inv_eq_zero_iff (schemeOver W) _

theorem kTriv_originLB : Out.KTriv (schemeOver W) (originLB W) := by
  refine kTriv_of_sections_vanish_on_zero _ (schemeOver W) (originLB W) (originSec W)
    (originLB_isLB W) (appLE_originSec_eq_zero_iff_eSec W) ?_
  intro R' _ f Y φ q H s T t j h e
  rw [show eSec (schemeOver W) = zero W from one_left W] at e
  exact appLE_sec_pull_originLB_eq_zero W H s t j h e

def ellPolAV : Out.PolAV (Spec (CommRingCat.of R)) where
  A := schemeOver W
  grp := grpObj W
  isAb := isAbelianScheme_schemeOver R W W.isUnit_Δ (isCommMonObj W)
  g := 1
  smoothDim := smoothOfRelativeDimension_toSpec_of_isUnit W W.isUnit_Δ
  L := originLB W
  isLB := originLB_isLB W
  rigid := rigidified_originLB W
  sym := sym_originLB W
  ample := relAmple_originLB W
  ktriv := kTriv_originLB W

@[simp] theorem ellPolAV_g : (ellPolAV W).g = 1 := rfl

theorem eSec_ellPolAV : eSec (ellPolAV W).A = zero W := one_left W

def ellTheta : (ellPolAV W).L.Sec := originSec W

theorem exists_isLieBasis_ellPolAV : ∃ v : epsR R ⟶ (ellPolAV W).A,
    (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
      v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
    IsLieBasis ![v] :=
  WeierstrassLie.isLieBasis_eps R W (one_left W)

section BaseChange

variable {R' : Type} [CommRing R'] {W' : _root_.WeierstrassCurve R'} [W'.IsElliptic]
  (f : R →+* R') (h : W.map f = W')

theorem isGrpPullback_ellPolAV :
    IsGrpPullback (ellPolAV W').A (ellPolAV W).A (spMap f) (mapHom W f h) :=
  isGrpPullback_mapHom W f h

theorem lbIso_ellPolAV : LBIso (ellPolAV W').L ((ellPolAV W).L.pull (mapHom W f h)) :=
  lbIso_pull_originLB W f h

end BaseChange

theorem not_isGen_ellPolAV [Nontrivial R] (t : (ellPolAV W).L.Gen) : ¬ t.IsGen :=
  not_isGen_originLB W t

theorem weierstrass_0_0_1_neg_one_0_isElliptic : (⟨0, 0, 1, -1, 0⟩ : _root_.WeierstrassCurve ℚ).IsElliptic :=
  ⟨by
    have : (⟨0, 0, 1, -1, 0⟩ : _root_.WeierstrassCurve ℚ).Δ = 37 := by
      norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
    rw [this]
    exact Ne.isUnit (by norm_num)⟩

end GlobalTheory.WeierstrassCurve
