module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPoints
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend


open GlobalTheory.SqDescend in
theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfLocalAffineCover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.AmpleOverBase
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LBGerm
variable {X Y : Scheme.{0}}

theorem gm_val_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (f.stalkMap y).hom (gm (𝟙 X) (f y) U a).val := by
  rw [← gs_unit f y U h, ← gs_unit (𝟙 X) (f y) U h]
  exact gs_stalkMap f y U h a.val

theorem isUnit_gs_id_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) (f y) U a) ↔ IsUnit (gs f y U a) := by
  rw [isUnit_gs_iff (𝟙 X) (f y) U h, isUnit_gs_iff f y U h]
  rfl

theorem stalkMap_injective (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) : Function.Injective (f.stalkMap y).hom :=
  (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem exists_push {L : LB X} (f : Y ⟶ X) [IsOpenImmersion f] (V : X.Opens) (hV : V = f.opensRange) {n : ℕ}
    (t : (lbPow (L.pull f) n).Sec) :
    ∃ T : ∀ J : PUnit → L.ι, Γ(X, V ⊓ powChart L J), T ∈ secOn (lbPow L n) V ∧
      ∀ (y : Y) (J : PUnit → L.ι), f y ∈ powChart L J →
        (IsUnit (gs (𝟙 X) (f y) _ (T J)) ↔ y ∈ nonzeroLocus t) := by
  let J' : (PUnit → L.ι) → PUnit → PUnit → L.ι := fun J _ _ => J PUnit.unit
  have hm : ∀ (y : Y) (J : PUnit → L.ι), y ∈ powChart (L.pull f) (J' J) ↔ f y ∈ powChart L J := fun y J =>
    mem_powChart.trans (mem_pull.trans mem_powChart.symm)
  have e : ∀ J, powChart (L.pull f) (J' J) ≤ f ⁻¹ᵁ (V ⊓ powChart L J) := fun J y hy =>
    ⟨hV ▸ ⟨y, rfl⟩, (hm y J).1 hy⟩
  have e' : ∀ J, f ⁻¹ᵁ (V ⊓ powChart L J) ≤ powChart (L.pull f) (J' J) := fun J y hy => (hm y J).2 hy.2
  choose T hT using fun J =>
    (bijective_appLE f (V ⊓ powChart L J) (inf_le_left.trans hV.le) _ (e J) (e' J)).2 (powFn t (J' J))
  have key : ∀ (y : Y) (J : PUnit → L.ι) (hJ : f y ∈ powChart L J),
      gs f y _ (T J) = gs (𝟙 Y) y _ (powFn t (J' J)) := fun y J hJ => by
    rw [← hT J, gs_appLE f _ _ (e J) (𝟙 Y) y ((hm y J).2 hJ), Category.id_comp]
  refine ⟨T, mem_secOn_of_germ (M := lbPow L n) (V := V) T fun x J K hx hJ hK => ?_, fun y J hJ => ?_⟩
  · obtain ⟨y, rfl⟩ : ∃ y, f y = x := by
      have : x ∈ f.opensRange := hV ▸ hx
      exact this
    change gs (𝟙 X) (f y) (V ⊓ powChart L J) (T J) =
      (gm (𝟙 X) (f y) ((lbPow L n).U J ⊓ (lbPow L n).U K) ((lbPow L n).g J K)).val *
        gs (𝟙 X) (f y) (V ⊓ powChart L K) (T K)
    replace hJ : f y ∈ powChart L J := hJ
    replace hK : f y ∈ powChart L K := hK
    have hJ' := (hm y J).2 hJ
    have hK' := (hm y K).2 hK
    apply stalkMap_injective f y
    rw [map_mul, ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L J from ⟨hx, hJ⟩),
      ← gs_stalkMap f y _ (show f y ∈ V ⊓ powChart L K from ⟨hx, hK⟩), key y J hJ, key y K hK,
      gm_lbPow_g n (𝟙 X) (f y) J K hJ hK, Units.val_pow_eq_pow_val, map_pow,
      ← gm_val_stalkMap f y _ (show f y ∈ L.U (J PUnit.unit) ⊓ L.U (K PUnit.unit) from
        ⟨mem_powChart.1 hJ, mem_powChart.1 hK⟩),
      gs_powFn_compat t (𝟙 Y) y (J' J) (J' K) hJ' hK']
    have hJ'' : y ∈ (L.pull f).U (fun _ => J PUnit.unit) := mem_pull.2 (mem_powChart.1 hJ)
    have hK'' : y ∈ (L.pull f).U (fun _ => K PUnit.unit) := mem_pull.2 (mem_powChart.1 hK)
    rw [gm_pull_g L f (𝟙 Y) y _ _ hJ'' hK'', Category.id_comp]
  · rw [isUnit_gs_id_iff f y _ (show f y ∈ V ⊓ powChart L J from ⟨hV ▸ ⟨y, rfl⟩, hJ⟩), key y J hJ]
    exact (mem_nonzeroLocus_iff_powFn t ((hm y J).2 hJ)).symm

end GlobalTheory.AmpleOverBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem cechPic_sp_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing hL)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonicalTrivialOfRelativeAmple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KTrivSpread

namespace GlobalTheory.KTrivGenericPt

theorem spMap_eq_lift_comp_jK {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) :
    spMap ψ = spMap (IsFractionRing.lift (K := FractionRing R) hψ) ≫ Out.jK R := by
  rw [Out.jK, spMap, spMap, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem trivAlong_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {R : Type} [CommRing R] [IsDomain R]
    {g : Sp R ⟶ S} (h : TrivAlong A L (Out.jK R ≫ g)) {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ g) := by
  rw [spMap_eq_lift_comp_jK ψ hψ, Category.assoc]
  exact h.comp _

end GlobalTheory.KTrivGenericPt


open GlobalTheory.KTrivGenericPt in
theorem GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ _ t hP ha hpol
  haveI : IsProper t.G.hom := hP
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hgen : TrivAlong t.G t.PP.L (Out.jK R) :=
    trivAlong_of_kTriv (isGrpPullback_pullback t.G (Out.jK R)) t.PP.isLB hpol.2.2
  have hgen' : TrivAlong t.G t.PP.L (Out.jK R ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; exact hgen
  refine kTriv_of_primes hG R t.G hA t.PP.L t.PP.isLB ha fun p => ?_
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    letI := hf.toField
    have := trivAlong_field hgen' (algebraMap R O) hO
    rwa [Category.comp_id] at this
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩, ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · have key := trivAlong_dvr hG (𝟙 (Sp R)) hA t.PP t.cub ha V (spMap (ρ.comp (algebraMap R O))) ?_
      · rwa [Category.comp_id] at key
      · let F := AlgebraicClosure (FractionRing V)
        have H' := trivAlong_field hgen'
          ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
          ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
        have e : (Out.TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
            ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
          (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
        rw [← e, Category.assoc] at H'
        exact H'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorMemConeOfSmulCombination
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem cell_gen_mem_cone_of_smul : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (i : Fin m) (k : ℕ) (a : Fin m' → ℕ), IsCell bar φ δ → IsCell bar φ γ → 0 < k → k • δ i = ∑ j, a j • γ j →
    ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l := by
  intro O _ bar φ X _ _ _ m m' δ γ i k a hδ hγ hk he j hj
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hδ.strict

  have eδ : φ.evalZ (k • δ i) = k * φ.evalZ (δ i) := by
    have := hδ.linear (Pi.single i (k : ℝ)) fun l => by
      by_cases h : l = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp
  have eγ : φ.evalZ (∑ j, a j • γ j) = ∑ j, (a j : ℝ) * φ.evalZ (γ j) := by
    have := hγ.linear (fun j => (a j : ℝ)) fun j => by positivity
    rw [InvFun.evalZ]
    convert this using 2
    funext x y
    simp [LinearMap.sum_apply]
  have ℓδ : (ℓ (k • δ i) : ℝ) = k * (N * φ.evalZ (δ i)) := by
    rw [map_nsmul, ← h1 i, nsmul_eq_mul]; push_cast; rfl
  have ℓγ : (ℓ (∑ j, a j • γ j) : ℝ) = ∑ j, (a j : ℝ) * ℓ (γ j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; push_cast; simp [map_nsmul]
  have key : ∑ j, (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    have e1 : (ℓ (∑ j, a j • γ j) : ℝ) = N * φ.evalZ (∑ j, a j • γ j) := by
      rw [← he, ℓδ, eδ]; ring
    rw [ℓγ, eγ, Finset.mul_sum] at e1
    simp only [mul_sub, Finset.sum_sub_distrib, e1]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => by ring
  have nn : ∀ j ∈ Finset.univ, 0 ≤ (a j : ℝ) * ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) := fun j _ =>
    mul_nonneg (by positivity) (sub_nonneg.2 (h2 _ (hγ.mem j) (hγ.nonneg j)))
  have z := (Finset.sum_eq_zero_iff_of_nonneg nn).1 key j (Finset.mem_univ _)
  have ha : (a j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have heq : (N : ℝ) * φ.evalZ (γ j) = ℓ (γ j) := by
    have := (mul_eq_zero.1 z).resolve_left ha
    linarith
  exact h3 _ (hγ.mem j) (hγ.nonneg j) heq

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorsSmulMemOtherCellCone
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_smul_eq_sum_of_sum_toReal_eq {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ) (hδ : IsCell bar φ δ) (hγ : IsCell bar φ γ) (hc : ∀ j, 0 ≤ c j)
    (hs : ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j)) :
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict

  have hrel : ∑ i, (ℓ (δ i) : ℝ) = ∑ j, c j * (ℓ (γ j) : ℝ) := by
    have e := sum_mul_eq_zero_of_sum_toReal (X := X) (j := LinearMap.id) (fun _ _ h => h) ℓ
      (β := Sum.elim δ γ) (c := Sum.elim (fun _ => (1 : ℝ)) (fun j => -c j)) (by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, LinearMap.id_apply, one_smul, neg_smul, Finset.sum_neg_distrib, hs,
          add_neg_cancel])
    rw [Fintype.sum_sum_type] at e
    simp only [Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul, Finset.sum_neg_distrib] at e
    linarith

  have hlinγ := (linearOn_iff φ γ).1 hγ.linear c hc
  have hlinδ := (linearOn_iff φ δ).1 hδ.linear (fun _ => 1) (fun _ => zero_le_one)
  simp only [one_smul, one_mul] at hlinδ
  rw [hs, hlinγ] at hlinδ

  have hsum : ∑ i, ((ℓ (δ i) : ℝ) - N * φ.evalZ (δ i)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hlinδ, hrel, Finset.mul_sum]
    simp only [h1]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun j _ => by ring
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (ℓ (δ i) : ℝ) - N * φ.evalZ (δ i) := fun i _ =>
    sub_nonneg.2 (h2 _ (hδ.mem i) (hδ.nonneg i))
  intro i
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  exact h3 _ (hδ.mem i) (hδ.nonneg i) (by linarith)

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartRingFormallyUnramified
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan

theorem formallyUnramified_residue_comp_of_isEtaleCompletion :
    ∀ (k : Type) [Field k] (m e : ℕ) [CharZero (ChartRing k m e)] {A : Type} [CommRing A] [IsLocalRing A]
      (φ : A →+* ChartRing k m e), IsEtaleCompletion φ → ((residue (ChartRing k m e)).comp φ).FormallyUnramified := by
  intro k _ m e _ A _ _ φ hφ
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    constructor
    intro a ha
    by_contra hna
    have h1 : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have h2 : φ a ∈ maximalIdeal (ChartRing k m e) := hmax ▸ Ideal.mem_map_of_mem φ h1
    exact (mem_maximalIdeal _).1 h2 ha
  rw [← ResidueField.map_comp_residue]
  refine RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) ?_
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  haveI : CharZero k := RingHom.charZero (algebraMap k (ChartRing k m e))
  haveI : CharZero (ResidueField (ChartRing k m e)) :=
    (RingHom.charZero_iff ((residue (ChartRing k m e)).comp (algebraMap k (ChartRing k m e))).injective).1 inferInstance
  haveI : CharZero (ResidueField A) := RingHom.charZero (ResidueField.map φ)
  letI := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField (ChartRing k m e)) := hfin'
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField (ChartRing k m e)) := inferInstance
  exact Algebra.FormallyUnramified.of_isSeparable _ _

end GlobalTheory.GenFan
end

