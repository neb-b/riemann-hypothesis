module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapAllTuplesOverCoreOfRankBound
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapCore

theorem oneMapRowR_of_core_of_size :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → IoExt R → ∀ i, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → OneMapRowR T R κ v₀ O ph i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hn hC hoff hused hT hI i hP hph
  have hci : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := GlobalTheory.chartIndependence_unconditional
  have h0 : OneMapRow0 T R κ v₀ O i :=
    _root_.GlobalTheory.OneMapTies.oneMapRow0_of_ties_core hci D G Pl0 T0 A T R F κ v₀ hC (_root_.GlobalTheory.tieIn_of_nonempty_tie D G Pl0 T0 A T R κ v₀ hT) hI O i hP
  exact _root_.GlobalTheory.OneMapCore.oneMapRowR_of_core hci D G Pl0 T0 A T R F κ v₀ O ph hC hoff hused hT hI i hP hph
    (_root_.GlobalTheory.ClassSumSpanCore.classSumsSpan_core D G Pl0 T0 A T R F κ v₀ O hn hC hT hI i hP h0)

end GlobalTheory.OneMapCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFracFunctionFieldMapOfEssentiallyEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open IsLocalRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleKlt

theorem ord_functionFieldMap_of_formallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), (∀ x, functionFieldMap f x ∈ E'.ring → x ∈ E.ring) → ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → ((functionFieldMap f).restrict E.ring E'.ring h).EssFiniteType → ∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := by
  intro M W _ _ p f _ E E' h htr het hft g
  set φ := functionFieldMap f
  set ρ := φ.restrict E.ring E'.ring h
  letI := ρ.toAlgebra
  haveI : Algebra.FormallyEtale E.ring E'.ring := het
  haveI : Algebra.EssFiniteType E.ring E'.ring := hft
  haveI : IsLocalHom (algebraMap E.ring E'.ring) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have e : φ (x : W.functionField) * (y : M.functionField) = 1 := congrArg Subtype.val hy
    have hx0 : (x : W.functionField) ≠ 0 := by
      rintro h0
      rw [h0, map_zero, zero_mul] at e
      exact zero_ne_one e
    have hinv : φ ((x : W.functionField)⁻¹) = y := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right e
    have hmem : (x : W.functionField)⁻¹ ∈ E.ring := htr _ (hinv ▸ y.2)
    exact IsUnit.of_mul_eq_one (b := (⟨_, hmem⟩ : E.ring)) (Subtype.ext (mul_inv_cancel₀ hx0))
  have hm := Algebra.FormallyUnramified.map_maximalIdeal (R := E.ring) (S := E'.ring)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht' : Irreducible (ρ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  obtain ⟨m, u, e⟩ := exists_eq_unit_mul_zpow (F := W.functionField) ht g.ne_zero
  have h1 := ordTop_vw_unit_mul_zpow (F := W.functionField) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := M.functionField) ht' (Units.map ρ.toMonoidHom u) m
  rw [← e, ordTop_vw_of_ne_zero _ g.ne_zero, WithTop.coe_inj] at h1
  have e2 : ((Units.map φ.toMonoidHom g : M.functionFieldˣ) : M.functionField) =
      algebraMap E'.ring M.functionField (Units.map ρ.toMonoidHom u) *
        algebraMap E'.ring M.functionField (ρ t) ^ m := by
    rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, e, map_mul, map_zpow₀]
    rfl
  rw [← e2, ordTop_vw_of_ne_zero _ (Units.ne_zero _), WithTop.coe_inj] at h2
  exact h2.trans h1.symm

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverTensorIsPullbackOfIsPullbackSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem over_tensor_isPullback_of_isPullback {S S' : Scheme.{0}} (s : S' ⟶ S) (A B : Over S')
    (Y Z : Over S) (j : A.left ⟶ Y.left) (j' : B.left ⟶ Z.left)
    (h₁ : IsPullback j A.hom Y.hom s) (h₂ : IsPullback j' B.hom Z.hom s) :
    ∃ k : (A ⊗ B).left ⟶ (Y ⊗ Z).left, k ≫ (fst Y Z).left = (fst A B).left ≫ j ∧
      k ≫ (snd Y Z).left = (snd A B).left ≫ j' ∧ IsPullback k (A ⊗ B).hom (Y ⊗ Z).hom s := by
  let k : pullback A.hom B.hom ⟶ pullback Y.hom Z.hom :=
    pullback.map A.hom B.hom Y.hom Z.hom j j' s h₁.w.symm h₂.w.symm
  have kf : k ≫ pullback.fst Y.hom Z.hom = pullback.fst A.hom B.hom ≫ j := pullback.lift_fst _ _ _
  have ks : k ≫ pullback.snd Y.hom Z.hom = pullback.snd A.hom B.hom ≫ j' :=
    pullback.lift_snd _ _ _
  refine ⟨k, kf, ks, ?_⟩
  change IsPullback k (pullback.fst A.hom B.hom ≫ A.hom) (pullback.fst Y.hom Z.hom ≫ Y.hom) s
  have w : k ≫ pullback.fst Y.hom Z.hom ≫ Y.hom = (pullback.fst A.hom B.hom ≫ A.hom) ≫ s := by
    rw [← Category.assoc, kf, Category.assoc, h₁.w, Category.assoc]
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w ?lift ?fl ?fr ?uniq)
  case lift =>
    intro c
    have e₁ : (c.fst ≫ pullback.fst Y.hom Z.hom) ≫ Y.hom = c.snd ≫ s := by
      simpa using c.condition
    have e₂ : (c.fst ≫ pullback.snd Y.hom Z.hom) ≫ Z.hom = c.snd ≫ s := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]; exact e₁
    exact pullback.lift (h₁.lift _ _ e₁) (h₂.lift _ _ e₂) (by simp)
  case fl =>
    intro c
    apply pullback.hom_ext
    · rw [Category.assoc, kf, pullback.lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, ks, pullback.lift_snd_assoc, h₂.lift_fst]
  case fr =>
    intro c
    rw [pullback.lift_fst_assoc, h₁.lift_snd]
  case uniq =>
    intro c m hm hm'
    have hA : m ≫ pullback.fst A.hom B.hom ≫ A.hom = c.snd := hm'
    have hB : m ≫ pullback.snd A.hom B.hom ≫ B.hom = c.snd := by
      rw [← pullback.condition]; exact hA
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← kf, ← Category.assoc, hm]
      · rw [h₁.lift_snd, Category.assoc, hA]
    · rw [pullback.lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← ks, ← Category.assoc, hm]
      · rw [h₂.lift_snd, Category.assoc, hB]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PnPosOfGeneratesAt
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CombForm

section Atlas

variable {e : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']

def tAtlas (A : FinHolAtlas e X) (h : X ≃ₜ X') : FinHolAtlas e X' where
  n := A.n
  chart j := h.symm.transOpenPartialHomeomorph (A.chart j)
  cover x := (A.cover (h.symm x)).imp fun _ hj => hj
  holo j k := by
    have e₁ : (h.symm.transOpenPartialHomeomorph (A.chart k)) ∘ (h.symm.transOpenPartialHomeomorph (A.chart j)).symm =
        A.chart k ∘ (A.chart j).symm := funext fun y => by simp
    have e₂ : (h.symm.transOpenPartialHomeomorph (A.chart j)).target ∩
        (h.symm.transOpenPartialHomeomorph (A.chart j)).symm ⁻¹' (h.symm.transOpenPartialHomeomorph (A.chart k)).source =
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
      ext y; simp
    rw [e₁, e₂]
    exact A.holo j k

theorem tAtlas_symm (A : FinHolAtlas e X) (h : X ≃ₜ X') (j : Fin (tAtlas A h).n) (y : Fin e → ℂ) :
    ((tAtlas A h).chart j).symm y = h ((A.chart j).symm y) := rfl

end Atlas

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

section Met

variable {σ : F →+* ℂ} {Δ : Y.Dv}

end Met

end GlobalTheory.Mean4O.CombForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have pullIso : ∀ {X Y Z : Scheme.{0}} {M : LB Y} {N : LB X} {f : Y ⟶ X},
      LBIso M (N.pull f) → (g : Z ⟶ Y) → LBIso (M.pull g) (N.pull (g ≫ f)) := by
    intro X Y Z M N f H g
    exact H.chartPull (chartPullPull M g)
      (chartPullSame N (fun _ : PUnit => g ≫ f) (fun _ : PUnit => f) (fun _ => 1) g fun _ => rfl)
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), LBIso (ev P a b) (ev P₀ b (a ≫ l)) := by
    intro Y a b
    have hs := pullIso hsym (lift a b).left
    have hl' := pullIso hl (lift b a).left
    have es : LBIso (ev P a b) (ev P b a) := by
      simpa only [← Over.comp_left, comp_lift, lift_snd, lift_fst] using hs
    have el : LBIso (ev P b a) (ev P₀ b (a ≫ l)) := by
      simpa only [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc] using hl'
    exact (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).1
      (((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 es).trans
       ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 el))
  refine ⟨?_, fun T x hx => ?_⟩
  · have hs : LBIso (swap P₀) (swap P₀) := (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB hP₀ _)).1 rfl
    have hs' := pullIso hs (lift (fst A A ≫ l) (snd A A)).left
    have hs'' : LBIso (ev (swap P₀) (fst A A ≫ l) (snd A A)) (ev P₀ (snd A A) (fst A A ≫ l)) := by
      simpa only [swap, ev, ← Over.comp_left, comp_lift, lift_fst, lift_snd] using hs'
    apply (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1
    exact ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 (by simpa only [Category.comp_id] using key (A ⊗ A) (fst A A) (snd A A))).trans
      ((CechPic.cls_eq_iff (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₀ _)).2 hs'').symm
  · have hk := key (A ⊗ T) (snd A T ≫ x) (fst A T)
    simp only [Category.assoc, hx, MonObj.comp_one] at hk
    have ht : Triv (ev P₀ (fst A T) (1 : A ⊗ T ⟶ B)) := by
      obtain ⟨t, ht⟩ := hD.zero
      have h := DVR.pullGen_isGen _ _ _ t ht (fst A T).left
      simpa only [ev, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] using (show Triv _ from ⟨_, h⟩)
    exact (CechPic.iso_triv_iff _).1 ((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP _)).1
      (((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP₀ _)).2 ((CechPic.iso_triv_iff _).2 ht)).trans
        ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 hk).symm))

end GlobalTheory.AbDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.CxPts Topology Set

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem isRatSec_tens {A B : LB Z} {r : A.ι → Z.functionFieldˣ} {s : B.ι → Z.functionFieldˣ}
    (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem div_tens (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ} {s : N.B.ι → Z.functionFieldˣ}
    (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).div (isRatSec_tens hr hs) = M.div hr + N.div hs :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB z
    obtain ⟨b, hb⟩ := exists_chart N.isLB z
    exact ⟨_, (presents_divOfRatSec (M.tens N).isLB (isRatSec_tens hr hs)).isEqn (a, b) z ⟨ha, hb⟩,
      ((presents_divOfRatSec M.isLB hr).isEqn a z ha).add ((presents_divOfRatSec N.isLB hs).isEqn b z hb)⟩

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}

theorem curveDeg_tens [IsLocallyNoetherian Z] (hZ : IsArithVar q 0)
    (hc : CharZero (Z.residueField (genericPoint Z))) (M N : HermLB q) {r : M.B.ι → Z.functionFieldˣ}
    {s : N.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) (hs : IsRatSec N.B s) :
    (M.tens N).curveDeg (isRatSec_tens hr hs) = M.curveDeg hr + N.curveDeg hs := by
  have := hZ.isNoetherian
  have hfin (D : CartierDiv Z) : (Function.support fun z =>
      (D.mult z : ℝ) * Real.log (Nat.card (Z.residueField z))).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have h₂ (σ) (y : CxPts q σ) : logNorm ((M.tens N).φ σ) (fun c : M.B.ι × N.B.ι => r c.1 * s c.2) y =
      logNorm (M.φ σ) r y + logNorm (N.φ σ) s y := by
    have hy : under y = genericPoint Z := hZ.under_eq_genericPoint y
    have ho (D : CartierDiv Z) : y ∈ offSupp q σ D := mem_offSupp.2 (hy ▸ D.genericPoint_notMem_supp)
    have ha := mem_pick (M.φ σ).isLB y
    have hb := mem_pick (N.φ σ).isLB y
    have hu (g : Z.functionFieldˣ) : ‖ratVal (g : Z.functionField) y‖ ≠ 0 :=
      norm_ne_zero_iff.2 (ratVal_ne_zero (hy ▸ unitAt_genericPoint g.ne_zero))
    refine (logNorm_eq ((M.tens N).φ σ) (isRatSec_tens hr hs) (ho _) (i := (pick (M.φ σ).isLB y, pick (N.φ σ).isLB y))
      (mem_ptsIn_inf.2 ⟨ha, hb⟩)).trans ?_
    change Real.log ‖ratVal ((r (pick (M.φ σ).isLB y) * s (pick (N.φ σ).isLB y) : Z.functionFieldˣ) : Z.functionField) y‖ -
      ((M.φ σ).φ (pick (M.φ σ).isLB y) y + (N.φ σ).φ (pick (N.φ σ).isLB y) y) / 2 = _
    rw [logNorm, logNorm, Units.val_mul,
      ratVal_mul (hy ▸ regAt_genericPoint _) (hy ▸ regAt_genericPoint _), norm_mul, Real.log_mul (hu _) (hu _)]
    ring
  have := SmallSecHeight.numberField hZ hc
  have : Finite (Σ σ : k →+* ℂ, CxPts q σ) := .of_equiv _ (SmallSecHeight.ptsEquiv hZ).symm
  have (σ : k →+* ℂ) : Finite (CxPts q σ) := .of_injective _ (sigma_mk_injective (i := σ))
  have := hZ.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have (σ : k →+* ℂ) := Fintype.ofFinite (CxPts q σ)
  unfold HermLB.curveDeg
  rw [div_tens M N hr hs]
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  rw [finsum_add_distrib (hfin _) (hfin _)]
  simp only [finsum_eq_sum_of_fintype, h₂, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtHtComb

namespace GlobalTheory.PtHtComb

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem height_tens (hX : IsArithVar p D) {L M : HermLB p} {h h' h'' : X → ℝ} (H : L.IsArithHeight h)
    (H' : M.IsArithHeight h') (H'' : (L.tens M).IsArithHeight h'') {x : X} (hx : IsAlgPt x) :
    h'' x = h x + h' x := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have := hX.isNoetherian_sub i
  have hr : range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr i).isLB
  obtain ⟨s, hs⟩ := exists_isRatSec (M.restr i).isLB
  obtain ⟨t, ht, h₁, h₂⟩ := (HermLB.isometric_pull_tens (L := L) (M := M) i rfl).symm.exists_isRatSec
    (isRatSec_tens hr hs)
  rw [H''.point Z i hcΓ hd t ht, H.point Z i hcΓ hd r hr, H'.point Z i hcΓ hd s hs,
    ← curveDeg_tens hZ hc' (L.restr i) (M.restr i) hr hs, HermLB.curveDeg, h₁]
  refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
  rw [hZ.under_eq_genericPoint]
  exact CartierDiv.genericPoint_notMem_supp _

end GlobalTheory.PtHtComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesDeformationOfBoundedLatticeSeries
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow

theorem deform_of_lattice_series : ∀ (κ : Rule) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [CharZero C] (e : C →+* ℂ) (x : KeyIn C) (g : ℕ) (hg : x.P.g = g) (m : ℕ) (ζ : Cˣ)
    (lev : Out.Level x.P (m ^ 2) (unitOn ζ)) (k : C) (X : Type) (n : X → ℕ) (π : C) (B : ℝ)
    (a : (Fin (2 * g) → ZMod (m ^ 2)) → X → C) (b : (Fin (2 * g) → ZMod (m ^ 2)) → Fin g → X → C),
    π ≠ 0 → ‖π‖ < 1 → (∀ i, {α | n α = i}.Finite) → (∀ i α, ‖a i α‖ ≤ B * ‖π‖ ^ n α) →
    (∀ i j α, ‖b i j α‖ ≤ B * ‖π‖ ^ n α) →
    ThJet x hg m (levelPoint lev hg) (fun i => ∑' α, a i α) (fun i j => ∑' α, b i j α) →
    (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, u ≠ 0 → ‖u‖ < ε →
      ((∀ i, Summable fun α => ‖e (a i α) * u ^ n α‖) ∧ ∀ i j, Summable fun α => ‖e (b i j α) * u ^ n α‖) ∧
      ∃ (x₀ : KeyIn ℂ) (hg₀ : x₀.P.g = g) (lev₀ : Out.Level x₀.P (m ^ 2) (unitOn (Units.map e.toMonoidHom ζ))),
        ThJet x₀ hg₀ m (levelPoint lev₀ hg₀) (fun i => ∑' α, e (a i α) * u ^ n α)
          (fun i j => ∑' α, e (b i j α) * u ^ n α) ∧ (κ ℂ x₀ : ℂ) = e k) →
    Deform κ e x hg m ζ lev k := by
  intro κ C _ _ _ _ e x g hg m ζ lev k X n π B a b hπ0 hπ1 hfin ha hb hJ hE
  have hA := fun i => lattice_series_regroup C X n π (a i) B hπ0 hπ1 hfin (ha i)
  have hB := fun i j => lattice_series_regroup C X n π (b i j) B hπ0 hπ1 hfin (hb i j)
  choose Θ hΘb hΘs hΘc using hA
  choose Γ hΓb hΓs hΓc using hB
  obtain ⟨ε, hε, hu⟩ := hE
  have heπ : e π ≠ 0 := (map_ne_zero e).2 hπ0
  have hnπ : 0 < ‖e π‖ := norm_pos_iff.2 heπ
  refine ⟨Θ, Γ, π, max B 0, hπ1, fun i l => ⟨hΘb i l, fun j => hΓb i j l⟩, ?_, ε * ‖e π‖, mul_pos hε hnπ, ?_⟩
  · have h1 : (fun i => ∑' l, PowerSeries.coeff l (Θ i) * π ^ l) = fun i => ∑' α, a i α := funext hΘs
    have h2 : (fun i j => ∑' l, PowerSeries.coeff l (Γ i j) * π ^ l) = fun i j => ∑' α, b i j α :=
      funext fun i => funext (hΓs i)
    rw [h1, h2]; exact hJ
  · intro u hu0 hul
    have hv0 : u / e π ≠ 0 := div_ne_zero hu0 heπ
    have hvl : ‖u / e π‖ < ε := by rw [norm_div, div_lt_iff₀ hnπ]; exact hul
    obtain ⟨⟨hsa, hsb⟩, x₀, hg₀, lev₀, hJ₀, hk⟩ := hu (u / e π) hv0 hvl
    refine ⟨fun i => ⟨(hΘc i e u (hsa i)).1, fun j => (hΓc i j e u (hsb i j)).1⟩, x₀, hg₀, lev₀, ?_, hk⟩
    have h1 : (fun i => ∑' l, e (PowerSeries.coeff l (Θ i)) * u ^ l) = fun i => ∑' α, e (a i α) * (u / e π) ^ n α :=
      funext fun i => (hΘc i e u (hsa i)).2
    have h2 : (fun i j => ∑' l, e (PowerSeries.coeff l (Γ i j)) * u ^ l) =
        fun i j => ∑' α, e (b i j α) * (u / e π) ^ n α :=
      funext fun i => funext fun j => (hΓc i j e u (hsb i j)).2
    rw [h1, h2]; exact hJ₀

end GlobalTheory.MBLow
end

