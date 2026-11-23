module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolFibre

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isHolTo_comp {W : Set E} {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo W c) (ψ : X ⟶ Y) :
    IsHolTo W (fun w => c w ≫ ψ) := by
  intro U f
  have := hc (ψ ⁻¹ᵁ U) ((ψ.app U).hom f)
  simp only [valAt'_comp, ← top_le_preimage_comp] at this
  exact this

theorem isHolTo_const {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    IsHolTo W (fun _ => x) := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [h, and_true]
    exact hW
  · simp only [h, and_false, Set.setOf_false, isOpen_empty]

theorem isHolTo_of_isPullback {W : Set E} {S X Y Z : Scheme.{0}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)}
    (ha : IsHolTo W (fun w => c w ≫ p)) (hb : IsHolTo W (fun w => c w ≫ q)) : IsHolTo W c := by
  intro U f
  refine holFamily_of_affine valAt'_rules W Z c (fun w₀ hw₀ => ?_) U f
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((c w₀ ≫ p ≫ s) (default : PrimeSpectrum ℂ))) isOpen_univ
  have hm₁ : (c w₀ ≫ p) (default : PrimeSpectrum ℂ) ∈ s ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, top_le_preimage_iff_mem]
    exact hx₀
  have hm₂ : (c w₀ ≫ q) (default : PrimeSpectrum ℂ) ∈ t ⁻¹ᵁ U₀ := by
    rw [← top_le_preimage_iff_mem, ← top_le_preimage_comp, Category.assoc, ← H.w, top_le_preimage_iff_mem]
    exact hx₀
  obtain ⟨_, ⟨U₁, hU₁, rfl⟩, hx₁, hl₁⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hm₁ (s ⁻¹ᵁ U₀).isOpen
  obtain ⟨_, ⟨U₂, hU₂, rfl⟩, hx₂, hl₂⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    hm₂ (t ⁻¹ᵁ U₀).isOpen
  have hU₀ : IsAffineOpen U₀ := hU₀
  have hU₁ : IsAffineOpen U₁ := hU₁
  have hU₂ : IsAffineOpen U₂ := hU₂
  have hl₁ : U₁ ≤ s ⁻¹ᵁ U₀ := hl₁
  have hl₂ : U₂ ≤ t ⁻¹ᵁ U₀ := hl₂
  set V : Z.Opens := p ⁻¹ᵁ U₁ ⊓ q ⁻¹ᵁ U₂ with hVdef
  have hiff : ∀ w, ⊤ ≤ c w ⁻¹ᵁ V ↔ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U₁ ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U₂ := fun w => by
    rw [hVdef, Scheme.Hom.preimage_inf, le_inf_iff, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  have hV : IsAffineOpen V := by
    have : IsAffine _ := hU₀
    have : IsAffine _ := hU₁
    have : IsAffine _ := hU₂
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁
      hVdef).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := U₀) (UT := U₂) (UX := U₁) hl₂ hl₁ hVdef).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ hU₀ hU₂ hU₁)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  refine ⟨V, hV, (hiff w₀).2 ⟨(top_le_preimage_iff_mem _ _).2 hx₁, (top_le_preimage_iff_mem _ _).2 hx₂⟩, ?_,
    fun g => ?_⟩
  · convert (ha U₁ 0).1.inter (hb U₂ 0).1 using 1
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hiff]
    tauto
  · have hg : g ∈ Subring.closure _ := hgen.ge (Subring.mem_top g)
    induction hg using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ((ha U₁ y).2.mono fun w (hw : w ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V}) =>
          ⟨hw.1, ((hiff w).1 hw.2).1⟩).congr fun w hw =>
          valAt'_appLE (c w) p U₁ V _ y hw.2
      · exact ((hb U₂ y).2.mono fun w (hw : w ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V}) =>
          ⟨hw.1, ((hiff w).1 hw.2).2⟩).congr fun w hw =>
          valAt'_appLE (c w) q U₂ V _ y hw.2
    | zero => exact (differentiableOn_const (0 : ℂ)).congr fun w _ => valAt'_zero _ _
    | one => exact (differentiableOn_const (1 : ℂ)).congr fun w hw => valAt'_one _ hw.2
    | add x y _ _ hx hy => exact (hx.add hy).congr fun w _ => valAt'_add _ _ _ _
    | neg x _ hx => exact hx.neg.congr fun w _ => valAt'_neg _ _ _
    | mul x y _ _ hx hy => exact (hx.mul hy).congr fun w _ => valAt'_mul _ _ _ _

theorem isHolTo_fibPt {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (G : Over X) (y : Sp ℂ ⟶ X)
    (e : E → (Over.mk y ⟶ G)) (he : IsHolTo W (fun z => (e z).left)) :
    IsHolTo W (fun z => fibPt G (e z)) := by
  refine isHolTo_of_isPullback (IsPullback.of_hasPullback G.hom y) ?_ ?_
  · simp only [fibPt, pullback.lift_fst]
    exact he
  · simp only [fibPt, pullback.lift_snd]
    exact isHolTo_const hW _

theorem isHolTo_fibPt_and_comp :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) :=
  fun _ G y _ e he =>
    ⟨isHolTo_fibPt isOpen_univ G y e he, fun _ ψ => isHolTo_comp (isHolTo_fibPt isOpen_univ G y e he) ψ⟩

end GlobalTheory.HolFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
noncomputable section
namespace GlobalTheory.AbLaw.BaseChange

theorem cst_comp_specMap {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f' : X ⟶ Spec (CommRingCat.of R')) (W : X.Opens) (r : R) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) W r = cst f' W (g r) := by
  have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)).hom r)
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom] at h ⊢
  rw [h]

theorem ap_top_eq_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    {W : X.Opens} (h : W ≤ f ⁻¹ᵁ ⊤) (d : Γ(Spec (CommRingCat.of R), ⊤)) :
    ∃ r, ap f h d = cst f W r := by
  obtain ⟨r, rfl⟩ := (cst_bijective (𝟙 (Spec (CommRingCat.of R))) (W := ⊤) rfl).2 d
  exact ⟨r, by rw [ap_cst, Category.comp_id]⟩

end GlobalTheory.AbLaw.BaseChange


open GlobalTheory.AbLaw.BaseChange in
theorem GlobalTheory.AbLaw.isProjBy_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsProjBy f → IsProjBy f' := by
  intro R R' _ _ g X X' f p q sq hf
  obtain ⟨H, hH, m, s, hs, hs'⟩ := hf
  have hloc : ∀ a, nonzeroLocus (boxSec p q (s a) (oneSec _)) = p ⁻¹ᵁ nonzeroLocus (s a) ⊓ q ⁻¹ᵁ ⊤ := fun a => by
    rw [nonzeroLocus_boxSec, nonzeroLocus_oneSec]
  have hbox : (box p q H (Inh.trivLB _)).IsLB := by
    have hK : (Inh.trivLB (Spec (CommRingCat.of R'))).IsLB := by
      refine ⟨?_, ?_, ?_⟩
      · simp [Inh.trivLB]
      · intro i
        exact (res _).map_one
      · intro i j k
        exact (congrArg₂ (· * ·) (res _).map_one (res _).map_one).trans
          ((_root_.one_mul _).trans (res _).map_one.symm)
    refine ⟨?_, ?_, ?_⟩
    · refine top_le_iff.1 fun y _ => ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show p y ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show q y ∈ ⨆ i, (Inh.trivLB _).U i by rw [hK.cover]; trivial)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, j), hi, hj⟩
    · intro a
      refine Units.ext ((rs_mul p q _ _ _ _ _).trans ?_)
      rw [ap_g_self p hH, ap_g_self q hK, _root_.mul_one, Units.val_one]
    · intro a b c
      refine Units.ext ((congrArg₂ (· * ·) (rs_mul p q _ _ _ _ _) (rs_mul p q _ _ _ _ _)).trans
        (Eq.trans ?_ (rs_mul p q _ _ _ _ _).symm))
      exact (mul_mul_mul_comm _ _ _ _).trans
        (congrArg₂ (· * ·) (ap_cocycle p hH _ _ _ _ _ _).symm (ap_cocycle q hK _ _ _ _ _ _).symm)
  refine ⟨box p q H (Inh.trivLB _), hbox, m,
    fun a => boxSec p q (s a) (oneSec _), ?_, fun a => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show p y ∈ ⨆ i, nonzeroLocus (s i) by rw [hs]; trivial)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [hloc]
    exact ⟨hi, trivial⟩
  obtain ⟨aff₁, r₁, hr₁, sj₁⟩ := hs' a
  have aff₂ : IsAffineOpen (⊤ : (Spec (CommRingCat.of R')).Opens) := isAffineOpen_top _
  have loc := hloc a
  have l₁ := loc.le.trans inf_le_left
  have l₂ := loc.le.trans inf_le_right
  refine ⟨?_, fun b => ap p l₁ (r₁ b), fun b k => ?_, ?_⟩
  · have : IsAffine _ := aff₁
    have : IsAffine _ := aff₂
    have : IsAffine _ := isAffineOpen_top (Spec (CommRingCat.of R))
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) le_top le_top loc).isoPullback.hom
  · refine (rs_mul p q _ _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (rs_ap p _ _ _) (rs_mul p q _ _ _ _ _)).symm)
    exact (congrArg (· * _) (ap_ratio p (hr₁ b k.1) _ _)).trans (_root_.mul_assoc _ _ _)
  · have po := (isIso_pushoutSection_iff sq (US := ⊤) le_top le_top loc).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) aff₂ aff₁)
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · obtain ⟨F, rfl⟩ := sj₁ d
      change ap p l₁ _ ∈ _
      induction F using MvPolynomial.induction_on with
      | C c => exact ⟨MvPolynomial.C (g c), by
          rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, ap_cst, sq.w, GlobalTheory.AbLaw.BaseChange.cst_comp_specMap]⟩
      | add F G hF hG => rw [map_add (f := _), map_add (f := _)]; exact Subring.add_mem _ hF hG
      | mul_X F i hF =>
        rw [map_mul, map_mul]
        refine Subring.mul_mem _ hF ⟨MvPolynomial.X i, ?_⟩
        simp only [MvPolynomial.eval₂Hom_X']
    · change ap q l₂ _ ∈ _
      obtain ⟨r, hr⟩ := GlobalTheory.AbLaw.BaseChange.ap_top_eq_cst q l₂ d
      exact ⟨MvPolynomial.C r, by rw [MvPolynomial.eval₂Hom_C, hr]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LineBundleTrivialBasicOpenOfTrivialFibreProduct
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.AbLaw.CubeOpen

noncomputable section

namespace GlobalTheory.Exist.ProdOpen

section BaseChange
variable {S S' : Scheme.{0}} (φ : S' ⟶ S) (X Y : Over S)

def prodMap : ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).left ⟶ (X ⊗ Y).left :=
  (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left ≫ pullback.fst (X ⊗ Y).hom φ

theorem isPullback_prodMap :
    IsPullback (prodMap φ X Y) ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
      (X ⊗ Y).hom φ := by
  have h := IsPullback.of_hasPullback (X ⊗ Y).hom φ
  have hw := Over.w (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  haveI : IsIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y).left :=
    (Over.forget S').map_isIso (Functor.LaxMonoidal.μ (Over.pullback φ) X Y)
  rw [← hw]
  exact isPullback_iso_comp h _

theorem lift_prodMap {Z : Over S} (a : Z ⟶ X) (b : Z ⟶ Y) :
    (lift ((Over.pullback φ).map a) ((Over.pullback φ).map b)).left ≫ prodMap φ X Y =
      pullback.fst Z.hom φ ≫ (lift a b).left := by
  rw [prodMap, ← Category.assoc, ← Over.comp_left, Functor.Monoidal.lift_μ]
  exact pullback.lift_fst _ _ _

theorem toUnit_section (y : 𝟙_ (Over S) ⟶ Y) :
    toUnit ((Over.pullback φ).obj X) ≫ Functor.LaxMonoidal.ε (Over.pullback φ) ≫
      (Over.pullback φ).map y = (Over.pullback φ).map (toUnit X ≫ y) := by
  rw [← Category.assoc, Functor.Monoidal.toUnit_ε, Functor.map_comp]

end BaseChange

theorem bijective_baseChange {R T : Type} [CommRing R] [CommRing T] (g₁ : R →+* T) (X : Over (Sp R))
    (h : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom)) :
    (∀ (R' : Type) [CommRing R'] (g : T →+* R') (X' : Scheme.{0}) (π : X' ⟶ ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' ((Over.pullback (Spec.map (CommRingCat.ofHom g₁))).obj X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) := by
  intro R' _ g X' π f' hp
  have hq := hp.paste_horiz (IsPullback.of_hasPullback X.hom (Spec.map (CommRingCat.ofHom g₁)))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hq
  exact h R' _ X' _ f' hq

theorem triv_lift_prod {R : Type} [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X)
    (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y) [Flat X.hom] [Flat Y.hom] [IsProper X.hom] [IsProper Y.hom]
    (hX : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (hY : (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom))
    (M : LB (X ⊗ Y).left) (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left))
    (h₂ : Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left))
    (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T)
    (he : ∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) (he' : e ∈ IsLocalRing.maximalIdeal T)
    (H : ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left)
      (f' : X' ⟶ Spec (CommRingCat.of (T ⧸ Ideal.span {e}))),
      IsPullback π f' (X ⊗ Y).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) ≫
          Spec.map (CommRingCat.ofHom g)) → Triv (M.pull π)) :
    Triv (M.pull (prodMap (Spec.map (CommRingCat.ofHom g)) X Y)) := by
  let φ : Sp T ⟶ Sp R := Spec.map (CommRingCat.ofHom g)
  have hp := IsPullback.of_hasPullback ((Over.pullback φ).obj X ⊗ (Over.pullback φ).obj Y).hom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))))
  refine GlobalTheory.SmallExtLift.triv_prod_of_small_extension T e he ((Over.pullback φ).obj X) ((Over.pullback φ).obj Y)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map x₀)
    (Functor.LaxMonoidal.ε (Over.pullback φ) ≫ (Over.pullback φ).map y₀)
    (inferInstanceAs (Flat (pullback.snd X.hom φ))) (inferInstanceAs (Flat (pullback.snd Y.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd X.hom φ)))
    (inferInstanceAs (IsProper (pullback.snd Y.hom φ)))
    (bijective_baseChange g X hX) (bijective_baseChange g Y hY) (M.pull (prodMap φ X Y))
    (LB.isLB_pull hM _) ?_ ?_ _ _ _ hp he' ?_
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst X.hom φ) ?_ h₁)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · refine triv_pull_pull _ _ (triv_comp (pullback.fst Y.hom φ) ?_ h₂)
    rw [← lift_prodMap, toUnit_section, CategoryTheory.Functor.map_id]
  · exact triv_pull_pull _ _ (H _ _ _ (hp.paste_horiz (isPullback_prodMap φ X Y)))

theorem surjective_prod {S : Scheme.{0}} (X Y : Over S) (x₀ : 𝟙_ (Over S) ⟶ X)
    (y₀ : 𝟙_ (Over S) ⟶ Y) : Surjective (X ⊗ Y).hom := by
  have hw : (lift x₀ y₀).left ≫ (X ⊗ Y).hom = 𝟙 S := Over.w (lift x₀ y₀)
  refine ⟨fun s => ⟨(lift x₀ y₀).left s, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, hw]
  rfl

theorem triv_basicOpen_of_triv_fibre_prod : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Nonempty (Perf (X ⊗ Y).hom M) → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ (X ⊗ Y).left) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom g₀)) → Triv (M.pull π₀) → ∃ r : R, g₀ r ≠ 0 ∧ Triv (M.pull ((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι) := by
  intro R _ X Y x₀ y₀ _ _ _ _ hX hY hXY M hM hP h₁ h₂ K _ g₀ X₀ π₀ f₀ h₀ ht₀
  haveI : IsProper (X ⊗ Y).hom := inferInstanceAs (IsProper (pullback.fst X.hom Y.hom ≫ X.hom))
  obtain ⟨r, I, hr, hI, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ (X ⊗ Y).hom M hM hP inferInstance
    (surjective_prod X Y x₀ y₀) K g₀ X₀ π₀ f₀ h₀ (hXY K g₀ X₀ π₀ f₀ h₀) ht₀
  haveI : (RingHom.ker g₀).IsPrime := RingHom.ker_isPrime g₀
  obtain ⟨c, hc, hcI⟩ := exists_ann (RingHom.ker g₀) I hI
    ((H K g₀ X₀ π₀ f₀ h₀ (Ne.isUnit hr)).1 ht₀) (fun T _ _ g e hu he he' hle => by
      refine (H T g _ _ _ (isPullback_prodMap (Spec.map (CommRingCat.ofHom g)) X Y) (hu r hr)).1 ?_
      refine triv_lift_prod X Y x₀ y₀ hX hY M hM h₁ h₂ T g e he he' fun X' π f' hp => ?_
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at hp
      exact (H _ _ X' π f' hp ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle)
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let L := Localization.Away (r * c)
  have hu : IsUnit (algebraMap R L (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have hp := IsPullback.of_hasPullback (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  have ht := (H L (algebraMap R L) _ _ _ hp hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
    IsOpenImmersion.of_isLocalization (r * c)
  have hsub : Set.range (((X ⊗ Y).hom ⁻¹ᵁ (PrimeSpectrum.basicOpen (r * c))).ι ≫ (X ⊗ Y).hom) ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rintro _ ⟨y, rfl⟩
    have := PrimeSpectrum.localization_away_comap_range L (r * c)
    change _ ∈ Set.range (PrimeSpectrum.comap (algebraMap R L))
    rw [this]
    exact y.2
  exact triv_comp (hp.lift _ _ (IsOpenImmersion.lift_fac _ _ hsub).symm) (hp.lift_fst _ _ _) ht

end GlobalTheory.Exist.ProdOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ObjComp

section Bundle

variable {X : Scheme.{0}}

def idPullIso (L : LB X) : LB.Iso L (L.pull (𝟙 X)) :=
  ⟨fun p => res (fun _ hy => ⟨mem_pull.1 hy.1, hy.2⟩ :
    (L.pull (𝟙 X)).U p.1 ⊓ L.U p.2 ≤ L.U (p.1 PUnit.unit) ⊓ L.U p.2) (L.g (p.1 PUnit.unit) p.2)⟩

theorem gw_idPullIso (L : LB X) {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (j k : L.ι) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gw (idPullIso L) f y j k = gm f y _ (L.g j k) := by
  have hm : f y ∈ (L.pull (𝟙 X)).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  show gm f y _ (res _ (L.g j k)) = _
  exact gm_res f y _ hm _

theorem pgen_idPullIso {L : LB X} (hL : L.IsLB) : PGen (idPullIso L) := by
  intro Y f y j j' k k' hj hj' hk hk'
  have hj₀ : f y ∈ L.U j := hj
  have hj₀' : f y ∈ L.U j' := hj'
  rw [gw_idPullIso L f y j k hj₀ hk, gw_idPullIso L f y j' k' hj₀' hk', Category.comp_id]
  have a := gm_cocycle hL f y hj₀ hk hk'
  have b := gm_cocycle hL f y hj₀ hj₀' hk'
  rw [mul_right_comm, b, ← a, mul_inv_cancel_right]

theorem pmaps_idPullIso (L : LB X) {K : Type} [Fintype K] {Y : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) : PMaps (idPullIso L) φ φ ε t t (𝟙 Y) := by
  intro Z r z p q hp hq
  have hp₀ : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  have hm : r z ∈ LB.wchart L φ p ⊓ LB.wchart L φ q := ⟨Set.mem_iInter.2 hp₀, Set.mem_iInter.2 hq⟩
  have e := congrArg (gm r z (LB.wchart L φ p ⊓ LB.wchart L φ q)) (ht p q)
  rw [Category.comp_id]
  refine (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  rw [gw_idPullIso L (r ≫ φ k) z (p k) (q k) (hp₀ k) (hq k)]
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z (L.U (p k) ⊓ L.U (q k)) ⟨hp₀ k, hq k⟩ _)

end Bundle

section Group

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

theorem isGrpPullback_id : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  exact (mul_left_congr (b := T.hom) (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
    (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm

variable [IsCommMonObj G]

def cubeMapId : CubeMap G G where
  F := 𝟙 _
  F3 := 𝟙 _
  e := 𝟙 _
  e_comm := by rw [Category.comp_id, Category.id_comp]
  psum_comm := fun _ => by rw [Category.comp_id, Category.id_comp]

theorem isPullCubical_id {L : RigLB G} (c : CubicalStr G L) : (cubeMapId G).IsPullCubical c c :=
  (isPullCubical_iff _ c c).2 ⟨idPullIso L.L, pgen_idPullIso L.isLB,
    pmaps_idPullIso L.L _ _ L.rig L.rigGen, pmaps_idPullIso L.L _ _ c.t c.isGen⟩

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def sabMapId {S : Scheme.{0}} (t : SAB H S) : SABMap t t (𝟙 S) where
  cm := cubeMapId t.G
  cart := isGrpPullback_id t.G
  base := rfl
  act := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  lin := isPullCubical_id t.G t.cub

variable {D : Datum H} {l : Level H}

def objMapId {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) :
    ObjMap o o (𝟙 S) where
  toSABMap := sabMapId o.t
  eta := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm
  etaA := fun _ => (Category.comp_id _).trans (Category.id_comp _).symm

section

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}

theorem sec_comp {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (h : x' ≫ φ = f ≫ x) (h' : x'' ≫ φ' = f' ≫ x') :
    x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x := by
  rw [← Category.assoc, h', Category.assoc, h, Category.assoc]

theorem sec_cancel {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (hp : IsPullback φ G'.hom G.hom f) (w : φ' ≫ G'.hom = G''.hom ≫ f')
    {x : S ⟶ G.left} {x' : S' ⟶ G'.left} {x'' : S'' ⟶ G''.left} (hx' : x' ≫ G'.hom = 𝟙 _) (hx'' : x'' ≫ G''.hom = 𝟙 _)
    (h : x' ≫ φ = f ≫ x) (h'' : x'' ≫ φ' ≫ φ = (f' ≫ f) ≫ x) : x'' ≫ φ' = f' ≫ x' := by
  apply hp.hom_ext
  · rw [Category.assoc, h'', Category.assoc, Category.assoc, h]
  · rw [Category.assoc, w, ← Category.assoc, hx'', Category.assoc, hx']; simp

theorem objMap_comp (m : ObjMap o' o f) (m' : ObjMap o'' o' f') :
    ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨n, fun a => by rw [hn']; exact sec_comp (m.eta a) (m'.eta a),
    fun a => by rw [hn']; exact sec_comp (m.etaA a) (m'.etaA a)⟩, hn⟩

theorem objMap_cancel (m : ObjMap o' o f) (n : ObjMap o'' o (f' ≫ f)) :
    ∃ m' : ObjMap o'' o' f', n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  obtain ⟨m', hn⟩ := sabCancel pullCubCancel E H S S' S'' o.t o'.t o''.t f f' m.toSABMap n.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  exact ⟨⟨m', fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.eta a)) (Over.w (o''.eta a)) (m.eta a)
      (by rw [← hn']; exact n.eta a),
    fun a => sec_cancel m.cart.1 m'.cart.1.w (Over.w (o'.etaA a)) (Over.w (o''.etaA a)) (m.etaA a)
      (by rw [← hn']; exact n.etaA a)⟩, hn⟩

end

end GlobalTheory.ObjComp

namespace GlobalTheory

end GlobalTheory
end
end

