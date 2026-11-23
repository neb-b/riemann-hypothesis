module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProductAcyclicOverAffineFiniteClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem sq_abelian_and_affine_H1 : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  intro R _
  refine ⟨fun A _ g hA hg ↦ ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, ?_⟩, fun X _ s c ↦ ?_⟩
  · haveI := hg
    haveI : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (Limits.pullback.fst A.hom A.hom ≫ A.hom))
  · let T₀ : AffOp X := Opposite.op ⟨⊤, isAffineOpen_top X⟩
    have h : Limits.IsInitial T₀ := Limits.IsInitial.ofUniqueHom
      (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top X⟩ from le_top (a := U.unop.1))).op) fun _ _ ↦ rfl
    exact H1.eq_zero_of_isInitial _ h c

end GlobalTheory.Obs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyChartAffineOfChartFiniteType
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualApprox

theorem evc_comp_of_same {S : Scheme.{0}} {A T T₀ Y : Over S} {N : LB (A ⊗ T).left} {N₀ : LB (A ⊗ T₀).left}
    (hN : N.IsLB) (hN₀ : N₀.IsLB) (h : T ⟶ T₀) (hs : Same A N N₀ (𝟙 T) h) (y : Y ⟶ T) :
    evc hN (fst A Y) (snd A Y ≫ y) = evc hN₀ (fst A Y) (snd A Y ≫ y ≫ h) := by
  rw [same_iff hN hN₀, Category.comp_id] at hs
  have := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ y)).left) hs
  rw [pull_evc, pull_evc] at this
  simp only [lift_fst, lift_snd, lift_snd_assoc, Category.assoc] at this
  exact this

theorem chartAt_of_finiteType : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → (∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  intro R _ _ A _ hA U M hM hfin T _ N hN
  obtain ⟨T₀, h, N₀, hT₀, hft, hN₀, hs⟩ := _root_.GlobalTheory.DualApprox.exists_fam_finiteType R A hA T N hN
  obtain ⟨W₀, hW₀⟩ := hfin T₀ hft N₀ hN₀
  refine ⟨h.left ⁻¹ᵁ W₀, fun Y y ↦ ?_⟩
  have key : ∀ u : Y ⟶ U, Same A N M y u ↔ Same A N₀ M (y ≫ h) u := fun u ↦ by
    rw [same_iff hN.isLB hM.isLB, same_iff hN₀.isLB hM.isLB, evc_comp_of_same hN.isLB hN₀.isLB h hs y]
  simp_rw [key, hW₀ Y (y ≫ h)]
  rfl

end GlobalTheory.DualApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleEqMumfordLambdaOfAmpleAlgClose
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AddLineField


open GlobalTheory.PrimitiveOverField in
theorem additive_eq_lam_of_ample : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ N : LB (A ⊗ 𝟙_ (Over (Sp K))).left, Fam A N → ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, Same A N (abelian₂ A L) (𝟙 _) a := by
  intro K _ _ A _ hA L hL hamp N hN
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have hpr : IsProjBy A.hom := by
    obtain ⟨_, _, m, s, hH, hv⟩ := veryAmpleBy_of_relAmple hL hamp (𝟙 A.left) (Category.id_comp _)
      (pull_isLB hL (𝟙 A.left)) (GlobalTheory.lbIso_self (pull_isLB hL _))
    exact ⟨_, hH, m, s, hv⟩
  have hproj : ∀ (R : Type) [CommRing R] (u : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K)) (X : Scheme.{0})
      (π : X ⟶ A.left) (f : X ⟶ Spec (CommRingCat.of R)), IsPullback π f A.hom u → IsProjBy f :=
    fun R _ u X π f h => GlobalTheory.StabFlat.isProjBy_baseChange hpr h
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.exists_gen_theta_of_isProjBy K A hA hpr L hL
  obtain ⟨S, hS, hSK⟩ := _root_.GlobalTheory.KLFinite.kl_finite K A hA L hL hamp
  let O : LB A.left := ev N (𝟙 A) (toUnit A)
  have hO : O.IsLB := pull_isLB hN.isLB _
  have hLam : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have pO : ∀ {Y : Over (Sp K)} (u : Y ⟶ A), CechPic.pull u.left (cls O hO) = evc hN.isLB u (toUnit Y) := by
    intro Y u
    rw [cls_ev hN.isLB, pull_evc, Category.comp_id, comp_toUnit]
  have lamO : lam (cls O hO) (fst A A) (snd A A) = 0 := by
    have e := (isAdditive_iff hN.isLB).1 hN.add (A ⊗ A) (fst A A) (snd A A) (toUnit _)
    have e1 := hN.add.evc_one hN.isLB (toUnit (A ⊗ A))
    simp only [lam, pO, e, e1]
    abel
  have key : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO = lam (cls L hL) (toUnit A ≫ x) (𝟙 A) →
      Same A N (abelian₂ A L) (𝟙 _) x := by
    intro x hx
    rw [same_iff hN.isLB hLam]
    have e1 : evc hN.isLB (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ 𝟙 _) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (cls O hO) := by
      rw [pO, Category.comp_id, toUnit_unique (toUnit _) (snd A _)]
    have e2 : evc hLam (fst A (𝟙_ (Over (Sp K)))) (snd A _ ≫ x) =
        CechPic.pull (fst A (𝟙_ (Over (Sp K)))).left (lam (cls L hL) (toUnit A ≫ x) (𝟙 A)) := by
      have cL : cls (abelian₂ A L) hLam = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hLam
      rw [evc, cL, pull_lam, pull_lam, lift_fst,
        lift_snd, Category.comp_id, ← Category.assoc, toUnit_unique (fst A _ ≫ toUnit A) (snd A _), lam_comm]
    rw [e1, e2, hx]
  by_contra hno
  have hno' : ∀ x : 𝟙_ (Over (Sp K)) ⟶ A, cls O hO ≠ lam (cls L hL) (toUnit A ≫ x) (𝟙 A) :=
    fun x e => hno ⟨x, key x e⟩
  obtain ⟨F, hF, eF⟩ := cls_surj (lam (cls L hL) (fst A A) (snd A A) - CechPic.pull (snd A A).left (cls O hO))
  have hpq : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have cst_left : ∀ x : 𝟙_ _ ⟶ A, (toUnit A ≫ x).left = A.hom ≫ x.left := fun x =>
    congrArg (· ≫ x.left) ((Category.comp_id _).symm.trans (Over.w (toUnit A)))
  have s₁ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (toUnit A ≫ x) (𝟙 A)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) - cls O hO := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, Over.id_left, pull_id]
  have s₂ : ∀ x : 𝟙_ _ ⟶ A, cls _ (pull_isLB hF (lift (𝟙 A) (toUnit A ≫ x)).left) =
      lam (cls L hL) (toUnit A ≫ x) (𝟙 A) := fun x => by
    rw [cls_pull hF, eF, map_sub, pull_lam, ← pull_comp, ← Over.comp_left, lift_fst, lift_snd, pull_const, sub_zero,
      lam_comm]
  have total : Ac ((fst A A).left ≫ A.hom) F := by
    refine (_root_.GlobalTheory.ProductAcyclic.acyclic_of_over_affine_and_converse K _ _ _ _ _ _ _ hpq inferInstance inferInstance inferInstance inferInstance F hF).1
      fun R _ t Y π f h ht => ac_of_slices hproj hpq h hF fun x hx _ => ?_
    let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
    refine ⟨(lift (toUnit A ≫ x') (𝟙 A)).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
    · exact (congrArg CommaMorphism.left (lift_fst (toUnit A ≫ x') (𝟙 A))).trans (cst_left x')
    · exact congrArg CommaMorphism.left (lift_snd (toUnit A ≫ x') (𝟙 A))
    · rw [s₁, lam_sub, lam_lam hL hΘ, lamO, sub_zero]
    · rw [s₁, sub_ne_zero]
      exact fun e => hno' x' e.symm
  rw [hpq.w] at total
  let o : Spec (CommRingCat.of K) ⟶ A.left := η[A].left
  have ho : o ≫ A.hom = 𝟙 _ := Over.w η[A]
  have all := _root_.GlobalTheory.ProductAcyclicFin.acyclic_over_affine_of_finite_closed K _ _ _ _ _ _ _ hpq.flip inferInstance inferInstance inferInstance
    inferInstance F hF S hS (fun R _ t Y π f h ht hne => ac_of_slices hproj hpq.flip h hF fun x hx hr => by
      let x' : 𝟙_ _ ⟶ A := Over.homMk x hx
      refine ⟨(lift (𝟙 A) (toUnit A ≫ x')).left, ?_, ?_, ac_of_primitive hA hpr (pull_isLB hF _) ?_ ?_⟩
      · exact (congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ x'))).trans (cst_left x')
      · exact congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ x'))
      · rw [s₂, lam_lam hL hΘ]
      · rw [s₂]
        intro e
        have hm := hSK x' e
        obtain ⟨y, hy⟩ := hr (IsLocalRing.closedPoint K)
        exact hne y (by rw [hy]; exact hm)) total
  have hs := ac_slice hproj hpq.flip hF all o ho (lift (𝟙 A) (toUnit A ≫ η[A])).left
    ((congrArg CommaMorphism.left (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (cst_left η[A]))
    (congrArg CommaMorphism.left (lift_fst (𝟙 A) (toUnit A ≫ η[A])))
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : Nonempty A.left := ⟨o (IsLocalRing.closedPoint K)⟩
  exact not_ac_of_cls_eq_zero _ (pull_isLB hF _) ((s₂ _).trans (lam_one_left _ _)) hs

end GlobalTheory.AddLineField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPieces
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.ProdGlue

theorem fam_of_pieces {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left] (hcov : ⨆ i, (j i).left.opensRange = ⊤) (hdisj : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange) (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Fam A (P i)) (hPt : Pt.IsLB) (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) : Fam A Pt := by
  refine ⟨hPt, (GlobalTheory.AbDual.isAdditive_iff hPt).mpr ?_⟩
  intro Y a a' t

  have hcovY : ⨆ i, (pullback.fst t.left (j i).left).opensRange = ⊤ := by
    simp only [Scheme.Hom.opensRange_pullbackFst]
    rw [← Scheme.Hom.preimage_iSup, hcov]
    try simp
  have hdisjY : Pairwise fun i i' => Disjoint (pullback.fst t.left (j i).left).opensRange
      (pullback.fst t.left (j i').left).opensRange := by
    intro i i' hii
    have h : Disjoint (j i).left.opensRange (j i').left.opensRange := hdisj hii
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Hom.opensRange_pullbackFst]
    rw [disjoint_iff] at h ⊢
    refine le_antisymm (fun x hx => ?_) bot_le
    have hx' : t.left x ∈ (j i).left.opensRange ⊓ (j i').left.opensRange := ⟨hx.1, hx.2⟩
    rw [h] at hx'
    simp at hx'

  rw [← sub_eq_zero]
  refine _root_.GlobalTheory.PicDisj.eq_zero_of_pull_eq_zero (fun i => pullback.fst t.left (j i).left) hcovY hdisjY _ (fun i => ?_)
  let Zi : Over S := Over.mk (pullback.fst t.left (j i).left ≫ Y.hom)
  let u : Zi ⟶ Y := Over.homMk (pullback.fst t.left (j i).left) rfl
  have hv : pullback.snd t.left (j i).left ≫ (B i).hom = Zi.hom := by
    show pullback.snd t.left (j i).left ≫ (B i).hom = pullback.fst t.left (j i).left ≫ Y.hom
    rw [← Over.w (j i), ← Over.w t, ← Category.assoc, ← Category.assoc, pullback.condition]
  let v : Zi ⟶ B i := Over.homMk (pullback.snd t.left (j i).left) hv
  have huv : u ≫ t = v ≫ j i := by
    ext
    simp [u, v, pullback.condition]
  change GlobalTheory.CechPic.pull u.left _ = 0
  rw [map_sub, map_add (f := _), GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, GlobalTheory.AbDual.pull_evc, huv,
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i),
    evc_comp_of_iso (j i) hPt (hP i).isLB (hiso i), MonObj.comp_mul,
    (GlobalTheory.AbDual.isAdditive_iff (hP i).isLB).mp (hP i).add]
  exact sub_self _

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenRingNormalCharZeroFiniteTypeOverInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyVals

theorem ring_of_isAffineOpen : ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (W : S.Opens), IsAffineOpen W → (W : Set S).Nonempty →
    Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s → CharZero Γ(S, ⊤) →
    IsIntegrallyClosed Γ(S, W) ∧ CharZero Γ(S, W) ∧ Algebra.FiniteType ℤ Γ(S, W) := by
  intro S _ s W hW hne hN hs hc
  haveI : Nonempty W := hne.to_subtype
  haveI : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).2 hN
  refine ⟨GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW, ?_, ?_⟩
  · exact charZero_of_injective_ringHom (map_injective_of_isIntegral S (homOfLE (le_top : W ≤ ⊤)))
  · have h₁ : (s.appLE ⊤ W le_top).hom.FiniteType :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s hs ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
    have h₂ : ((Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).FiniteType :=
      RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv.surjective
    have h₃ := h₁.comp h₂
    rw [← RingHom.finiteType_algebraMap, RingHom.ext_int (algebraMap ℤ Γ(S, W))
      ((s.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)]
    exact h₃

end GlobalTheory.KeyVals
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem presents_lbPow_toLB' {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ) :
    Presents (k • D) (lbPow (toLB D) k) fun j => (j PUnit.unit).1.2 ^ k := by
  refine ⟨isLB_lbPow (isLB_toLB D) k, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB D) k).g i j = _ from lbPow_g _ k i j, Units.val_pow_eq_pow_val,
      LB.val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ k i).le hx)).nsmul k

theorem locus_rat {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) :
    locus D k ((presents_lbPow_toLB' D k).rat s) = (nonzeroLocus s : Set X) :=
  Set.ext fun _ => (presents_lbPow_toLB' D k).generatesAt_rat_iff s

theorem rat_mem_sec {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (k : ℕ)
    (s : (lbPow (toLB D) k).Sec) : (presents_lbPow_toLB' D k).rat s ∈ Sec D k :=
  CartierDiv.mem_sections.1 ((presents_lbPow_toLB' D k).rat_mem s)

theorem ampleDiv_iff_isAmpleLB : ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] (D : CartierDiv X),
    AmpleDiv D ↔ IsAmpleLB (toLB D) := by
  intro X _ hc D
  constructor
  · intro h
    refine ⟨isLB_toLB D, hc, fun x => ?_⟩
    obtain ⟨k, hk, u, hu, U, hUa, hU, hx⟩ := h x
    obtain ⟨s, hs⟩ := (presents_lbPow_toLB' D k).exists_rat_eq (CartierDiv.mem_sections.2 hu)
    have e : nonzeroLocus s = U := SetLike.coe_injective (by rw [hU, ← locus_rat D k s, hs])
    exact ⟨k, hk, s, e ▸ hx, e ▸ hUa⟩
  · intro h x
    obtain ⟨k, hk, s, hx, ha⟩ := h.exists_affine x
    exact ⟨k, hk, _, rat_mem_sec D k s, nonzeroLocus s, ha, (locus_rat D k s).symm, hx⟩

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.BlowAmpleNoeth
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.ProjBlowup

theorem ample_twist_of_blowup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s →
    FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  intro R _ _ _ X X' N s J b ν EX hs hb hν hEX L hL
  obtain ⟨L₀, m, σ, hL₀, hσ⟩ := GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf R X s J hs
  obtain ⟨c, hc, hprop, hci⟩ := _root_.GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates R X X' s J b L₀ m σ hs hb hσ
  have hψ : Proportional σ (ν ≫ b) (ν ≫ c) := hprop.comp ν
  have hiso := GlobalTheory.T.pullback_O1_iso_blowup_twist_dual R X N J L₀ m σ (ν ≫ b) (ν ≫ c) EX hL₀ hσ hψ hEX
  have : IsProper s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (GlobalTheory.AmpleDominates.eventually_isAmpleLB s hL hL₀)
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hO := isAmple_projective_O_one R m
  set A := LB.div (lbPow L T) L₀ with hAdef
  set p := pullback.fst s (PSpace.str R m)
  set q := pullback.snd s (PSpace.str R m)
  set B := tens (A.pull p) ((O1 R m).pull q)
  have hBL : B.IsLB := isLB_tens (LB.isLB_pull hA.isLB _) (LB.isLB_pull hO.isLB _)
  have hB : IsAmpleLB B := by
    refine hA.box hO hBL (IsPullback.of_hasPullback s (PSpace.str R m)) ?_
    have h1 := LB.isLB_div hBL (LB.isLB_pull hA.isLB p)
    refine (cls_eq_zero_iff (LB.isLB_div h1 (LB.isLB_pull hO.isLB q))).1 ?_
    rw [cls_div h1 (LB.isLB_pull hO.isLB q), cls_div hBL (LB.isLB_pull hA.isLB p),
      cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q)]
    abel
  let h : N ⟶ pullback s (PSpace.str R m) := ν ≫ pullback.lift b c hc
  have hp : h ≫ p = ν ≫ b := by
    simp only [h, p, Category.assoc]; rw [pullback.lift_fst]
  have hq : h ≫ q = ν ≫ c := by
    simp only [h, q, Category.assoc]; rw [pullback.lift_snd]
  have h2 := hB.pull_of_isAffineHom h
  have hT : (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)).IsLB :=
    isLB_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb)
  refine h2.of_lbIso hT ((cls_eq_iff hT (LB.isLB_pull hBL h)).1 ?_)
  have hG := (cls_eq_iff (LB.isLB_pull hO.isLB _) (isLB_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb))).2 hiso
  rw [cls_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb, cls_pull hO.isLB, cls_pull hL₀] at hG
  rw [cls_pull hBL, cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q), cls_pull hA.isLB, cls_pull hO.isLB,
    cls_div (isLB_lbPow hL.isLB T) hL₀, cls_lbPow hL.isLB,
    cls_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb,
    cls_lbPow (LB.isLB_pull hL.isLB _), cls_pull hL.isLB, map_add, ← pull_comp, ← pull_comp, hp, hq, hG]
  simp only [map_sub, map_nsmul]
  abel

end GlobalTheory.BlowAmpleNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add (f := _)]⟩
      simp only [Obs.Aug.KerQ, map_add (f := _)] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_ev_of_isPullback : ∀ (S : Scheme.{0}) (A B S' S'' B'' : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (h : S'' ⟶ S') (k : B'' ⟶ B) (b'' : B'' ⟶ S''), Rep A b P → IsPullback k b'' b h → Rep A b'' (ev P (fst A B'') (snd A B'' ≫ k)) := by
  first | exact @GlobalTheory.DualCon.Rep.baseChange | exact GlobalTheory.DualCon.Rep.baseChange | (intros; apply GlobalTheory.DualCon.Rep.baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFrame_change_diagonal_units_integral_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  first | exact @GlobalTheory.IntFrameDiag.diag_unit_of_intFr | exact GlobalTheory.IntFrameDiag.diag_unit_of_intFr | (intros; apply GlobalTheory.IntFrameDiag.diag_unit_of_intFr <;> assumption)
end

