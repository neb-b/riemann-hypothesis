module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsClosedImmersionDescendsToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.ClosedLimit

universe u

theorem surjective_of_isPushout {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {a : A ⟶ A'} {b : B ⟶ B'}
    {f' : A' ⟶ B'} (po : IsPushout f a b f') (s : Set B)
    (hs : Subring.closure (Set.range f.hom ∪ s) = ⊤) (h : ∀ x ∈ s, b.hom x ∈ f'.hom.range) :
    Function.Surjective f'.hom := by
  have h₁ : (⊤ : Subring B) ≤ f'.hom.range.comap b.hom := by
    rw [← hs, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | hx)
    · exact ⟨a.hom y, congr($(po.w.symm).hom y)⟩
    · exact h _ hx
  rw [← RingHom.range_eq_top, ← top_le_iff,
    ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨y, rfl⟩ | hx)
  · exact h₁ (Subring.mem_top y)
  · exact hx

theorem exists_isClosedImmersion_of_isLimit {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (α : D ⟶ E) (c : Cone D) (d : Cone E) (hc : IsLimit c) (hd : IsLimit d)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ i, IsAffine (E.obj i)]
    [∀ i, LocallyOfFiniteType (α.app i)]
    (hα : ∀ {i j} (f : i ⟶ j), IsPullback (D.map f) (α.app i) (α.app j) (E.map f))
    (g : c.pt ⟶ d.pt) [IsClosedImmersion g] (hg : ∀ i, g ≫ d.π.app i = c.π.app i ≫ α.app i) :
    ∃ i, IsClosedImmersion (α.app i) := by
  classical
  have : IsAffine d.pt := Scheme.isAffine_of_isLimit _ hd
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine g
  obtain ⟨i, hi⟩ := Scheme.exists_isAffine_of_isLimit D c hc
  have one (x : Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i),
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hsurj ((c.π.app i).appTop x)
    obtain ⟨j, y, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit E d hd y
    let m := IsCofiltered.min i j
    let a : m ⟶ i := IsCofiltered.minToLeft i j
    let b : m ⟶ j := IsCofiltered.minToRight i j
    have e₁ : c.π.app m ≫ D.map a = c.π.app i := c.w a
    have e₂ : c.π.app m ≫ α.app m ≫ E.map b = g ≫ d.π.app j := by
      rw [← reassoc_of% hg, d.w b]
    obtain ⟨l, f, hl⟩ := exists_app_map_eq_map_of_isLimit D c hc (U := ⊤) isCompact_univ
      ((D.map a).appTop x) ((α.app m ≫ E.map b).appTop y) (by
        have h₁ : (c.π.app m).appTop ((D.map a).appTop x) = (c.π.app i).appTop x :=
          congr(($e₁).appTop x)
        have h₂ : (c.π.app m).appTop ((α.app m ≫ E.map b).appTop y) =
          g.appTop ((d.π.app j).appTop y) := congr(($e₂).appTop y)
        exact h₁.trans (hy.symm.trans h₂.symm))
    refine ⟨l, f ≫ a, (E.map f ≫ E.map b).appTop y, ?_⟩
    have e₃ : α.app l ≫ E.map f ≫ E.map b = D.map f ≫ α.app m ≫ E.map b := by
      rw [α.naturality_assoc]
    have h₃ : (α.app l).appTop ((E.map f ≫ E.map b).appTop y) =
      (D.map f).appTop ((α.app m ≫ E.map b).appTop y) := congr(($e₃).appTop y)
    have h₄ : (D.map (f ≫ a)).appTop x = (D.map f).appTop ((D.map a).appTop x) :=
      congr(($(D.map_comp f a)).appTop x)
    exact h₃.trans (hl.symm.trans h₄.symm)
  have mono {j l : I} (f : j ⟶ i) (h : l ⟶ j) (x : Γ(D.obj i, ⊤))
      (hx : (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range) :
      (D.map (h ≫ f)).appTop.hom x ∈ (α.app l).appTop.hom.range := by
    obtain ⟨y, hy⟩ := hx
    refine ⟨(E.map h).appTop y, ?_⟩
    have h₃ : (α.app l).appTop ((E.map h).appTop y) =
      (D.map h).appTop ((α.app j).appTop y) := congr(($((α.naturality h).symm)).appTop y)
    have h₄ : (D.map (h ≫ f)).appTop x = (D.map h).appTop ((D.map f).appTop x) :=
      congr(($(D.map_comp h f)).appTop x)
    exact h₃.trans ((congrArg _ hy).trans h₄.symm)
  have many (s : Finset Γ(D.obj i, ⊤)) : ∃ (j : I) (f : j ⟶ i), ∀ x ∈ s,
      (D.map f).appTop.hom x ∈ (α.app j).appTop.hom.range := by
    induction s using Finset.induction_on with
    | empty => exact ⟨i, 𝟙 i, by simp⟩
    | insert x s _ ih =>
      obtain ⟨j₁, f₁, h₁⟩ := ih
      obtain ⟨j₂, f₂, h₂⟩ := one x
      obtain ⟨l, g₁, g₂, eg⟩ := IsCofiltered.cospan f₁ f₂
      refine ⟨l, g₁ ≫ f₁, fun y hy ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [eg]; exact mono _ _ _ h₂
      · exact mono _ _ _ (h₁ y hy)
  have hft : (α.app i).appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  let _ := (α.app i).appTop.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  obtain ⟨j, f, hj⟩ := many s
  have : IsAffine (D.obj j) := isAffine_of_isAffineHom (D.map f)
  refine ⟨j, IsClosedImmersion.of_surjective_of_isAffine _ ?_⟩
  refine surjective_of_isPushout (isPushout_appTop_of_isPullback (hα f)) s ?_ hj
  exact (Algebra.adjoin_eq_ring_closure (s : Set Γ(D.obj i, ⊤))).symm.trans (congrArg Subalgebra.toSubring hs)

open GlobalTheory.Spread

section
variable {k : Type} [CommRing k] {X₀ Y₀ : Scheme.{0}} (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp k)

noncomputable def bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) : pullback (g₀ ≫ q) t ⟶ pullback q t :=
  pullback.lift (pullback.fst _ _ ≫ g₀) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])

theorem bcHom_fst {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g₀ := pullback.lift_fst _ _ _

@[reassoc]
theorem bcHom_snd {T : Scheme.{0}} (t : T ⟶ Sp k) :
    bcHom g₀ q t ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem isPullback_bcHom {T : Scheme.{0}} (t : T ⟶ Sp k) :
    IsPullback (pullback.fst (g₀ ≫ q) t) (bcHom g₀ q t) g₀ (pullback.fst q t) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q t) (v₂₂ := q) (h₃₁ := t) ?_
    (bcHom_fst g₀ q t).symm (.of_hasPullback _ _)
  rw [bcHom_snd]
  exact .of_hasPullback _ _

theorem isPullback_bcMap_bcHom {R A : Type} [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]
    (f : R →ₐ[k] A) :
    IsPullback (bcMap (g₀ ≫ q) f) (bcHom g₀ q _) (bcHom g₀ q _) (bcMap q f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (v₁₃ := g₀) (h₂₂ := pullback.fst _ _) ?_ ?_
    (isPullback_bcHom g₀ q _)
  · rw [bcMap_fst, bcMap_fst]
    exact isPullback_bcHom g₀ q _
  · apply pullback.hom_ext
    · rw [Category.assoc, bcHom_fst, bcMap_fst_assoc, Category.assoc, bcMap_fst, bcHom_fst]
    · rw [Category.assoc, bcHom_snd, bcMap_snd, Category.assoc, bcMap_snd, bcHom_snd_assoc]

theorem isClosedImmersion_of_isPullback {X Y X' Y' : Scheme.{0}} {g : X ⟶ Y} {πX : X ⟶ X₀}
    {πY : Y ⟶ Y₀} {g' : X' ⟶ Y'} {πX' : X' ⟶ X₀} {πY' : Y' ⟶ Y₀}
    (h : IsPullback πX g g₀ πY) (h' : IsPullback πX' g' g₀ πY') (m : Y' ⟶ Y) (hm : m ≫ πY = πY')
    [IsClosedImmersion g] : IsClosedImmersion g' := by
  subst hm
  have : IsPullback (h.lift πX' (g' ≫ m) (by rw [Category.assoc, h'.w])) g' g m :=
    IsPullback.of_right (by rw [h.lift_fst]; exact h') (h.lift_snd _ _ _) h
  exact MorphismProperty.of_isPullback this inferInstance

theorem exists_finset_bcHom (A : Type) [CommRing A] [Algebra k A] [IsAffine Y₀]
    [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀]
    [IsClosedImmersion (bcHom g₀ q (spMap (algebraMap k A)))] :
    ∃ s : Finset A, IsClosedImmersion
      (bcHom g₀ q (spMap (algebraMap k (Algebra.adjoin k (s : Set A))))) := by
  classical
  let α : bcDiagram (g₀ ≫ q) A ⟶ bcDiagram q A :=
    { app s := bcHom g₀ q _
      naturality s t f := (isPullback_bcMap_bcHom g₀ q _).w }
  have (s : (Finset A)ᵒᵖ) : IsAffine ((bcDiagram q A).obj s) :=
    inferInstanceAs (IsAffine (pullback q
      (spMap (algebraMap k (Algebra.adjoin k (s.unop : Set A))))))
  have (s : (Finset A)ᵒᵖ) : LocallyOfFiniteType (α.app s) :=
    MorphismProperty.of_isPullback (isPullback_bcHom g₀ q _) inferInstance
  have : @IsClosedImmersion (bcCone (g₀ ≫ q) A).pt (bcCone q A).pt
    (bcHom g₀ q (spMap (algebraMap k A))) := ‹_›
  obtain ⟨s, hs⟩ := exists_isClosedImmersion_of_isLimit _ _ α (bcCone (g₀ ≫ q) A) (bcCone q A)
    (isLimitBcCone _ _) (isLimitBcCone _ _) (fun f ↦ isPullback_bcMap_bcHom g₀ q _)
    (bcHom g₀ q (spMap (algebraMap k A))) (fun s ↦ (isPullback_bcMap_bcHom g₀ q _).w.symm)
  exact ⟨s.unop, hs⟩

end

theorem descends_of_isAffine (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0})
    (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [IsAffine Y₀] [QuasiCompact g₀] [QuasiSeparated g₀]
    [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S)
    (hY : IsPullback πY p q (spMap R₀.subtype)) (hX : IsPullback πX g g₀ πY)
    (hg : IsClosedImmersion g) :
    ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ →
      ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁),
        πY₁ ≫ q = p₁ ≫ spMap (Subring.inclusion h) → IsPullback πX₁ g₁ g₀ πY₁ →
          IsClosedImmersion g₁ := by
  have hY' : IsPullback πY p q (spMap (algebraMap R₀ S)) := hY
  have := isClosedImmersion_of_isPullback g₀ hX (isPullback_bcHom g₀ q (spMap (algebraMap R₀ S)))
    hY'.isoPullback.inv hY'.isoPullback_inv_fst
  obtain ⟨s, hs'⟩ := exists_finset_bcHom g₀ q S
  refine ⟨s, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  have hle : (Algebra.adjoin R₀ (s : Set S)).toSubring ≤ R₁ := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact h r.2
    | add x y _ _ hx hy => exact R₁.add_mem hx hy
    | mul x y _ _ hx hy => exact R₁.mul_mem hx hy
  let i : Algebra.adjoin R₀ (s : Set S) →+* R₁ := Subring.inclusion hle
  have hi : spMap i ≫ spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))) =
      spMap (Subring.inclusion h) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  exact isClosedImmersion_of_isPullback g₀
    (isPullback_bcHom g₀ q (spMap (algebraMap R₀ (Algebra.adjoin R₀ (s : Set S))))) hX₁
    (pullback.lift πY₁ (p₁ ≫ spMap i) (by rw [Category.assoc, hi, hY₁])) (pullback.lift_fst _ _ _)

theorem exists_isPullback_restrict {X₀ Y₀ X Y V : Scheme.{0}} {g₀ : X₀ ⟶ Y₀} {g : X ⟶ Y}
    {πX : X ⟶ X₀} {πY : Y ⟶ Y₀} (hX : IsPullback πX g g₀ πY) (j : V ⟶ Y₀) :
    ∃ m : pullback g (pullback.fst πY j) ⟶ pullback g₀ j,
      IsPullback m (pullback.snd _ _) (pullback.snd _ _) (pullback.snd πY j) := by
  have h := (IsPullback.of_hasPullback g (pullback.fst πY j)).paste_horiz hX
  rw [pullback.condition (f := πY)] at h
  refine ⟨pullback.lift (pullback.fst _ _ ≫ πX) (pullback.snd _ _ ≫ pullback.snd πY j)
    (by rw [h.w, Category.assoc]), ?_⟩
  exact IsPullback.of_right (by rw [pullback.lift_fst]; exact h) (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)

end GlobalTheory.ClosedLimit

namespace GlobalTheory


open ClosedLimit in
theorem isClosedImmersion_descends_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X₀ Y₀ X Y : Scheme.{0}) (g₀ : X₀ ⟶ Y₀) (q : Y₀ ⟶ Sp R₀) [QuasiCompact q] [QuasiCompact g₀] [QuasiSeparated g₀] [LocallyOfFiniteType g₀] (g : X ⟶ Y) (πX : X ⟶ X₀) (πY : Y ⟶ Y₀) (p : Y ⟶ Sp S), IsPullback πY p q (spMap R₀.subtype) → IsPullback πX g g₀ πY → IsClosedImmersion g → ∃ F : Finset S, ∀ (R₁ : Subring S) (h : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ Y₁ : Scheme.{0}) (g₁ : X₁ ⟶ Y₁) (πX₁ : X₁ ⟶ X₀) (πY₁ : Y₁ ⟶ Y₀) (p₁ : Y₁ ⟶ Sp R₁), IsPullback πY₁ p₁ q (spMap (Subring.inclusion h)) → IsPullback πX₁ g₁ g₀ πY₁ → IsClosedImmersion g₁ := by
  classical
  intro S _ R₀ X₀ Y₀ X Y g₀ q _ _ _ _ g πX πY p hY hX hg
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace q
  let 𝒰 := Y₀.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstance
  have key (i : 𝒰.I₀) := descends_of_isAffine S R₀ _ _ _ _ (pullback.snd g₀ (𝒰.f i)) (𝒰.f i ≫ q) _ _ _ _
    ((IsPullback.of_hasPullback πY (𝒰.f i)).flip.paste_vert hY)
    (exists_isPullback_restrict hX (𝒰.f i)).choose_spec inferInstance
  choose F hF using key
  refine ⟨Finset.univ.biUnion F, fun R₁ h hs X₁ Y₁ g₁ πX₁ πY₁ p₁ hY₁ hX₁ ↦ ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
    (𝒰.pullback₁ πY₁)).mpr fun i ↦ ?_
  exact hF i R₁ h
    ((Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem F (Finset.mem_univ (α := 𝒰.I₀) i))).trans hs) _ _ _ _ _ _
    ((IsPullback.of_hasPullback πY₁ (𝒰.f i)).flip.paste_vert hY₁).w
    (exists_isPullback_restrict hX₁ (𝒰.f i)).choose_spec

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsSquareDetComparisonEqMulDetPowOfBasisChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.BoxDetUnique

theorem isProper_powObj {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∀ n, IsProper (Out.powObj A n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => (AbelianSchemeGerms.isAbelianScheme_powObj A hA n).proper

theorem box_indep {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) {m : ℤ} {N : ℕ} (b : Fin N → LB.Sec (pw L m))
    (hb : ∀ c : Fin N → K, (∀ i, ∑ k, cst A.hom (L.U i) (c k) * (show Γ(A.left, L.U i) from (b k).f i) = 0) → c = 0) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → K), (∀ (y : (Out.powObj A n).left) J, Good L y J →
      ∑ I, kv (Out.powObj A n).hom y (q I) * ∏ c, gs (Out.powPr A c).left y (L.U (J (Out.powPr A c).left))
        ((b (I c)).f (J (Out.powPr A c).left)) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    let y : (Out.powObj A 0).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)
    have := hq y J hJ
    rw [Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero] at this
    exact funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this
  | succ n ih =>
    intro q hq
    haveI := hA.proper
    haveI := isProper_powObj A hA n
    choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K))
      (fun _ _ => b i)
    choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom
      (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))
    have H := (GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m)
      (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by
        have hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i) :=
          Set.mem_iInter.2 fun _ => hy
        have := congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))
        refine Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans
          ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))
        refine (gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)
        refine congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_
        rw [ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])
      (fun z J hJ => by
        refine Eq.trans ?_ (hq z J hJ)
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_
        rw [Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]
        rfl)
    funext I
    have := ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by
      have h1 := hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)
      have h0 := h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans
        (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))
      simpa only [Category.id_comp] using h0)
    have h2 := congrFun this (Fin.tail I)
    rwa [Fin.cons_self_tail] at h2

theorem isSquareDetComparison_eq_mul_det_pow_of_basis_change : Out.Laws → ∀ (K : Type) [Field K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b b' : Fin (m ^ x.P.g) → RR x m) (B : (Matrix (Fin (m ^ x.P.g)) (Fin (m ^ x.P.g)) K)ˣ) (lam lam' : Kˣ), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → IsBasis x b → (∀ k, Coords x b (fun k' => B.val k' k) (b' k).f) → IsSquareDeterminantComparison x m al b lam → IsSquareDeterminantComparison x m al b' lam' → lam' = lam * (Matrix.GeneralLinearGroup.det B) ^ (-8 * (m ^ (3 * x.P.g + 2) : ℕ) : ℤ) := by
  intro laws K _ x m al b b' B lam lam' hm hal hb hB
    ⟨ξ, mu, w, Q, rho, hne, hker, hmu, hw, hn, hQ, hlam⟩ ⟨ξ', mu', w', Q', rho', hne', hker', hmu', hw', hn', hQ', hlam'⟩
  have inj : ∀ ζ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x,
      (∀ I I', I ≠ I' → ∀ p : Sp K, ∃ r, (ζ I r).left p ≠ (ζ I' r).left p) → Function.Injective ζ := by
    intro ζ h I I' e
    by_contra hI
    obtain ⟨r, hr⟩ := h I I' hI (IsLocalRing.closedPoint K)
    exact hr (by rw [e])
  obtain ⟨σ, rfl⟩ := exists_perm laws.mulN x.P m al hm hal ξ ξ' (inj _ hne) (inj _ hne') hker hker'
  have hL := x.P.isLB
  have hmm : ∀ (Z : Scheme.{0}) (r : Z ⟶ x.P.A.left) (z : Z) (J), Good x.P.L z J → val mu' r z J = val mu r z J := by
    haveI := x.P.isAb.comm
    exact gen_unique hL (S₀ := Sp K) x.P.A.hom (eSec x.P.A) (Over.w η[x.P.A]) (laws.globalFns _ _ x.P.isAb).2 hmu' hmu
      (fun y J hJ => (hn' y J hJ).1.trans (hn y J hJ).1.symm)
  choose c hc using fun I => gen_ratio hL (Out.powObj x.P.A 4).hom
    (laws.globalFns _ _ (AbelianSchemeGerms.isAbelianScheme_powObj _ x.P.isAb 3)).2 (hw (σ I)) (hw' I)
  have hr : ∀ I, (rho' I : K) = c I ^ (m ^ 2) * rho (σ I) := by
    intro I
    let p : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (𝟙_ (Over (Sp K))).left ⟶ x.P.A.left => exists_chart hL (χ p)
    have h1 := (hn p J hJ).2 (σ I)
    have h2 := (hn' p J hJ).2 I
    simp only [hmm _ _ p J hJ] at h2
    rw [Units.val_mul, Units.val_pow_eq_pow_val, gs_cst _ _ p ⊤ trivial, Category.comp_id] at h1 h2
    rw [hc I _ _ p J hJ, mul_pow, _root_.mul_assoc, h1, ← _root_.mul_assoc, Units.mul_left_inj,
      show eSec (Out.powObj x.P.A 4) ≫ (Out.powObj x.P.A 4).hom = (𝟙_ (Over (Sp K))).hom from Over.w η[Out.powObj x.P.A 4],
      ← map_pow, ← map_mul] at h2
    exact ((kv _ p).injective h2).symm
  have hind := box_indep x.P.A x.P.isAb hL b (fun c hc => by
    obtain ⟨c₀, -, hu⟩ := hb ⟨fun _ => 0, fun i j => by rw [map_zero, map_zero, mul_zero]⟩
    exact (hu c fun i => (hc i).symm).trans (hu 0 fun i =>
      (Finset.sum_eq_zero fun k _ => by rw [Pi.zero_apply, map_zero, zero_mul]).symm).symm) 4
  have hq : ∀ I I', Q (σ I) I' = c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d := by
    intro I I'
    refine sub_eq_zero.1 (congrFun (hind (fun I' => Q (σ I) I' - c I * ∑ d, Q' I d *
      (Matrix.of fun (I I' : Fin (3 + 1) → Fin (m ^ x.P.g)) => ∏ c, B.val (I c) (I' c)) I' d) fun y J hJ => ?_) I')
    have h1 := (hQ (σ I) y J hJ).symm.trans (hQ' I y J hJ)
    rw [hc I _ _ y J hJ, mul_comm (kv _ _ _), _root_.mul_assoc, Units.mul_right_inj] at h1
    simp only [gs_cst _ _ y ⊤ trivial, Category.id_comp] at h1
    have h3 : ∀ (r : (Out.powObj x.P.A 4 ⟶ x.P.A)) k, gs r.left y (x.P.L.U (J r.left)) ((b' k).f (J r.left)) =
        ∑ k', kv (Out.powObj x.P.A 4).hom y (B.val k' k) * gs r.left y (x.P.L.U (J r.left)) ((b k').f (J r.left)) := by
      intro r k
      refine (congrArg (gs r.left y (x.P.L.U (J r.left))) (hB k (J r.left))).trans ?_
      refine (gs_sum' _ y _ (hJ _) _ _).trans (Finset.sum_congr rfl fun k' _ => ?_)
      rw [gs_mul _ y _ (hJ _), gs_cst _ _ y _ (hJ _), Over.w r]
    simp only [h3] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, h1, map_mul, map_sum, Matrix.of_apply, map_prod,
      _root_.mul_assoc, ← Finset.mul_sum]
    rw [sub_eq_zero]
    congr 1
    simp only [Finset.sum_mul, _root_.mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum, Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp only [Finset.prod_mul_distrib]
  have key := det_calc σ Q Q' _ c (fun I => rho I) (fun I => rho' I) (m ^ 2) hq hr
  rw [← hlam, ← hlam', GlobalTheory.det_kroneckerPower, ← pow_mul] at key
  have e : lam = lam' * (Matrix.GeneralLinearGroup.det B) ^ (8 * m ^ (3 * x.P.g + 2)) := by
    apply Units.ext
    rw [key, Units.val_mul, Units.val_pow_eq_pow_val]
    congr 2
    ring
  rw [e, _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
  simp

end GlobalTheory.BoxDetUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory

private lemma spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem morphism_descends_to_subring :
    ∀ (R : Type) [CommRing R] (R₀ : Subring R) (X X₀ Y₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp R₀) (q : Y₀ ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation q] (φ : X ⟶ Y₀), IsPullback π f f₀ (spMap R₀.subtype) → φ ≫ q = π ≫ f₀ → ∃ S : Finset R, ∀ (R₁ : Subring R) (h : R₀ ≤ R₁), (S : Set R) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion h)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Y₀, j ≫ ψ = φ ∧ ψ ≫ q = π₁ ≫ f₀ := by
  intro R _ R₀ X X₀ Y₀ f f₀ q π _ _ _ φ hP hφ
  let _ : Algebra R₀ R := R₀.subtype.toAlgebra
  have hP' : IsPullback π f f₀ (spMap (algebraMap R₀ R)) := hP

  let e := hP'.isoPullback
  obtain ⟨R', ψ', hfg, hψ'q, hψ'φ⟩ := Spread.exists_fg_comp_eq (pB := f₀) (pZ := q) (A := R)
    (e.inv ≫ φ) (by rw [Category.assoc, hφ, ← Category.assoc, hP'.isoPullback_inv_fst])
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun R₁ h hS X₁ f₁ π₁ j hP₁ hjπ hjf => ?_⟩

  have hle : ∀ x ∈ R', x ∈ R₁ := by
    let T : Subalgebra R₀ R := { R₁.toSubsemiring with algebraMap_mem' := fun r => h r.2 }
    have hT : R' ≤ T := ht ▸ Algebra.adjoin_le hS
    exact fun x hx => hT hx
  let a : R' →+* R₁ := RingHom.codRestrict R'.val.toRingHom R₁ (fun x => hle x x.2)
  have ha : spMap a ≫ spMap (algebraMap R₀ R') = spMap (Subring.inclusion h) := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  have hb : spMap R₁.subtype ≫ spMap a = spMap R'.val.toRingHom := by
    rw [spMap_comp_moduli_spaces]
    congr 1
  let L : X₁ ⟶ pullback f₀ (spMap (algebraMap R₀ R')) :=
    pullback.lift π₁ (f₁ ≫ spMap a) (by rw [Category.assoc, ha]; exact hP₁.w)
  refine ⟨L ≫ ψ', ?_, ?_⟩
  · have hjL : j ≫ L = e.hom ≫ Spread.bcMap f₀ R'.val := by
      apply pullback.hom_ext
      · simp only [L, e, Category.assoc, Spread.bcMap_fst, IsPullback.isoPullback_hom_fst]
        rw [pullback.lift_fst, hjπ]
      · simp only [L, e, Category.assoc, pullback.lift_snd, Spread.bcMap_snd,
          IsPullback.isoPullback_hom_snd_assoc]
        rw [← Category.assoc, hjf, Category.assoc, hb]
    rw [← Category.assoc, hjL, Category.assoc, hψ'φ, ← Category.assoc, e.hom_inv_id,
      Category.id_comp]
  · rw [Category.assoc, hψ'q, ← Category.assoc, pullback.lift_fst]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PullbackSectionsBasisOfAffineOpensStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackSections_basis_of_affine_opens : ∀ (X Y T : Scheme.{0}) (L : LB X) (t : ℤ) (N : ℕ) (b : Fin N → LB.Sec (pw L t)) (p₁ : Y ⟶ T) (p₂ : Y ⟶ X), (∀ W : T.Opens, IsAffineOpen W → GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W) → ∀ W : T.Opens, GlobalTheory.RelBasis.IndepOn b p₁ p₂ W ∧ GlobalTheory.RelBasis.SpanOn b p₁ p₂ W := by
  first | exact @GlobalTheory.RelBasis.basis_of_affine | exact GlobalTheory.RelBasis.basis_of_affine | (intros; apply GlobalTheory.RelBasis.basis_of_affine <;> assumption)
end

