module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0043
public import Development.EtaleCohomology.EtaleSheaves.Bundle0052
public import Development.EtaleCohomology.EtaleSheaves.Bundle0050
public import Development.EtaleCohomology.EtaleSheaves.Bundle0002
public import Development.EtaleCohomology.EtaleSheaves.Bundle0051
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044
public import Development.EtaleCohomology.EtaleSheaves.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.AugHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationSheaf

variable (q : ℕ)

def CP : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) where
  obj U := ModuleCat.of _ C(U.unop, ULift.{1} (ZMod q))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ContinuousMap.comp g f.unop.base.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem isSheaf_etaleTopology_continuousMaps : Presheaf.IsSheaf Scheme.etaleTopology.{0} (CP q) := by
  apply Presheaf.IsSheaf.of_le (le_trans Scheme.etaleTopology_le_proetaleTopology Scheme.proetaleTopology_le_fpqcTopology)
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) :=
    reflectsLimitsOfSize_shrink.{1, 1, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q))))
  exact isSheaf_fpqcTopology_continuousMapPresheaf (ULift.{1} (ZMod q))

def augA (U : Scheme.{0}) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U) →ₗ[ULift.{1} (ZMod q)] C(U, ULift.{1} (ZMod q)) :=
  (twRel q 0 Γ(U, ⊤)).liftQ (Finsupp.linearCombination _ (fun _ => (1 : C(U, ULift.{1} (ZMod q))))) (by
    refine Submodule.span_le.2 ?_
    rintro x ⟨ζ, ξ, a, -, rfl⟩
    simp)

def augP : Scheme.Γ ⋙ twF q 0 ⟶ CP q where
  app U := ModuleCat.ofHom (augA q U.unop)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply Submodule.linearMap_qext
    apply Finsupp.lhom_ext
    intro ζ c
    apply ContinuousMap.ext; intro t
    erw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    change (augA q V.unop) (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.unop.appTop.hom) (Finsupp.single ζ c))) t =
      (augA q U.unop (Submodule.Quotient.mk (Finsupp.single ζ c))) (f.unop.base t)
    simp only [augA]
    erw [Submodule.liftQ_apply, Submodule.liftQ_apply, Finsupp.mapDomain_single, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single]
    rfl

def augS : sheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0) ⟶ CP q :=
  sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q)

def augC (T : Scheme.{0}) (x : Sec (tw q 0) T) : C(T, ULift.{1} (ZMod q)) := ((augS q).app (Opposite.op T)).hom x

def aug (T : Scheme.{0}) : Sec (tw q 0) T →+ LocallyConstant T (ZMod q) :=
  AddMonoidHom.mk' (fun x => ⟨fun t => (augC q T x t).down,
      (IsLocallyConstant.iff_continuous _).2 (continuous_uliftDown.comp (ContinuousMap.continuous _))⟩)
    (fun x y => by
      ext t
      simp only [LocallyConstant.coe_add, Pi.add_apply, LocallyConstant.coe_mk, augC]
      erw [LinearMap.map_add]
      rfl)

theorem aug_nat {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U) :
    aug q V (Sec.res g x) = (aug q U x).comap g.base.hom := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom h) x) ((augS q).naturality g.op)
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_comap, Function.comp_apply]
  exact congrArg (fun k : C(V, ULift.{1} (ZMod q)) => (k t).down) h

theorem aug_gen (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) : aug q U (twGen 0 ζ) = 1 := by
  have h := congrArg (fun h => (ModuleCat.Hom.hom (NatTrans.app h (Opposite.op U))) (Submodule.Quotient.mk (Finsupp.single ζ 1)))
    (toSheafify_sheafifyLift Scheme.etaleTopology.{0} (augP q) (isSheaf_etaleTopology_continuousMaps q))
  ext t
  simp only [aug, AddMonoidHom.mk'_apply, LocallyConstant.coe_mk, LocallyConstant.coe_one, Pi.one_apply]
  have h2 := congrArg (fun k : C(U, ULift.{1} (ZMod q)) => (k t).down) h
  refine h2.trans ?_
  simp only [augP, augA]
  erw [ModuleCat.hom_ofHom, Submodule.liftQ_apply, Finsupp.linearCombination_single]
  simp

theorem Aug_holds : LateralTheory.E.TateTwistZeroAugmentationBijective.Aug := fun q => ⟨aug q, fun g x => aug_nat q g x, aug_gen q⟩

theorem Tw0_of (hB : LateralTheory.E.TateTwistZeroAugmentationBijective.AugBij) : LateralTheory.E.LCIsoPf.Tw0 := LateralTheory.E.TateTwistZeroAugmentationBijective.Tw0_of Aug_holds hB

end LateralTheory.E.TateTwistZeroAugmentationSheaf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.TruncCokPf Opposite

namespace LateralTheory.E.LevelsPf

def CechLevel : Prop := ∀ (p : ℕ) {D E Y' Y'' : CommRingCat.{0}} (e : D ⟶ E) (φ' : D ⟶ Y') (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (hpo : IsPushout φ' e u φ''),
    ∃ (Ep Yp : CommRingCat.{0}) (dp : D ⟶ Ep) (wp : Y' ⟶ Yp) (φp : Ep ⟶ Yp), IsPushout φ' dp wp φp ∧
      (∀ {A : CommRingCat.{0}} (d : A ⟶ D) (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop), PushClosed P → P D d →
        P E (d ≫ e) → P Ep (d ≫ dp)) ∧
      Nonempty (Arrow.mk ((Arrow.mapCechNerve (sq e φ' u φ'' hpo.w)).app (op (SimplexCategory.mk p))) ≅
        Arrow.mk (yoneda.map (Spec.map φp)))

theorem pull_iso_bij (R : Type) [CommRing R] {E E' : Spc} (a : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R a.hom F n) := by
  have h1 : ∀ x, pull R a.inv F n (pull R a.hom F n x) = x := fun x => by
    rw [← pull_comp, Iso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R a.hom F n (pull R a.inv F n x) = x := fun x => by
    rw [← pull_comp, Iso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem transfer (R : Type) [CommRing R] (F : Shv R) {P Q P' Q' : PSh} (f : P ⟶ Q) (g : P' ⟶ Q')
    (α : Arrow.mk f ≅ Arrow.mk g) (n : ℤ) :
    (Function.Surjective (pull R (disc.map g) F n) → Function.Surjective (pull R (disc.map f) F n)) ∧
    (Function.Injective (pull R (disc.map g) F n) → Function.Injective (pull R (disc.map f) F n)) := by
  let αl : P ≅ P' := Arrow.leftFunc.mapIso α
  let αr : Q ≅ Q' := Arrow.rightFunc.mapIso α
  have hw : f ≫ αr.hom = αl.hom ≫ g := by
    exact (Arrow.w α.hom).symm
  have hf : f = αl.hom ≫ g ≫ αr.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]; exact hw
  have he : ⇑(pull R (disc.map f) F n) =
      pull R (disc.mapIso αl).hom F n ∘ pull R (disc.map g) F n ∘ pull R (disc.mapIso αr).symm.hom F n := by
    funext x
    rw [hf, Functor.map_comp, Functor.map_comp, pull_comp, pull_comp]; rfl
  have bl := pull_iso_bij R (disc.mapIso αl) F n
  have br := pull_iso_bij R (disc.mapIso αr).symm F n
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · rw [he]; exact bl.2.comp (hs.comp br.2)
  · rw [he]; exact bl.1.comp (hi.comp br.1)

theorem Levels_of (hC : CechLevel) : LateralTheory.E.TruncCokPf.Levels := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  obtain ⟨Ep, Yp, dp, wp, φp, hpp, hP, ⟨α⟩⟩ := hC p e φ' u φ'' hpo'
  have hsq : IsPushout φ (d ≫ dp) (w ≫ wp) φp := hpo.paste_vert hpp
  have hrel : RelZ q i m φp := hlow m hm Ep (d ≫ dp) (hP d P hpush hD hE) Yp (w ≫ wp) φp hsq
  have ht := fun k => transfer (ZMod q) (tw q i) _ _ α k
  refine ⟨fun k hk => (ht k).1 (hrel.1 k hk), (ht m).2 hrel.2⟩

end LateralTheory.E.LevelsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CurveUnitsOrderAtInfinity
section
open Polynomial IntermediateField.algebraAdjoinAdjoin

namespace LateralTheory.E.CurveUnitsOrderAtInfinity

theorem minpolyCoeff : LateralTheory.E.E4.LeafMinpolyCoeff := by
  intro k L _ _ _ s hs F hF x hx i
  subst hF
  have : UniqueFactorizationMonoid (Algebra.adjoin k {s}) := hs.uniqueFactorizationMonoid_adjoin
  have : IsIntegrallyClosed (Algebra.adjoin k {s}) := inferInstance
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' (IntermediateField.adjoin k {s}) hx, coeff_map]
  exact ((minpoly (Algebra.adjoin k {s}) x).coeff i).2

theorem ordInfHom : LateralTheory.E.E4.LeafOrdInfHom :=
  LateralTheory.E.E4.LeafOrdInfHom_of_local (LateralTheory.E.E4.LeafOrdInfLocal_of' LateralTheory.E.E4.LeafFinInf_of LateralTheory.E.E4.LeafFinVal_of)

theorem LeafUnits_of : LateralTheory.E.E4.LeafUnits :=
  LateralTheory.E.E4.LeafUnits_of (LateralTheory.E.E4.LeafUnitsFG_of_dim LateralTheory.E.E4.LeafNoetherDim_of
    (LateralTheory.E.E4.LeafOrdAtInfinity_of_cut ordInfHom minpolyCoeff))

end LateralTheory.E.CurveUnitsOrderAtInfinity
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FiltrationLevelInjectivity
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.FiltrationLevelInjectivity

def gN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') : cech (Spec.map u) ⟶ cech (Spec.map e) :=
  Arrow.mapCechNerve (f := Arrow.mk (yoneda.map (Spec.map u))) (g := Arrow.mk (yoneda.map (Spec.map e)))
    ⟨yoneda.map (Spec.map φ''), yoneda.map (Spec.map φ'), by
      simp only [Arrow.mk_hom, Functor.id_map, Functor.id_obj, Arrow.mk_left, Arrow.mk_right,
        ← Functor.map_comp, ← Spec.map_comp, h]⟩

def iN {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app _ := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality := by
    intro x y θ
    apply WidePullback.hom_ext
    · intro j
      erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, WidePullback.lift_π]
      exact Category.id_comp _
    · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, WidePullback.lift_base]
      exact Category.id_comp _

theorem iN_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : iN f ≫ cechAug f = sch.map f := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem iN_app_zero_iso {Y X : Scheme.{0}} (f : Y ⟶ X) : IsIso ((iN f).app (op ⦋0⦌)) := by
  refine ⟨⟨WidePullback.π (fun _ : Fin 1 => yoneda.map f) 0, ?_, ?_⟩⟩
  · erw [WidePullback.lift_π]
  · apply WidePullback.hom_ext
    · intro j
      have hj : j = 0 := Fin.fin_one_eq_zero j
      subst hj
      erw [Category.assoc, WidePullback.lift_π, Category.id_comp]
      exact Category.comp_id _
    · erw [Category.assoc, WidePullback.lift_base, Category.id_comp]
      exact WidePullback.π_arrow _ _

theorem gN_aug {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    gN φ' e u φ'' h ≫ cechAug (Spec.map e) = cechAug (Spec.map u) ≫ sch.map (Spec.map φ') := by
  refine NatTrans.ext (funext fun x => ?_)
  erw [NatTrans.comp_app, WidePullback.lift_base]
  rfl

theorem gN_iN {D Y' E Y'' : CommRingCat.{0}} (φ' : D ⟶ Y') (e : D ⟶ E) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y'')
    (h : φ' ≫ u = e ≫ φ'') :
    sch.map (Spec.map φ'') ≫ iN (Spec.map e) = iN (Spec.map u) ≫ gN φ' e u φ'' h := by
  have hw : yoneda.map (Spec.map φ'') ≫ yoneda.map (Spec.map e) = yoneda.map (Spec.map u) ≫ yoneda.map (Spec.map φ') := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp, h]
  refine NatTrans.ext (funext fun x => ?_)
  apply WidePullback.hom_ext
  · intro j
    erw [Category.assoc, WidePullback.lift_π, Category.assoc, WidePullback.lift_π, ← Category.assoc,
      WidePullback.lift_π, Category.id_comp]
    exact Category.comp_id _
  · erw [Category.assoc, WidePullback.lift_base, Category.assoc, WidePullback.lift_base, ← Category.assoc,
      WidePullback.lift_base]
    exact hw

def Filt : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X)
  (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X) (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g),
  IsIso (a.app (op ⦋0⦌)) → IsIso (b.app (op ⦋0⦌)) →
  (∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n → Function.Injective (pull R (disc.map (g.app (op ⦋p⦌))) F m) ∧
    Function.Surjective (pull R (disc.map (g.app (op ⦋p⦌))) F (m - 1))) →
  Function.Injective (rpull R g (disc.map h) b a comm F n)

def LvlRel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo : IsPushout φ' e u φ'',
  ∀ p : ℕ, 1 ≤ p → ∀ m : ℤ, m < n →
    Function.Injective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) m) ∧
    Function.Surjective (pull (ZMod q) (disc.map ((gN φ' e u φ'' hpo.w).app (op ⦋p⦌))) (tw q i) (m - 1))

theorem LevelInj_of (hF : Filt) (hL : LvlRel) : LateralTheory.E.RelDescPf.LevelInj := by
  intro hH q _ i n A Y φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo'
  refine ⟨gN φ' e u φ'' hpo'.w, gN_aug _ _ _ _ _, iN (Spec.map e), iN (Spec.map u), gN_iN _ _ _ _ _,
    iN_aug _, iN_aug _, ?_⟩
  exact hF hH (ZMod q) (tw q i) n (gN φ' e u φ'' hpo'.w) (yoneda.map (Spec.map φ'')) (iN (Spec.map e))
    (iN (Spec.map u)) (gN_iN _ _ _ _ _) (iN_app_zero_iso _) (iN_app_zero_iso _)
    (hL hH q i n φ hq P hP hE hB D d hD Y' w φ' hpo E e Y'' u φ'' he hs hPE hpo')

end LateralTheory.E.FiltrationLevelInjectivity
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HasLimPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.HasLimPf

theorem hasLimit_of_affine {K : Type} [SmallCategory K] (F : K ⥤ Scheme.{0}) (hF : ∀ k, IsAffine (F.obj k)) :
    HasLimit F := by
  have : HasLimit (F ⋙ Scheme.Γ.rightOp) := inferInstance
  have : PreservesLimitsOfSize.{0, 0} Scheme.Spec.{0} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  have : HasLimit (F ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec) :=
    HasLimit.mk ⟨_, isLimitOfPreserves Scheme.Spec (limit.isLimit (F ⋙ Scheme.Γ.rightOp))⟩
  have : ∀ k, IsIso ((Functor.whiskerLeft F ΓSpec.adjunction.unit).app k) := fun k => by
    have := hF k
    dsimp; infer_instance
  have : IsIso (Functor.whiskerLeft F ΓSpec.adjunction.unit) := NatIso.isIso_of_isIso_app _
  exact hasLimit_of_iso (asIso (Functor.whiskerLeft F ΓSpec.adjunction.unit)).symm

def Loc : Prop := ∀ {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (j₀ : J),
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) →
  (∀ U : (D.obj j₀).Opens, IsAffineOpen U → HasLimit (opensDiagram D j₀ U)) → HasLimit (Over.forget j₀ ⋙ D)

theorem HasLim_of (hL : Loc) : LateralTheory.E.SysPf.HasLim := by
  intro J _ _ D hD
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  have : HasLimit (Over.forget j₀ ⋙ D) := hL D j₀ hD (fun U hU => by
    refine hasLimit_of_affine _ (fun j => ?_)
    have := hD j.hom
    exact hU.preimage (D.map j.hom))
  have : HasLimit D := Functor.Initial.hasLimit_of_comp (Over.forget j₀)
  exact ⟨limit.cone D, ⟨limit.isLimit D⟩⟩

end LateralTheory.E.HasLimPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IsClosedImmersionOfCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.CorePf2

theorem isClosedImmersion_of_cover {X Y : Scheme.{0}} (f : X ⟶ Y) {ι : Type} (O : ι → Y.Opens)
    (hcl : IsClosed (Set.range f)) (hcov : Set.range f ⊆ ⋃ i, (O i : Set Y))
    (hloc : ∀ i, IsClosedImmersion (f ∣_ O i)) : IsClosedImmersion f := by
  let O' : Option ι → Y.Opens := fun o => o.elim ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩ O
  refine IsZariskiLocalAtTarget.of_iSup_eq_top O' ?_ ?_
  · rw [eq_top_iff]
    intro y _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases hy : y ∈ Set.range f
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
      exact ⟨some i, hi⟩
    · exact ⟨none, hy⟩
  · intro o
    cases o with
    | none =>
      have : IsEmpty (f ⁻¹ᵁ O' none).toScheme := ⟨fun x => x.2 ⟨x.1, rfl⟩⟩
      infer_instance
    | some i => exact hloc i

theorem range_closed {S X₁ P : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁] (q : P ⟶ S) {V : Scheme.{0}}
    (γ : V ⟶ pullback p₁ q) : IsClosed (Set.range (γ.imageι ≫ pullback.snd p₁ q)) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (pullback.snd p₁ q).isClosedMap _ γ.imageι.isClosedEmbedding.isClosed_range

end LateralTheory.E.CorePf2

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDescendChainPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendChainPf

def PreChain {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) {C0 C1 C2 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) {D0 D1 D2 : Scheme.{0}} (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0)
    (d2 : D2 ⟶ D1) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2) : Prop :=
  (LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q) ∧
  (LocallyOfFinitePresentation (d1 ≫ q) ∧ QuasiCompact (d1 ≫ q) ∧ QuasiSeparated (d1 ≫ q)) ∧
  (LocallyOfFinitePresentation (d2 ≫ d1 ≫ q) ∧ QuasiCompact (d2 ≫ d1 ≫ q) ∧ QuasiSeparated (d2 ≫ d1 ≫ q)) ∧
  IsPullback v0 c0 q (toR R) ∧ IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (toR R) ∧
  IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (toR R) ∧ γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2

def LeafDescendFP : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {C0 : Scheme.{0}}
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 → ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1),
    IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2), PreChain R c0 γ1 γ2 q d1 d2 v0 v1 v2

end LateralTheory.E.LeafDescendChainPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDimBoundPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.LeafDimBoundPf

theorem dim_le_of_quasiFinite (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.QuasiFinite A S] : ringKrullDim S ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A S)) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := hPQ.le
  refine lt_of_le_of_ne (fun x hx => hle hx) ?_
  intro h
  apply hPQ.ne
  have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) P.asIdeal Q.asIdeal hle
    (congrArg PrimeSpectrum.asIdeal h)
  exact PrimeSpectrum.ext this

theorem dim_le_of_stdSmooth1 (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R S] : ringKrullDim S ≤ ringKrullDim R + 1 := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := 1) R S
  let _ : Algebra (MvPolynomial (Fin 1) R) S := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin 1) R) S := hg
  have h1 := dim_le_of_quasiFinite (MvPolynomial (Fin 1) R) S
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing] at h1
  simpa using h1

theorem dim_affineOpen {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    topologicalKrullDim (V : Set X) = ringKrullDim Γ(X, V) := by
  have h1 : topologicalKrullDim (V : Set X) = topologicalKrullDim (Spec Γ(X, V)) :=
    (Scheme.homeoOfIso hV.isoSpec).isHomeomorph.topologicalKrullDim_eq
  rw [h1]
  exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _

theorem dim_affineOpen_Spec_le (A : CommRingCat.{0}) {U : (Spec A).Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(Spec A, U) ≤ ringKrullDim A := by
  rw [← dim_affineOpen hU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := A)]
  exact topologicalKrullDim_subspace_le _ _

theorem LeafDimBound_of : LateralTheory.E.LeafDescendVCut.LeafDimBound := by
  intro k _ Ω _ _ R hR D0 q hq
  have : IsNoetherianRing R := isNoetherianRing_of_fg hR
  apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := hq.exists_isStandardSmoothOfRelativeDimension x
  have : IsNoetherianRing Γ(Sp R, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let _ : Algebra Γ(Sp R, U) Γ(D0, V) := (q.appLE U V e).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Sp R, U) Γ(D0, V) := hs
  refine ⟨(V : Set D0), V.isOpen, hx, ?_⟩
  rw [dim_affineOpen hV]
  calc ringKrullDim Γ(D0, V) ≤ ringKrullDim Γ(Sp R, U) + 1 := dim_le_of_stdSmooth1 _ _
    _ ≤ ringKrullDim R + 1 := by
      gcongr
      exact dim_affineOpen_Spec_le (CommRingCat.of R) hU

end LateralTheory.E.LeafDimBoundPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafIrredPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafIrredPf

lemma mem_range {C0 D0 S T : Scheme.{0}} {v0 : C0 ⟶ D0} {c0 : C0 ⟶ T} {q : D0 ⟶ S} {t : T ⟶ S}
    (h : IsPullback v0 c0 q t) (x : D0) (y : T) (hxy : q x = t y) : x ∈ Set.range v0 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := q) (g := t) x y hxy
  refine ⟨h.isoPullback.inv z, ?_⟩
  rw [← hz, ← h.isoPullback_inv_fst]
  rfl

lemma spec_gen {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (y : Sp Ω) (p : Sp R) :
    toR R y ⤳ p := by
  apply (PrimeSpectrum.le_iff_specializes (R := R) ((toR R) y) p).mp
  intro a ha
  have hA : (toR R).base y = PrimeSpectrum.comap (algebraMap R Ω) y := by
    rw [Spec.map_base]; rfl
  change a ∈ ((toR R).base y).asIdeal at ha
  rw [hA] at ha
  let y' : PrimeSpectrum Ω := y
  have ha' : algebraMap R Ω a ∈ y'.asIdeal := ha
  rw [Ideal.eq_bot_of_prime y'.asIdeal, Ideal.mem_bot] at ha'
  have ha := ha'
  have : a = 0 := Subtype.ext (by simpa using ha)
  rw [this]; exact p.asIdeal.zero_mem

theorem LeafIrred_of : LeafIrred := by
  intro k _ Ω _ _ R _ C0 D0 c0 q v0 hc hq h
  obtain ⟨hint, -, -⟩ := hc
  have := hint
  have := hq
  have : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  have : UniversallyOpen q := UniversallyOpen.of_flat q
  have : IrreducibleSpace C0 := irreducibleSpace_of_isIntegral C0
  have hirr : IsIrreducible (Set.range v0) := by
    simpa [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ C0).image v0 v0.continuous.continuousOn
  have hdense : Dense (Set.range v0) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hx⟩
    obtain ⟨c⟩ := (inferInstance : Nonempty C0)
    have hopen : IsOpen (q '' U) := q.isOpenMap U hU
    have hmem : toR R (c0 c) ∈ q '' U := (spec_gen R (c0 c) (q x)).mem_open hopen ⟨x, hx, rfl⟩
    obtain ⟨x', hx'U, hx'⟩ := hmem
    exact ⟨x', hx'U, mem_range h x' (c0 c) hx'⟩
  have : IsIrreducible (Set.univ : Set D0) := by
    rw [← hdense.closure_eq]; exact hirr.closure
  exact { isPreirreducible_univ := this.2, toNonempty := ⟨this.1.some⟩ }

end LateralTheory.E.LeafIrredPf
end
end

