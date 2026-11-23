module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompOpenImmersionOfQuasiFinite
section
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
namespace GlobalTheory.ZMTFin

theorem exists_glued_map (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α) :
    ∃ g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued,
      g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase ∧
      ∀ V, (relativeGluingData hα).cover.f V ≫ g =
        Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V := by
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  let η : (relativeGluingData hα).functor ⟶ (relativeGluingData hα').functor :=
    { app V := Spec.map (ι.app (Opposite.op V))
      naturality U V i := by
        dsimp [relativeGluingData]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        exact (ι.naturality i.op).symm }
  refine ⟨colimMap η, ?_, ?_⟩
  · apply colimit.hom_ext; intro V
    rw [ι_colimMap_assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Scheme.Cover.RelativeGluingData.ι_toBase]
    subst hι
    show Spec.map (ι.app _) ≫ (Spec.map (α'.app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι =
      (Spec.map ((α' ≫ ι).app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι
    rw [NatTrans.comp_app, Spec.map_comp]; exact (Category.assoc _ _ _).symm
  · intro V
    exact ι_colimMap η V

theorem isIso_morphismRestrict_iSup {Z T : Scheme.{0}} (g : Z ⟶ T) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsIso (g ∣_ W i)) : IsIso (g ∣_ ⨆ i, W i) := by
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
  refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
  have : Scheme.Opens.ι _ ''ᵁ (𝒰.f x).opensRange = W x := by
    simp only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp, Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
  convert! hW x

theorem isOpenImmersion_comp_of_isIso_restrict {U Z T : Scheme.{0}} (h : U ⟶ Z) (g : Z ⟶ T)
    (W : T.Opens) [IsOpenImmersion h] (hg : IsIso (g ∣_ W)) (hr : Set.range h ⊆ (g ⁻¹ᵁ W : Set Z)) :
    IsOpenImmersion (h ≫ g) := by
  let h' : U ⟶ (g ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι h (by simpa using hr)
  have e : h = h' ≫ (g ⁻¹ᵁ W).ι := (IsOpenImmersion.lift_fac _ _ _).symm
  have : IsOpenImmersion (h' ≫ (g ⁻¹ᵁ W).ι) := by rw [← e]; infer_instance
  have : IsOpenImmersion h' := IsOpenImmersion.of_comp h' (g ⁻¹ᵁ W).ι
  rw [e, Category.assoc, ← morphismRestrict_ι]
  infer_instance

theorem toBase_of_Spec (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V, P (Spec.map (α'.app V))) : P (relativeGluingData h).toBase := by
  haveI : ((relativeGluingData h).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let V0 : X.AffineZariskiSite := ⟨U.1, U.2⟩
  haveI : IsOpenImmersion ((relativeGluingData h).cover.f V0) := (relativeGluingData h).cover.map_prop V0
  have hpre : (relativeGluingData h).toBase ⁻¹ᵁ U.1 =
      ((relativeGluingData h).cover.f V0).opensRange := by
    simpa using! (relativeGluingData h).toBase_preimage_eq_opensRange_ι V0
  let e := IsOpenImmersion.isoOfRangeEq ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι
    ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre])
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono hU.fromSpec := inferInstance
  have key : e.inv ≫ ((relativeGluingData h).toBase ∣_ U.1) ≫ hU.isoSpec.hom =
      Spec.map (α'.app (Opposite.op V0)) := by
    apply (cancel_mono hU.fromSpec).mp
    have := (relativeGluingData h).ι_toBase V0
    simp [IsAffineOpen.isoSpec_hom, e]
    refine (congrArg (· ≫ (relativeGluingData h).toBase) (IsOpenImmersion.isoOfRangeEq_inv_fac ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre]))).trans ?_
    refine this.trans ?_
    show (Spec.map (α'.app (Opposite.op V0)) ≫ hU.isoSpec.inv) ≫ U.1.ι = _
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map (α'.app (Opposite.op V0)) ≫ ·) (IsAffineOpen.isoSpec_inv_ι hU))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ hU.isoSpec.hom, Category.assoc, key]
  exact hP _


set_option backward.isDefEq.respectTransparency false in
theorem isFinite_toBase (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (hfin : ∀ V, (α'.app V).hom.Finite) : IsFinite (relativeGluingData h).toBase := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨toBase_of_Spec X F' α' h (@IsIntegralHom : MorphismProperty Scheme.{0}) fun V ↦ IsIntegralHom.SpecMap_iff.mpr (hfin V).to_isIntegral,
    toBase_of_Spec X F' α' h (@LocallyOfFiniteType : MorphismProperty Scheme.{0}) fun V ↦
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (hfin V).finiteType⟩

theorem isIso_restrict_basicOpen (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α)
    (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued)
    (hg₁ : g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase)
    (hg₂ : ∀ V, (relativeGluingData hα).cover.f V ≫ g =
      Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V)
    (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V))
    (hb : Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b))
    (W : (relativeGluingData hα').glued.Opens)
    (hW : (W : Set (relativeGluingData hα').glued) =
      (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V))))) :
    IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) =
      (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) :
        Set (PrimeSpectrum (F.obj (Opposite.op V)))) :=
  _root_.GlobalTheory.relSpec_map_isIso_over_basicOpen X F F' α α' hα hα' ι hι g hg₁ hg₂ V b hb W hW

theorem exists_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) :=
  GlobalTheory.T.normalization_basicOpen_cover' U X f V

theorem bijective_awayMap_of_range (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (φ : A →+* B) (hφ : Function.Injective φ)
    (hC : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B) (hab : φ a = b)
    (h : ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) :
    Function.Bijective (Localization.awayMap φ a) :=
  _root_.GlobalTheory.awayMap_bijective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h


set_option backward.isDefEq.respectTransparency false in
theorem exists_finite_openImmersion : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f →
    ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  intro U X f hX h₁ h₂ h₃ h₄
  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).2) (fun x _ ↦ by
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    exact ⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩
  let n := t.card
  let V : Fin n → X.AffineZariskiSite := fun k ↦ ⟨(t.equivFin.symm k).1.1, (t.equivFin.symm k).1.2⟩
  have hV : ∀ x : X, ∃ k, x ∈ (V k).1 := fun x ↦ by
    obtain ⟨W, hWt, hxW⟩ := ht x
    exact ⟨t.equivFin ⟨W, hWt⟩, by simpa [V] using hxW⟩
  choose G hGfin hGcov using fun k ↦ exists_basicOpen_cover U X f h₁ h₂ h₃ h₄ (V k)
  have hs : ∀ k, ∃ s : Finset (f.normalizationDiagram.obj (Opposite.op (V k).1)),
      (G k : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ s ∧
      letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
      ∀ C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)),
        (s : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) → ∀ b ∈ G k, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
    intro k
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    exact _root_.GlobalTheory.exists_finset_awayMap_subalgebra_bijective _ _ (G k) (hGfin k)
  choose s hGs hsC using hs
  have hint : ∀ W : X.Opens, IsAffineOpen W →
      (f.normalizationDiagramMap.app (Opposite.op W)).hom.IsIntegral := by
    intro W _
    letI := (f.app W).hom.toAlgebra
    change (algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, f ⁻¹ᵁ W))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  obtain ⟨F', α', ι, hα', hι, hιinj, hfin, hιS⟩ := _root_.GlobalTheory.QcSub.exists_finite_coequifibered_subalgebra X hX f.normalizationDiagram
    f.normalizationDiagramMap f.coequifibered_normalizationDiagramMap hint n V s
  obtain ⟨g, hg₁, hg₂⟩ := exists_glued_map X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι
  refine ⟨_, (relativeGluingData hα').toBase, f.toNormalization ≫ g,
    isFinite_toBase X F' α' hα' hfin, ?_, ?_⟩
  rotate_left
  · rw [Category.assoc, hg₁]; exact f.toNormalization_fromNormalization
  choose b' hb' using fun (k : Fin n) (b : G k) ↦ hιS k b.1 (hGs k b.2)
  haveI : ∀ k, IsOpenImmersion ((relativeGluingData hα').cover.f (V k)) :=
    fun k ↦ (relativeGluingData hα').cover.map_prop _
  let Wp : (Σ k, G k) → (relativeGluingData hα').glued.Opens := fun p ↦
    (relativeGluingData hα').cover.f (V p.1) ''ᵁ PrimeSpectrum.basicOpen (b' p.1 p.2)
  have hbij : ∀ p : Σ k, G k, Function.Bijective
      (Localization.awayMap (ι.app (Opposite.op (V p.1))).hom (b' p.1 p.2)) := by
    rintro ⟨k, b⟩
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    let C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)) :=
      { (ι.app (Opposite.op (V k))).hom.range with
        algebraMap_mem' := fun r ↦ ⟨(α'.app (Opposite.op (V k))).hom r, by
          rw [← CommRingCat.comp_apply, ← NatTrans.comp_app, hι]; rfl⟩ }
    have hsub : ((s k : Finset _) : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) :=
      fun x hx ↦ by obtain ⟨y, hy⟩ := hιS k x hx; exact ⟨y, hy⟩
    have hC : ∀ x, x ∈ C ↔ ∃ y, (ι.app (Opposite.op (V k))).hom y = x := fun x ↦ Iff.rfl
    have hB := hsC k C hsub b.1 b.2
    have hφ : Function.Injective (ι.app (Opposite.op (V k))).hom := hιinj _
    exact bijective_awayMap_of_range Γ(X, (V k).1) (F'.obj (Opposite.op (V k)))
      (f.normalizationDiagram.obj (Opposite.op (V k).1)) C (ι.app _).hom hφ hC (b' k b) b.1
      (hb' k b) hB
  have hiso := fun p : Σ k, G k ↦ isIso_restrict_basicOpen X _ F' _ α'
    f.coequifibered_normalizationDiagramMap hα' ι hι g hg₁ hg₂ (V p.1) (b' p.1 p.2) (hbij p)
    (Wp p) rfl
  refine isOpenImmersion_comp_of_isIso_restrict f.toNormalization g (⨆ p, Wp p)
    (isIso_morphismRestrict_iSup g Wp fun p ↦ (hiso p).1) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hV (f x)
  obtain ⟨b, hbG, hxb⟩ := hGcov k x hk
  have h2 := (hiso ⟨k, ⟨b, hbG⟩⟩).2
  rw [hb' k ⟨b, hbG⟩] at h2
  have h3 : f.toNormalization x ∈ SetLike.coe (g ⁻¹ᵁ Wp ⟨k, ⟨b, hbG⟩⟩) := by rw [h2]; exact hxb
  exact g.preimage_mono (le_iSup Wp ⟨k, ⟨b, hbG⟩⟩) h3

end GlobalTheory.ZMTFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetEqSumAddCosetIndicator
section
open Filter Topology

namespace GlobalTheory.LinSchur


open Classical in
theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGermOpenAffine
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem liftAll_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → l.Prime → (∀ p ∈ L, 0 < p.1 ∧ Reg q p.1 p.2) →
    deg (liftAll q l L) = deg L ∧ ∀ p ∈ liftAll q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftAll, deg]
  | cons p L ih =>
    have hp := hL p (by simp)
    have ih' := ih (fun x hx => hL x (by simp [hx]))
    have hcons : liftAll q l (p :: L) = (if l ∣ p.1 then liftL q l [p]
        else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++ liftAll q l L := by
      simp [liftAll, List.flatMap_cons]
    have hdegapp : ∀ A B : List (ℕ × ℕ), deg (A ++ B) = deg A + deg B := by intro A B; simp [deg]
    have hdegcons : deg (p :: L) = p.1 + deg L := by simp [deg]
    rw [hcons, hdegapp, hdegcons]
    by_cases h : l ∣ p.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.T.deg_liftL_and_reg_pow q l [p] hq hl.pos (by
        intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, h, hp.2⟩)
      rw [if_pos h]
      have hs : deg [p] = p.1 := by simp [deg]
      refine ⟨by rw [h1, hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact ih'.2 x hx
    · rw [if_neg h]
      have hr := (GlobalTheory.T.regular_pair_lift_to_prime_power_field q l p.1 p.2 hq hl hp.1 h hp.2).1
      have hs : deg [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))] = p.1 := by simp [deg]
      refine ⟨by rw [hs, ih'.1], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx; subst hx; exact ⟨hp.1, hr⟩
      · exact ih'.2 x hx

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitian
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_gl_diagonal_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  intro F _ _ E _ _ c δ hE ν _ _ b hb hdet
  letI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have h2 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have hG : ∀ x y, (c : E →+* E) (b x y) = b y x := by
    intro x y
    have := congrFun (congrFun hb y) x
    simpa using this
  obtain ⟨P, d, hP, hPd, hfix, hne⟩ :=
    GlobalTheory.HermDiag.exists_congr_diagonal (c := (c : E →+* E)) h2 (fun t => hE.invol t) (G := b) hG
  have hd0 := hne hdet
  have hPd' : Pᵀ * b * P.map c = diagonal d := hPd
  choose f hf using fun i => hE.exists_of_fixed (hfix i)
  have hf0 : ∀ i, f i ≠ 0 := by
    intro i h; apply hd0 i; rw [hf i, h, map_zero]
  have hQ : (Pᵀ).det ≠ 0 := by rwa [det_transpose]
  set A : Matrix ν ν E := (Pᵀ)⁻¹ with hA
  have hAQ : A * Pᵀ = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQ)
  have hQA : Pᵀ * A = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ)
  have hAs : (A.map c)ᵀ * P.map c = 1 := by
    have h1 : (Pᵀ * A).map c = 1 := by rw [hQA]; exact Matrix.map_one _ (map_zero c) (map_one c)
    rw [show (Pᵀ * A).map c = (Pᵀ).map c * A.map c from Matrix.map_mul (f := c.toRingHom)] at h1
    have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    simpa [Matrix.transpose_map] using h3
  have hAs' : P.map c * (A.map c)ᵀ = 1 := mul_eq_one_comm.mp hAs
  have hAdet : A.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hAQ
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hAdet, fun j => Units.mk0 (f j) (hf0 j), ?_⟩
  have hD : diagonal (fun j => algebraMap F E ((Units.mk0 (f j) (hf0 j) : Fˣ) : F)) = diagonal d := by
    congr 1; funext j; simp [hf j]
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  rw [hD, ← hPd']
  calc b = (A * Pᵀ) * b * (P.map c * (A.map c)ᵀ) := by rw [hAQ, hAs', Matrix.one_mul, Matrix.mul_one]
    _ = A * (Pᵀ * b * P.map c) * (A.map c)ᵀ := by simp only [Matrix.mul_assoc]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosedBallAddCharEqZero
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem exists_integral_cball_char_eq_zero :
    ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  intro F _ _ _ _ _ _ _ lam _ ψ _ _ hne
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne (by ext x; simpa using h x)
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (by simp)
  refine ⟨Units.mk0 t ht0, fun s hs => ?_⟩
  have hs' : t ∈ GlobalTheory.SplitWeil.cball s := hs
  have hm : MeasurableSet (GlobalTheory.SplitWeil.cball s) := (GlobalTheory.SplitWeil.isOpen_cball s).measurableSet
  have hadd : ∀ x y : F, x ∈ GlobalTheory.SplitWeil.cball s → y ∈ GlobalTheory.SplitWeil.cball s →
      x + y ∈ GlobalTheory.SplitWeil.cball s := fun x y hx hy => by
    simp only [GlobalTheory.SplitWeil.cball, Set.mem_setOf_eq] at hx hy ⊢
    exact Valuation.map_add_le _ hx hy
  have hneg : -t ∈ GlobalTheory.SplitWeil.cball s := by
    simpa [GlobalTheory.SplitWeil.cball] using hs'
  have hiff : ∀ x : F, t + x ∈ GlobalTheory.SplitWeil.cball s ↔ x ∈ GlobalTheory.SplitWeil.cball s := fun x =>
    ⟨fun h => by simpa using hadd _ _ hneg h, fun h => hadd _ _ hs' h⟩
  rw [← integral_indicator hm]
  have h1 := integral_add_left_eq_self (μ := lam)
    ((GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x)) t
  have h2 : (fun x => (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) (t + x))
      = fun x => ψ t * (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x := by
    funext x
    by_cases hx : x ∈ GlobalTheory.SplitWeil.cball s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), AddChar.map_add_eq_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h)), mul_zero]
  rw [h2, integral_const_mul] at h1
  have h3 : (ψ t - 1) * ∫ x, (GlobalTheory.SplitWeil.cball s).indicator (fun x => ψ x) x ∂lam = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ht)

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsModelOfUnitary
section
open GlobalTheory.UnitLemma Polynomial Matrix

namespace GlobalTheory.InertUnitOrb

theorem stdH_mulVec_of_unitary (K : UQ) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (hγ : (γ.map K.c)ᵀ * γ = 1) (y z : Fin n → K.E) :
    stdH K n (γ *ᵥ y) (γ *ᵥ z) = stdH K n y z := by
  have h1 : ∀ u v : Fin n → K.E, stdH K n u v = u ⬝ᵥ (fun k => K.c (v k)) := fun u v => rfl
  have h2 : (fun k => K.c ((γ *ᵥ z) k)) = (γ.map K.c) *ᵥ (fun k => K.c (z k)) := by
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  rw [h1, h1, h2, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hγ, one_mulVec]

theorem exists_isModel_of_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  intro K B n γ hγ hg hsep hchar
  obtain ⟨x, e, h1, h2, h3⟩ := PairClass.exists_herm_model K (Fin n → K.E) (stdH K n)
    (fun x y z => by simp [stdH, add_mul, Finset.sum_add_distrib])
    (fun c x z => by simp [stdH, Finset.mul_sum, mul_assoc])
    (fun x y => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [stdH, map_sum, map_mul, K.c_c]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _)
    (fun y hy => by
      funext k
      have := hy (Pi.single k 1)
      rw [stdH, Finset.sum_eq_single k] at this
      · simpa using this
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp)
    B (Matrix.toLin' γ) hsep (by rw [Matrix.charpoly_toLin', hchar])
    (Or.inl ⟨hg, fun y z => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, stdH_mulVec_of_unitary K n γ hγ]⟩)
  exact ⟨x, e, h1, fun y => by rw [h2, Matrix.toLin'_apply], h3⟩

end GlobalTheory.InertUnitOrb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZeroStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jet_extension_square_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C), f₁.deg = f₂.deg → (∀ a, n a ∈ T.J) → (∀ a b, n a * n b = 0) → (∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) → ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧ ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)), χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first | exact @GlobalTheory.AnPer.Charts.exists_jet_factor | exact GlobalTheory.AnPer.Charts.exists_jet_factor | (intros; apply GlobalTheory.AnPer.Charts.exists_jet_factor <;> assumption)
end

