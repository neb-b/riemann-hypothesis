module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.ArcProper

theorem exists_isOpenImmersion_isProper {R : Type} [CommRing R] {U : Scheme.{0}} [IsAffine U]
    (s : U ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ (P : Scheme.{0}) (t : P ⟶ Sp R) (j : U ⟶ P), IsProper t ∧ IsOpenImmersion j ∧ j ≫ t = s := by
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv U)).isQProjOver s
  have := isProper_str R N
  exact ⟨i.image, i.imageι ≫ PSpace.str R N, i.toImage, inferInstance, inferInstance,
    by rw [i.toImage_imageι_assoc, e]⟩

theorem exists_isProper_factor {S U : Scheme.{0}} {J : Type} (P : J → Scheme.{0})
    (t : ∀ i, P i ⟶ S) (ht : ∀ i, IsProper (t i)) (u : U ⟶ S) (φ : ∀ i, U ⟶ P i)
    (h : ∀ i, φ i ≫ t i = u) (T : Finset J) :
    ∃ (Q : Scheme.{0}) (q : Q ⟶ S) (ψ : U ⟶ Q), IsProper q ∧ ψ ≫ q = u ∧
      ∀ i ∈ T, ∃ p : Q ⟶ P i, p ≫ t i = q ∧ ψ ≫ p = φ i := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨S, 𝟙 S, u, inferInstance, Category.comp_id _, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, q, ψ, _, e, H⟩ := ih
    refine ⟨pullback q (t a), pullback.fst _ _ ≫ q, pullback.lift ψ (φ a) (e.trans (h a).symm),
      inferInstance, by rw [pullback.lift_fst_assoc, e], fun i hi ↦ ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨pullback.snd _ _, pullback.condition.symm, pullback.lift_snd _ _ _⟩
    · obtain ⟨p, hp, hp'⟩ := H i hi
      exact ⟨pullback.fst _ _ ≫ p, by rw [Category.assoc, hp], by rw [pullback.lift_fst_assoc, hp']⟩

theorem exists_extension_of_cover {S Z X W : Scheme.{0}} [IsIntegral Z] [Nonempty W] (z : Z ⟶ S)
    (s : X ⟶ S) [IsSeparated s] (j : W ⟶ Z) [IsOpenImmersion j] (u : W ⟶ X) {J : Type}
    (V : J → Z.Opens) (hV : TopologicalSpace.IsOpenCover V) (m : ∀ i, (V i).toScheme ⟶ X)
    (hm : ∀ i, m i ≫ s = (V i).ι ≫ z)
    (hu : ∀ (i : J) (T : Scheme.{0}) (a : T ⟶ W) (b : T ⟶ V i), a ≫ j = b ≫ (V i).ι →
      b ≫ m i = a ≫ u) :
    ∃ g : Z ⟶ X, g ≫ s = z ∧ Set.range u ⊆ Set.range g := by
  let 𝒰 := Z.openCoverOfIsOpenCover V hV
  have hd : Dense (Set.range j) := j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
  have hc : ∀ i i', pullback.fst (V i).ι (V i').ι ≫ m i = pullback.snd (V i).ι (V i').ι ≫ m i' := by
    intro i i'
    let r := pullback.fst (V i).ι (V i').ι ≫ (V i).ι
    have : IsReduced (pullback (V i).ι (V i').ι) := isReduced_of_isOpenImmersion r
    have : IsDominant (pullback.fst r j) := ⟨by
      rw [DenseRange, Scheme.Pullback.range_fst]
      exact hd.preimage r.isOpenEmbedding.isOpenMap⟩
    refine ext_of_isDominant_of_isSeparated s ?_ (pullback.fst r j) ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [← Category.assoc, ← Category.assoc, hu i _ (pullback.snd r j), hu i' _ (pullback.snd r j)]
      · rw [Category.assoc, ← pullback.condition, ← pullback.condition]
      · rw [Category.assoc, ← pullback.condition]
  have hg : ∀ i, (V i).ι ≫ 𝒰.glueMorphisms m hc = m i := fun i ↦ 𝒰.ι_glueMorphisms m hc i
  refine ⟨𝒰.glueMorphisms m hc, 𝒰.hom_ext _ _ fun i ↦ ?_, ?_⟩
  · exact ((reassoc_of% hg i) s).trans (hm i)
  · rintro _ ⟨w, rfl⟩
    obtain ⟨i, hi⟩ := hV.exists_mem (j w)
    have : w ∈ Set.range (pullback.fst j (V i).ι) := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]; exact hi
    obtain ⟨v, rfl⟩ := this
    refine ⟨(pullback.snd j (V i).ι ≫ (V i).ι) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hg,
      hu i _ _ _ pullback.condition]

theorem exists_arc (k : Type) [Field k] [IsAlgClosed k] {Z : Scheme.{0}} [IsIntegral Z]
    (s : Z ⟶ Sp k) [LocallyOfFiniteType s] (z : Z) (hz : IsClosed ({z} : Set Z)) (W : Set Z)
    (hW : IsOpen W) (hW' : W.Nonempty) :
    ∃ c : Sp (PowerSeries k) ⟶ Z, c ≫ s = spMap (algebraMap k (PowerSeries k)) ∧
      c (IsLocalRing.closedPoint (PowerSeries k)) = z ∧
      Set.range (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ c) ⊆ W := by
  obtain ⟨B, g, _, y, rfl⟩ := Z.exists_Spec_apply_eq z
  have : Nonempty (Spec B) := ⟨y⟩
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion g
  have : IsDomain B := (affine_isIntegral_iff B).mp this
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (g ≫ s)
  have hft : ψ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra k B := ψ.hom.toAlgebra
  have : Algebra.FiniteType k B := hft
  have hy : y.asIdeal.IsMaximal := by
    refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 ?_
    have := hz.preimage g.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ g.isOpenEmbedding.injective] at this
  obtain ⟨w, hw⟩ : (g ⁻¹' W).Nonempty := by
    obtain ⟨_, hw, w, rfl⟩ := (g.isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)).inter_open_nonempty W hW hW'
    exact ⟨w, hw⟩
  obtain ⟨_, ⟨f, rfl⟩, hwf, hf⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hw
      (hW.preimage g.continuous)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hwf w.asIdeal.zero_mem
  obtain ⟨φ, hφ, hφm⟩ := GlobalTheory.ArcAvoid.exists_algHom_powerSeries_ne_zero k B y.asIdeal hy f hf0
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ g, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    congr 1
    ext1
    exact φ.comp_algebraMap
  · refine congrArg g (PrimeSpectrum.ext (Ideal.ext fun b ↦ ?_))
    change φ b ∈ IsLocalRing.maximalIdeal (PowerSeries k) ↔ _
    rw [hφm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      isUnit_iff_ne_zero, not_not]
  · rintro _ ⟨p, rfl⟩
    refine hf ?_
    change algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (φ f) ∉ p.asIdeal
    intro h
    refine p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsUnit.mk0 _ ?_))
    simpa using hφ

theorem isProper_of_arcs_extend (k : Type) [Field k] [IsAlgClosed k] {Y : Scheme.{0}} [IsIntegral Y]
    (s : Y ⟶ Sp k) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (H : ∀ a : Sp (FractionRing (PowerSeries k)) ⟶ Y,
      a ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ Y,
        spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) :
    IsProper s := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have hA : ∀ y : Y, ∃ A : Y.Opens, IsAffineOpen A ∧ y ∈ A := fun y ↦ by
    obtain ⟨A, h₁, h₂, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
    exact ⟨A, h₁, h₂⟩
  choose A₀ hA₀ hyA using hA
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun y ↦ (A₀ y : Set Y))
    (fun y ↦ (A₀ y).isOpen) (fun y _ ↦ Set.mem_iUnion.2 ⟨y, hyA y⟩)
  let A : T → Y.Opens := fun i ↦ A₀ i
  have hcov : ∀ y : Y, ∃ i : T, y ∈ A i := fun y ↦ by
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ y))
    exact ⟨⟨i, hi⟩, h⟩
  have hP := fun i : T ↦ (have : IsAffine (A i).toScheme := hA₀ i
    exists_isOpenImmersion_isProper ((A i).ι ≫ s))
  choose P t j ht hj hjt using hP
  let U : Y.Opens := Finset.univ.inf A
  have hUA : ∀ i, U ≤ A i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  have hU : genericPoint Y ∈ U := by
    have : ∀ i, genericPoint Y ∈ A i := fun i ↦
      ((genericPoint_spec Y).mem_open_set_iff (A i).isOpen).2 ⟨i, trivial, hyA i⟩
    refine Finset.inf_induction (p := fun V : Y.Opens ↦ genericPoint Y ∈ V) trivial
      (fun _ h _ h' ↦ ⟨h, h'⟩) fun i _ ↦ this i
  have : Nonempty U.toScheme := ⟨⟨_, hU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨Q, q, ψ, _, hψ, hp⟩ := exists_isProper_factor P t ht (U.ι ≫ s)
    (fun i ↦ Y.homOfLE (hUA i) ≫ j i) (fun i ↦ by rw [Category.assoc, hjt, Y.homOfLE_ι_assoc])
    Finset.univ
  choose p hpt hψp using fun i ↦ hp i (Finset.mem_univ i)
  obtain ⟨i₀, -⟩ := hcov (genericPoint Y)
  have : IsImmersion (ψ ≫ p i₀) := by rw [hψp]; infer_instance
  have : IsImmersion ψ := IsImmersion.of_comp ψ (p i₀)
  have : QuasiCompact (ψ ≫ q) := by rw [hψ]; infer_instance
  have : QuasiCompact ψ := QuasiCompact.of_comp ψ q
  have : IsIntegral ψ.image := isIntegral_image ψ
  let z : ψ.image ⟶ Sp k := ψ.imageι ≫ q
  have hz : ψ.toImage ≫ z = U.ι ≫ s := by rw [ψ.toImage_imageι_assoc, hψ]
  let V : T → ψ.image.Opens := fun i ↦ (ψ.imageι ≫ p i) ⁻¹ᵁ (j i).opensRange
  have hinj : Function.Injective
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) := IsFractionRing.injective _ _
  have : IsDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
    exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
  have key : ∀ x : ψ.image, IsClosed ({x} : Set ψ.image) → ∃ i, x ∈ V i := by
    intro x hx
    obtain ⟨c, hc, hcx, hcU⟩ := exists_arc k z x hx _ ψ.toImage.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    obtain ⟨l, hl⟩ : ∃ l, l ≫ ψ.toImage = _ := ⟨_, IsOpenImmersion.lift_fac ψ.toImage _ hcU⟩
    have hls : (l ≫ U.ι) ≫ s = spMap (algebraMap k (FractionRing (PowerSeries k))) := by
      rw [Category.assoc, ← hz, reassoc_of% hl, hc, ← Spec.map_comp]
      rfl
    obtain ⟨b, hb⟩ := H (l ≫ U.ι) hls
    have hbs : b ≫ s = spMap (algebraMap k (PowerSeries k)) := by
      refine ext_of_isDominant (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      rw [← Category.assoc, hb, hls, ← Spec.map_comp]
      rfl
    obtain ⟨i, hi⟩ := hcov (b (IsLocalRing.closedPoint (PowerSeries k)))
    have hr : Set.range b ⊆ Set.range (A i).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨v, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint v).map b.continuous).mem_open (A i).isOpen hi
    obtain ⟨b', hb'⟩ : ∃ b', b' ≫ (A i).ι = b := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
    have e : b' ≫ j i = c ≫ ψ.imageι ≫ p i := by
      refine ext_of_isDominant_of_isSeparated (t i) ?_
        (spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) ?_
      · rw [Category.assoc, hjt, reassoc_of% hb', hbs, Category.assoc, Category.assoc, hpt, hc]
      · rw [← reassoc_of% hl, ψ.toImage_imageι_assoc, hψp, ← Category.assoc, ← Category.assoc]
        congr 1
        rw [← cancel_mono (A i).ι, Category.assoc, hb', hb, Category.assoc, Y.homOfLE_ι]
    refine ⟨i, b' (IsLocalRing.closedPoint (PowerSeries k)), ?_⟩
    have e' : (b' ≫ j i) (IsLocalRing.closedPoint (PowerSeries k)) =
        (c ≫ ψ.imageι ≫ p i) (IsLocalRing.closedPoint (PowerSeries k)) := by rw [e]
    exact e'.trans (congrArg (ψ.imageι ≫ p i) hcx)
  have : CompactSpace ψ.image := QuasiCompact.compactSpace_of_compactSpace z
  have hV : TopologicalSpace.IsOpenCover V := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    obtain ⟨x', hx', hc⟩ := (isClosed_closure (s := {x})).exists_closed_singleton
      (Set.singleton_nonempty x).closure
    obtain ⟨i, hi⟩ := key x' hc
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨i, (specializes_iff_mem_closure.2 hx').mem_open (V i).isOpen hi⟩
  have hm : ∀ i, ∃ m : (V i).toScheme ⟶ A i, m ≫ j i = (V i).ι ≫ ψ.imageι ≫ p i := fun i ↦
    ⟨_, IsOpenImmersion.lift_fac (j i) _ (by rintro _ ⟨v, rfl⟩; exact v.2)⟩
  choose m hm using hm
  obtain ⟨g, hg, hgU⟩ := exists_extension_of_cover z s ψ.toImage U.ι V hV
    (fun i ↦ m i ≫ (A i).ι)
    (fun i ↦ by rw [Category.assoc, ← hjt, reassoc_of% hm, hpt])
    (fun i T a b e ↦ by
      rw [← Y.homOfLE_ι (hUA i), ← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (j i), Category.assoc, hm, ← reassoc_of% e, ψ.toImage_imageι_assoc, hψp,
        Category.assoc])
  have : IsProper (g ≫ s) := by rw [hg]; infer_instance
  have : IsProper g := IsProper.of_comp g s
  have : IsDominant g := ⟨(U.isOpen.dense ⟨_, hU⟩).mono (by rwa [Scheme.Opens.range_ι] at hgU)⟩
  have : Surjective g := surjective_of_isDominant_of_isClosed_range g g.isClosedMap.isClosed_range
  have : UniversallyClosed s := .of_comp_surjective g s
  exact {}

theorem isProper_of_arcs : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Over (Sp k)) [IsIntegral X.left], IsSeparated X.hom → LocallyOfFiniteType X.hom → QuasiCompact X.hom → (∀ a : Sp (FractionRing (PowerSeries k)) ⟶ X.left, a ≫ X.hom = spMap (algebraMap k (FractionRing (PowerSeries k))) → ∃ b : Sp (PowerSeries k) ⟶ X.left, spMap (algebraMap (PowerSeries k) (FractionRing (PowerSeries k))) ≫ b = a) → IsProper X.hom :=
  fun k _ _ X _ _ _ _ H ↦ isProper_of_arcs_extend k X.hom H

end GlobalTheory.ArcProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NatCastNeZeroOfIsUnit
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.FewAtTest

open GlobalTheory.CechPic

theorem pic_eq_zero_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {H : Scheme.{0}}
    (p : H ⟶ Sp V) (e : Sp V ⟶ H) (hs : Smooth p) (hi : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (c : Pic H)
    (h₁ : pull (pullback.fst p (Out.jK V)) c = 0) (h₂ : pull e c = 0) : c = 0 := by
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  let eK : Sp (FractionRing V) ⟶ pullback p (Out.jK V) := pullback.lift (Out.jK V ≫ e) (𝟙 _) (by
    rw [Category.assoc, he, Category.id_comp]; exact Category.comp_id _)
  have heK : eK ≫ pullback.fst p (Out.jK V) = Out.jK V ≫ e := pullback.lift_fst _ _ _
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff (pull_isLB hM (pullback.fst p (Out.jK V) ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₁])
  obtain ⟨ρ, hρ⟩ := (cls_eq_zero_iff (pull_isLB hM (e ≫ 𝟙 H))).1 (by
    rw [cls_pull hM, pull_comp, pull_id, h₂])
  obtain ⟨u, hu, cu⟩ := DVR.exists_normalized_to hM _ _ t ht (pullback.snd p (Out.jK V)) eK
    (pullback.lift_snd _ _ _) _ _ (LB.pullGen M _ _ ρ (Out.jK V)) (DVR.pullGen_isGen _ _ _ _ hρ _) (by
      congr 1
      funext k
      rw [← Category.assoc, heK, Category.assoc])
  obtain ⟨s, ⟨hs₁, -⟩, -⟩ := GenExtend.existsUnique_gen_extend V (FractionRing V) H H p e hs hi he eK heK M hM
    PUnit (fun _ => 𝟙 H) (fun _ => 1) u ρ hu hρ cu
  have := (cls_eq_zero_iff (pull_isLB hM (𝟙 H))).2 ⟨s, hs₁⟩
  rwa [cls_pull hM, pull_id] at this

theorem lbIso_of_generic {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (L M : RigLB G)
    (h : LBIso (L.L.pull (pullback.fst G.hom (Out.jK V))) (M.L.pull (pullback.fst G.hom (Out.jK V)))) :
    LBIso L.L M.L := by
  refine (cls_eq_iff L.isLB M.isLB).1 (sub_eq_zero.1 (pic_eq_zero_of_generic G.hom (eSec G) hG.smooth
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ ?_ ?_))
  · rw [map_sub, sub_eq_zero]
    exact (cls_eq_iff (pull_isLB L.isLB _) (pull_isLB M.isLB _)).2 h
  · have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
    have b := (cls_eq_zero_iff (pull_isLB M.isLB (eSec G))).2 ⟨M.rig, M.rigGen⟩
    rw [cls_pull L.isLB] at a
    rw [cls_pull M.isLB] at b
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (a.trans b.symm))

theorem natCast_ne_zero_of_isUnit {Z : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ Z) {n : ℕ}
    (h : IsUnit (n : Γ(Z, ⊤))) : (n : K) ≠ 0 := by
  have := (h.map x.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast, map_natCast] at this
  exact this.ne_zero

theorem range_rPt {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] [IsLocalRing V] (j : V →+* OO p) [IsLocalHom j] :
    Set.range (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) = {IsLocalRing.closedPoint V} := by
  have key : ∀ x : Sp (kb p), (rPt p ≫ spMap j : Sp (kb p) ⟶ Sp V) x = IsLocalRing.closedPoint V := fun x => by
    have hx : x = IsLocalRing.closedPoint (kb p) := Subsingleton.elim (α := PrimeSpectrum (kb p)) _ _
    subst hx
    exact (congrArg (PrimeSpectrum.comap j) (IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p)))).trans
      (IsLocalRing.comap_closedPoint j)
  ext x
  exact ⟨fun ⟨a, ha⟩ => ha ▸ key a, fun h => ⟨IsLocalRing.closedPoint (kb p), (key _).trans h.symm⟩⟩

end GlobalTheory.FewAtTest

namespace GlobalTheory.ZJ

open GlobalTheory.FewAtTest

theorem theta_few : GlobalTheory.ZH.ThmUSt → Out.Laws → Out.Laws2 → ∀ (C : Core) (T : C.Theta), Out.RelAmple C.A T.L.L → Out.KTriv C.A T.L.L → T.L.IsSymmetric → GlobalTheory.ZH.HypS C.A T.L.L → ∀ N n : ℕ, 4 ≤ N → IsUnit (n : Γ(C.Z, ⊤)) → 6 * (N ^ C.g * C.g.factorial) < n ^ 2 → T.Few n := by
  intro hU laws laws₂ C T hA hK hs hS N n hN hn hlt p _ y τ E c
  obtain ⟨-, h0, hG⟩ := (core_basic C).2.2.2.2.2.2.2.2.2.2.2.2 p y τ
  have hL := pull_isLB T.L.isLB τ.φ
  have hi := PolBaseChange.lbIso_refl hL
  obtain ⟨hab, hamp, hkt⟩ := pol_pull _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L (T.L.L.pull τ.φ)
    T.L.isLB hL C.ab τ.φ_cart hi
  let A : Out.PolAV (Sp (FractionRing τ.V)) :=
    { A := (Over.pullback (Out.jK τ.V)).obj τ.H
      isAb := hab
      g := C.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback τ.φ_cart.1 C.dim
      L := T.L.L.pull τ.φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull τ.φ_cart ⟨T.L.rig, T.L.rigGen⟩
      sym := PolBaseChange.sym_pull τ.φ_cart (CechPic.sym_of_isSymmetric T.L hs)
      ample := hamp hA
      ktriv := hkt hK }
  have := hab.comm
  have hS' := SymBaseChange.hypS_baseChange _ _ C.A ((Over.pullback (Out.jK τ.V)).obj τ.H) τ.yK τ.φ T.L.L
    (T.L.L.pull τ.φ) T.L.isLB hL τ.φ_cart hi hS
  obtain ⟨D, U, hgen⟩ := hU τ.V τ.complete A τ.H hG τ.split hS' (Iso.refl _)
    (inferInstanceAs (IsMonHom (𝟙 ((Over.pullback (Out.jK τ.V)).obj τ.H))))
  have e₁ : LBIso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) := U.ext
  rw [hgen] at e₁
  have e₂ : LBIso (E.L.L.pull (pullback.fst τ.H.hom (Out.jK τ.V))) (A.L.pull (𝟙 _)) :=
    LBIso.trans (pull_isLB E.L.isLB _) hL (pull_isLB hL _) (LBIso.symm ⟨E.w, E.w_gen⟩)
      (CechPic.iso_of_chart hL (Geo.Tor.chartPullPull _ _ _ rfl)).symm
  have e := lbIso_of_generic hG E.L U.LG
    (LBIso.trans (pull_isLB E.L.isLB _) (pull_isLB hL _) (pull_isLB U.LG.isLB _) e₂ e₁)
  have := isAlgClosed_kb (p := p)
  have := τ.j_loc
  exact GlobalTheory.FewZeros.card_torsion_translate_zeros_lt laws laws₂ τ.V τ.complete D A τ.H U E.L.L E.θ E.L.isLB e E.θ_ne (kb p) (rPt p ≫ spMap τ.j) N n
    (range_rPt τ.j) hN (natCast_ne_zero_of_isUnit (rPt p ≫ y) hn) hlt c

end GlobalTheory.ZJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem geometricallyConnected_of_generic_of_special (W L : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] {X : Scheme.{0}} (f : X ⟶ Sp W)
    (h₁ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W L))))
    (h₂ : GeometricallyConnected (pullback.snd f (spMap (algebraMap W (IsLocalRing.ResidueField W))))) :
    GeometricallyConnected f := by
  have key : ∀ (Ω F : Type) [Field Ω] [Field F] (a : W →+* F) (ψ : F →+* Ω),
      GeometricallyConnected (pullback.snd f (spMap a)) →
      ∀ (Z : Scheme.{0}) (fst : Z ⟶ X) (snd : Z ⟶ Sp Ω), IsPullback fst snd f (spMap (ψ.comp a)) →
      ConnectedSpace Z := by
    intro Ω F _ _ a ψ h Z fst snd hZ
    have e : spMap (ψ.comp a) = spMap ψ ≫ spMap a := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e] at hZ
    have sq : IsPullback (pullback.lift fst (snd ≫ spMap ψ) (hZ.w.trans (Category.assoc _ _ _).symm)) snd
        (pullback.snd f (spMap a)) (spMap ψ) :=
      IsPullback.of_right (by rw [pullback.lift_fst]; exact hZ) (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback f (spMap a))
    exact GeometricallyConnected.geometrically_connectedSpace (f := pullback.snd f (spMap a)) _ _ _ sq
  refine ⟨fun Ω _ q Z fst snd hZ => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  change IsPullback fst snd f (spMap φ.hom) at hZ
  by_cases h : RingHom.ker φ.hom = ⊥
  · have hinj := (RingHom.injective_iff_ker_eq_bot _).2 h
    have e : (IsFractionRing.lift (K := L) hinj).comp (algebraMap W L) = φ.hom :=
      RingHom.ext fun x => IsFractionRing.lift_algebraMap hinj x
    rw [← e] at hZ
    exact key Ω L _ _ h₁ Z fst snd hZ
  · have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal W :=
      IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime φ.hom).isMaximal h)
    let ψ : IsLocalRing.ResidueField W →+* Ω :=
      Ideal.Quotient.lift (IsLocalRing.maximalIdeal W) φ.hom fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)
    have e : ψ.comp (algebraMap W (IsLocalRing.ResidueField W)) = φ.hom := RingHom.ext fun x => rfl
    rw [← e] at hZ
    exact key Ω _ _ _ h₂ Z fst snd hZ

theorem isSemiAbelian_of_abelian_generic_of_torusExt : NfSt := by
  intro W _ _ _ L _ _ _ A _ hA G _ hc hs hsep hqc ⟨e, _⟩ hT
  obtain ⟨k, _, _, _, ⟨E⟩⟩ := _root_.GlobalTheory.SS.exists_finite_torusExtension_of_torusExt _ _ hT
  have hw : (baseChange W L G).hom = e.hom.left ≫ A.hom := (Over.w e.hom).symm
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have := hA.proper
  have := hA.geomConnected
  have hp : IsProper (baseChange W L G).hom := by rw [hw]; infer_instance
  have hg : GeometricallyConnected (baseChange W L G).hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := e.hom.left) (g := 𝟙 _) ⟨by rw [hw, Category.comp_id]⟩) hA.geomConnected
  have hk := (GlobalTheory.torusExtension_smooth_geometricallyConnected _ E).2.2.2.1
  have hsurj : Surjective (spMap (algebraMap (IsLocalRing.ResidueField W) k)) :=
    ⟨fun z => ⟨_, Subsingleton.elim (spMap (algebraMap (IsLocalRing.ResidueField W) k)
      (default : PrimeSpectrum _)) z⟩⟩
  have hsp : GeometricallyConnected (specialFibre W G).hom :=
    @GlobalTheory.geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback (specialFibre W G).hom (spMap (algebraMap (IsLocalRing.ResidueField W) k)))
      hsurj hk
  have hgc : GeometricallyConnected G.hom := geometricallyConnected_of_generic_of_special W L G.hom hg hsp
  refine isSemiAbelian_of_proper_generic_of_torusExtension W L G ⟨hc, hs, hsep, hqc, hgc⟩ hp k
    ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) ?_ ?_ ?_
  · rw [RingHom.ker_comp_of_injective _ (algebraMap (IsLocalRing.ResidueField W) k).injective]
    exact IsLocalRing.ker_residue
  · refine RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective) ?_
    exact Algebra.IsIntegral.isIntegral
  · have e' : spMap ((algebraMap (IsLocalRing.ResidueField W) k).comp (algebraMap W (IsLocalRing.ResidueField W))) =
        spMap (algebraMap (IsLocalRing.ResidueField W) k) ≫ spMap (algebraMap W (IsLocalRing.ResidueField W)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e']
    have : IsMonHom (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm.hom :=
      inferInstanceAs (IsMonHom (pullCompIso _ _ G).inv)
    exact ⟨torusExtOfIso (pullCompIso (spMap (algebraMap (IsLocalRing.ResidueField W) k))
        (spMap (algebraMap W (IsLocalRing.ResidueField W))) G).symm E⟩

end GlobalTheory.SS
end

