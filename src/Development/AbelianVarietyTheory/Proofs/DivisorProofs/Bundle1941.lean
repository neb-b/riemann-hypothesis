module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0522
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DvrCriterion

open Scheme.IdealSheafData TopologicalSpace

theorem universallyClosed_of_finite_jointly_surjective {ι : Type} [Finite ι] {X Z : Scheme.{0}}
    (A : ι → Scheme.{0}) (g : ∀ i, A i ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, ∃ i, ∃ a, g i a = x)
    (h : ∀ i, UniversallyClosed (g i ≫ k)) : UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c := fun i ↦ (h i).universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, a, ha⟩ := hcov (i₁ x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
      exact Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩
    · intro y hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, hz, by simp⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))

theorem universallyClosed_snd_of_lift {Y S : Scheme.{0}} (π : Y ⟶ S) [LocallyOfFiniteType π]
    [QuasiCompact π] [IsSeparated π] (R : Type) [CommRing R] [IsNoetherianRing R] (u : Sp R ⟶ S)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y →
        ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) :
    UniversallyClosed (pullback.snd π u) := by
  classical
  set s := pullback.snd π u with hs
  have : CompactSpace (pullback π u : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian (pullback π u : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian (pullback π u : Scheme.{0}) := {}
  let C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0}) :=
    fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  have : Finite (irreducibleComponents (pullback π u : Scheme.{0})) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1 := fun c ↦ by
    rw [range_subschemeι, coe_support_vanishingIdeal]; rfl
  refine universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme)
    (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)
  · refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    have : x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι := by
      rw [hr]; exact mem_irreducibleComponent
    exact this
  set I := vanishingIdeal (C c)
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (Set.range I.subschemeι) := by
    have h1 : IsIrreducible (Set.range I.subschemeι) := by rw [hr]; exact c.2.1
    exact Subtype.irreducibleSpace h1
  have : IrreducibleSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper (I.subschemeι ≫ s) := by
    refine GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_
    intro V K _ _ _ _ _ _ _ x y _ hxy
    let e : FractionRing V ≃ₐ[V] K := IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K
    let ε : K →+* FractionRing V := e.symm.toRingEquiv.toRingHom
    let ε' : FractionRing V →+* K := e.toRingEquiv.toRingHom
    have he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V := by
      rw [spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact e.symm.commutes a
    have he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K) := by
      rw [spMap, Out.jK, ← Spec.map_comp]
      congr 2
      ext a
      exact e.commutes a
    have he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 2
      ext a
      exact e.apply_symm_apply a
    let xF : Sp (FractionRing V) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u
    have hxF : xF ≫ π = Out.jK V ≫ (y ≫ u) := by
      have : xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u := by
        simp [xF, hs, pullback.condition]
      rw [this, hxy, ← he1]
      simp
    obtain ⟨x'', hx1, hx2⟩ := H V xF (y ≫ u) hxF
    let x3 : Sp V ⟶ pullback π u := pullback.lift x'' y hx2
    have h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι := by
      apply pullback.hom_ext
      · simp only [x3, Category.assoc, pullback.lift_fst]
        exact hx1
      · have : Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y := by
          rw [hxy, ← he1]; simp
        simp only [x3, Category.assoc, pullback.lift_snd]
        exact this.symm
    have hdom : IsDominant (Out.jK V) := by
      have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0})) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ closure (Set.range (Out.jK V)) := (Out.jK V).denseRange v
      have := map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by
        rintro _ ⟨w, rfl⟩
        change x3 (Out.jK V w) ∈ c.1
        rw [← Scheme.Hom.comp_apply, h3, ← hr c]
        exact ⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)
      rwa [(C c).isClosed.closure_eq] at this
    have hker : I.subschemeι.ker ≤ x3.ker := by
      rw [I.ker_subschemeι]
      exact GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange
    refine ⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩
    rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2,
      Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]
  exact inferInstance

theorem existence_of_lift_discreteValuationRing : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  intro Y S _ π _ _ _ H
  have hUC : UniversallyClosed π := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]
    intro i
    have := S.affineOpenCover.map_prop i
    have hR : IsNoetherianRing (S.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))
    exact @universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR
      (S.affineOpenCover.openCover.f i) H
  have h := hUC
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

end GlobalTheory.DvrCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakResolutionOfPrincipalisation
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.WeakRes

theorem isProjOver_comp_closed {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem isProjOver_seq {F : Type} [Field F] {Y Y' : Scheme.{0}} (f : Y ⟶ Sp F) {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) (hf : IsProjOver f) : IsProjOver (s ≫ f) := by
  induction h with
  | id => simpa using hf
  | @step Y₁ Y₂ s J π _ _ _ hb ih =>
    obtain ⟨X', b, hb', hproj, -⟩ := ProjBlowup.exists_blowup (s ≫ f) ih J
    obtain ⟨e, he, heb⟩ := ProjBlowup.exists_iso_of_blowup J π b hb hb'
    rw [← heb, Category.assoc]
    exact isProjOver_comp_closed e hproj


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem weak_resolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  intro hP F _ _ W _ p n hp hdim
  obtain ⟨N, i₀, hi₀, hi₀p⟩ := hp
  obtain ⟨ℓ, hℓ, hℓs, hℓd⟩ := _root_.GlobalTheory.LinearCodimTwo.exists_linear_closedImmersion_two_le_ringKrullDim_stalk F N
  let i := i₀ ≫ ℓ
  let f := PSpace.str F (N + 2)
  have hif : i ≫ f = p := by simp [i, f, hℓs, hi₀p]
  have hsmf : SmoothOfRelativeDimension (N + 2) f := Adelic.smoothOfRelativeDimension_pspace F _
  have : Smooth f := by haveI := hsmf; exact SmoothOfRelativeDimension.smooth (N + 2) f
  have : IsLocallyNoetherian (PSpace F (N + 2)) := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hne, hnc⟩ := _root_.GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier i (hℓd _)
  obtain ⟨Y', s, -, -, -, hseq, -, hE, -⟩ := hP F (N + 2) _ f inferInstance hsmf
    (ProjSpace.isProjOver_pspace_str F _) i.ker hne
  rcases _root_.GlobalTheory.isIso_near_or_centre_meets f _ (i (genericPoint W)) s hseq with ⟨U, hU, hiso⟩ |
    ⟨Y₁, s₁, J, U, y₁, hseq₁, hsm, hJB, hU, hiso, hy₁, hs₁⟩
  · exact (hnc U hU (_root_.GlobalTheory.effCartier_comap_of_isIso_restrict s _ U hiso hE)).elim
  · obtain ⟨z, hz⟩ : ∃ z, J.subschemeι z = y₁ := by
      rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]; exact hy₁
    obtain ⟨W', j, hjc, hjo, hW', w', rfl⟩ := _root_.GlobalTheory.exists_clopen_integral_of_smooth_over_field F J.subscheme (J.subschemeι ≫ s₁ ≫ f) hsm z
    have hg : ∀ w, (j ≫ J.subschemeι ≫ s₁) w ∈ i.ker.support := fun w =>
      hJB (Scheme.IdealSheafData.range_subschemeι J ▸ Set.mem_range_self _)
    have : IsReduced W' := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support i (j ≫ J.subschemeι ≫ s₁) hg
    have hw' : h w' = genericPoint W := by
      apply i.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hh]
      simp [hz, hs₁]
    obtain ⟨U', hU'ne, hU'iso⟩ := _root_.GlobalTheory.isIso_restrict_of_closedImmersion_near_generic i h (j ≫ J.subschemeι) s₁ U hiso (by rw [hh]; simp)
      hU ⟨w', hw'⟩
    have hq : h ≫ p = j ≫ J.subschemeι ≫ s₁ ≫ f := by rw [← hif, reassoc_of% hh]
    have : Smooth (j ≫ J.subschemeι ≫ s₁ ≫ f) := by
      have := hsm; infer_instance
    have hpft : LocallyOfFiniteType p := by rw [← hif]; infer_instance
    have hd := _root_.GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F W W' p (h ≫ p) h hpft (by rw [hq]; infer_instance) rfl U' hU'ne hU'iso
    refine ⟨W', h, U', hW', ?_, ?_, hU'ne, hU'iso⟩
    · rw [hq]; exact _root_.GlobalTheory.RelDimOfDim.smoothOfRelativeDimension_of_topologicalKrullDim_eq F W' _ n inferInstance (hd.trans hdim)
    · rw [hq, ← Category.assoc]
      exact isProjOver_comp_closed _ (isProjOver_seq f hseq₁ (ProjSpace.isProjOver_pspace_str F _))

end GlobalTheory.WeakRes
end
end

