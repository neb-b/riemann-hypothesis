module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.KrullDimClosedSubset
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IsomorphismTransport
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem smooth_ker_subschemeι_comp {k : Type u} [Field k] {X X' : Scheme.{u}}
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X')
    [AlgebraicGeometry.IsClosedImmersion τ] [AlgebraicGeometry.Smooth (τ ≫ p)] :
    AlgebraicGeometry.Smooth (τ.ker.subschemeι ≫ p) := by
  have hinv : inv τ.toImage ≫ τ = τ.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr τ.toImage_imageι.symm
  have hcomp : τ.ker.subschemeι ≫ p = inv τ.toImage ≫ (τ ≫ p) := by
    rw [← Category.assoc, hinv]
  rw [hcomp]
  infer_instance

theorem ker_le_map_idealSheaf {X X' : Scheme.{u}} (f : X ⟶ X') (I : X.IdealSheafData) :
    f.ker ≤ I.map f := by
  have hle : (⊥ : X.IdealSheafData).map f ≤ I.map f :=
    Scheme.IdealSheafData.map_mono f bot_le
  rwa [Scheme.IdealSheafData.map_bot] at hle

theorem orderAt_map_le_one_of_isClosedImmersion {k : Type u} [Field k] [CharZero k]
    {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ]
    [AlgebraicGeometry.Smooth (τ ≫ p)]
    (hker : NonzeroOnComponents τ.ker) (I : X.IdealSheafData) (x : ↥X') :
    orderAt (I.map τ) x ≤ 1 := by
  refine le_trans (orderAt_le_of_le (ker_le_map_idealSheaf τ I) x) ?_
  by_cases hx : x ∈ τ.ker.support
  · have : AlgebraicGeometry.Smooth (τ.ker.subschemeι ≫ p) := smooth_ker_subschemeι_comp p τ
    obtain ⟨U, m, c, S, hxU, hU, hD⟩ :=
      exists_chart_restrictIdeal_eq_coordIdeal p τ.ker x hx
    have hD' : τ.ker.comap U.ι = c.coordIdeal S := hD
    rcases S.eq_empty_or_nonempty with hS | ⟨j, hj⟩
    · subst hS
      exfalso
      have hcoord : c.coordIdeal (∅ : Finset (Fin m))
          = (⊥ : (affineSpaceFin k m).IdealSheafData).comap c.map := by
        rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_empty]
      have hUsupp : (U : Set ↥X') ⊆ (τ.ker.support : Set ↥X') := by
        intro y hy
        have hy' : y ∈ Set.range ⇑U.ι.base := by
          rw [Scheme.Opens.range_ι]
          exact hy
        obtain ⟨z, rfl⟩ := hy'
        have h1 : z ∈ ((τ.ker.comap U.ι).support : Set ↥U.toScheme) := by
          rw [hD', hcoord, support_comap_eq]
          simp [Scheme.IdealSheafData.support_bot]
        rw [support_comap_eq] at h1
        exact h1
      have hCmem : irreducibleComponent x ∈ irreducibleComponents ↥X' :=
        irreducibleComponent_mem_irreducibleComponents x
      refine hker _ hCmem ?_
      have hcl := closure_inter_open_eq (isClosed_irreducibleComponent)
        (isIrreducible_irreducibleComponent) U.2 ⟨x, mem_irreducibleComponent, hxU⟩
      rw [← hcl]
      refine closure_minimal ?_ (τ.ker.support).2
      exact fun y hy => hUsupp hy.2
    · exact orderAt_le_one_of_restrictIdeal_eq_coordIdeal p hU c S j hj τ.ker hD x hxU
  · have h0 : orderAt τ.ker x = 0 := (orderAt_eq_zero_iff_not_mem_support τ.ker x).mpr hx
    rw [h0]
    exact zero_le

theorem krullDimSucc_lt_of_isClosedImmersion_of_nonzeroOnComponents {k : Type u} [Field k]
    {X X' : Scheme.{u}} (p : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ] [Nonempty ↥X]
    (hker : NonzeroOnComponents τ.ker) :
    krullDimSucc X < krullDimSucc X' := by
  have hfin : topologicalKrullDim ↥X' < ⊤ :=
    topologicalKrullDim_lt_top_of_finiteType p ‹AlgebraicGeometry.LocallyOfFiniteType p›
      ‹AlgebraicGeometry.QuasiCompact p›
  have hemb : Topology.IsClosedEmbedding ⇑τ.base :=
    AlgebraicGeometry.Scheme.Hom.isClosedEmbedding τ
  obtain ⟨z⟩ := ‹Nonempty ↥X›
  refine krullDimSucc_lt_of_homeomorph_isClosed X' X (Set.range ⇑τ.base) hemb.isClosed_range
    ⟨τ.base z, z, rfl⟩ ?_ hfin hemb.toIsEmbedding.toHomeomorph
  intro C hC hsub
  exact hker C hC (hsub.trans τ.range_subset_ker_support)

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace IsPushforwardBlowupSeq

private theorem ker_comp_eq_ker_subschemeι_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Scheme.Hom.ker (f ≫ g) = Scheme.Hom.ker ((Scheme.Hom.ker f).subschemeι ≫ g) :=
  (ker_comp_eq_imageIdealSheaf_ker f g).trans (imageIdealSheaf_eq_ker g f.ker)

theorem comp {Y H X : Scheme.{u}} (σ : Y ⟶ H) [IsClosedImmersion σ]
    (ρ : H ⟶ X) [IsClosedImmersion ρ]
    {s : SequenceOfBlowups Y} {t : SequenceOfBlowups H} {u : SequenceOfBlowups X}
    (hNt : ∀ i : ℕ, i ≤ t.length → AlgebraicGeometry.IsNoetherian (t.schemeAt i))
    (hNu : ∀ i : ℕ, i ≤ u.length → AlgebraicGeometry.IsNoetherian (u.schemeAt i))
    (hst : IsPushforwardBlowupSeq σ s t) (htu : IsPushforwardBlowupSeq ρ t u) :
    IsPushforwardBlowupSeq (σ ≫ ρ) s u := by
  obtain ⟨hl1, a, haci, ha0, hasq, hac, hak⟩ := hst
  obtain ⟨hl2, b, hbci, hb0, hbsq, hbc, hbk⟩ := htu
  refine ⟨hl1.trans hl2, fun i hi => a i hi ≫ b i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hit : i ≤ t.length := by omega
    have := haci i hi
    have := hbci i hit
    show IsClosedImmersion (a i hi ≫ b i hit)
    infer_instance
  · show (a 0 (Nat.zero_le _) ≫ b 0 (Nat.zero_le _)) ≫ u.isoZero.hom
      = s.isoZero.hom ≫ (σ ≫ ρ)
    rw [Category.assoc, hb0, ← Category.assoc, ha0, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    show (a (i + 1) hi ≫ b (i + 1) hit) ≫ u.transitionMapSucc i
      = s.transitionMapSucc i ≫ (a i hi.le ≫ b i hit.le)
    rw [Category.assoc, hbsq i hit, ← Category.assoc, hasq i hi, Category.assoc]
  · intro i hi
    have hit : i < t.length := by omega
    have := haci i hi.le
    have := hbci i hit.le
    show u.center i = imageIdealSheaf (a i hi.le ≫ b i hit.le) (s.center i)
    rw [hbc i hit, hac i hi, imageIdealSheaf_comp]
  · intro i hi
    have hit : i < t.length := by omega
    have hiu : i < u.length := by omega
    have := hbci i hit.le
    have := hbci (i + 1) hit
    have := haci i hi.le
    have := haci (i + 1) hi
    have := hNt (i + 1) hit
    have := hNu (i + 1) hiu
    have hker : Scheme.Hom.ker (b (i + 1) hit)
        = Blowup.strictTransform (u.transitionMapSucc i)
            (Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le))
            (Scheme.Hom.ker (b i hit.le)) := by
      rw [hbk i hit, hbc i hit, imageIdealSheaf_eq_ker]
    have key := image_strictTransform_eq_strictTransform_image (b i hit.le) (t.center i)
      (Scheme.Hom.ker (a i hi.le)) (t.transitionMapSucc i) (u.transitionMapSucc i) (b (i + 1) hit)
      (hbsq i hit) hker
    have hL : Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
        = Scheme.Hom.ker ((Blowup.strictTransform (t.transitionMapSucc i) (t.center i)
            (Scheme.Hom.ker (a i hi.le))).subschemeι ≫ b (i + 1) hit) := by
      rw [ker_comp_eq_ker_subschemeι_comp, hak i hi]
    have hD : Scheme.Hom.ker (a i hi.le ≫ b i hit.le)
        = Scheme.Hom.ker ((Scheme.Hom.ker (a i hi.le)).subschemeι ≫ b i hit.le) :=
      ker_comp_eq_ker_subschemeι_comp _ _
    have hC : u.center i = Scheme.Hom.ker ((t.center i).subschemeι ≫ b i hit.le) := by
      rw [hbc i hit, imageIdealSheaf_eq_ker]
    show Scheme.Hom.ker (a (i + 1) hi ≫ b (i + 1) hit)
      = Blowup.strictTransform (u.transitionMapSucc i) (u.center i)
          (Scheme.Hom.ker (a i hi.le ≫ b i hit.le))
    rw [hL, key, hC, hD]

theorem of_isomorphic_source {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {s s' : SequenceOfBlowups S} {t : SequenceOfBlowups X}
    (hs : s.Isomorphic s') (h : IsPushforwardBlowupSeq j s t) :
    IsPushforwardBlowupSeq j s' t := by
  obtain ⟨hlen, e, h0, hsqe, hce⟩ := hs
  have hpb : IsStrictPullbackBlowupSeq (𝟙 S) s' s := by
    refine ⟨hlen.symm, fun i hi => (e i (by omega)).inv, ?_, ?_, ?_⟩
    · show (e 0 (Nat.zero_le _)).inv ≫ s.isoZero.hom = s'.isoZero.hom ≫ 𝟙 S
      rw [Category.comp_id, ← h0, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    · intro i hi
      have hi' : i < s.length := by omega
      have hsq : (e (i + 1) hi').inv ≫ s.transitionMapSucc i
          = s'.transitionMapSucc i ≫ (e i hi'.le).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, hsqe i hi', Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      show IsPullback ((e (i + 1) hi').inv) (s'.transitionMapSucc i) (s.transitionMapSucc i)
        ((e i hi'.le).inv)
      exact IsPullback.of_horiz_isIso ⟨hsq⟩
    · intro i hi
      have hi' : i < s.length := by omega
      have h1 : imageIdealSheaf (e i hi'.le).hom ((s'.center i).comap (e i hi'.le).hom)
          = imageIdealSheaf (e i hi'.le).hom (s.center i) := by rw [hce i hi']
      rw [imageIdealSheaf_comap] at h1
      have h2 : inv (e i hi'.le).hom = (e i hi'.le).inv :=
        IsIso.inv_eq_of_hom_inv_id (Iso.hom_inv_id (e i hi'.le))
      show s'.center i = (s.center i).comap ((e i hi'.le).inv)
      rw [h1, imageIdealSheaf_eq_comap_inv, h2]
  exact IsPushforwardBlowupSeq.isIso_comp (𝟙 S) j j (Category.id_comp j).symm hpb h

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
section
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

private theorem flat_of_isPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D}
    (sq : IsPullback a b c d) (hd : AlgebraicGeometry.Flat d) :
    AlgebraicGeometry.Flat a := by
  have := hd
  have : AlgebraicGeometry.Flat (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

private theorem isClosedImmersion_of_isPullback {A B C D : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ D} {d : C ⟶ D}
    (sq : IsPullback a b c d) (hd : IsClosedImmersion d) : IsClosedImmersion a := by
  have := hd
  have : IsClosedImmersion (pullback.snd d c) := inferInstance
  rw [← sq.flip.isoPullback_hom_snd]
  infer_instance

theorem comp_projectionToBase_of_comp_blowupMorphism {S X : Scheme.{u}} (s : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (L : ℕ) (j : S ⟶ X) (σ : ∀ i : ℕ, i ≤ L → (s.schemeAt i ⟶ t.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ t.isoZero.hom = s.isoZero.hom ≫ j)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      σ (i + 1) hi ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ σ i hi.le) :
    ∀ b : ℕ, ∀ hb : b ≤ L, σ b hb ≫ t.projectionToBase b = s.projectionToBase b ≫ j := by
  intro b
  induction b with
  | zero =>
    intro hb
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero]
    exact hzero
  | succ n ih =>
    intro hb
    have hn : n < L := hb
    have h1 := hstep n hn
    rw [SequenceOfBlowups.projectionToBase_succ, SequenceOfBlowups.projectionToBase_succ, ← Category.assoc, h1,
      Category.assoc, ih hn.le, Category.assoc]

namespace IsPushforwardBlowupSeq

theorem of_flat_isPullback {S X S' X' : Scheme.{u}}
    (j : S ⟶ X) (j' : S' ⟶ X') (g : X' ⟶ X) (p : S' ⟶ S)
    [IsClosedImmersion j] [IsClosedImmersion j'] [AlgebraicGeometry.Flat g]
    (hsq : IsPullback j' p g j)
    (s : SequenceOfBlowups S) (t : SequenceOfBlowups X) (s' : SequenceOfBlowups S') (t' : SequenceOfBlowups X')
    (hnoeth : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (hnoeth' : ∀ i : ℕ, i ≤ t'.length → IsLocallyNoetherian (t'.schemeAt i))
    (hpush : IsPushforwardBlowupSeq j s t)
    (hs' : IsStrictPullbackBlowupSeq p s' s)
    (ht' : IsStrictPullbackBlowupSeq g t' t) :
    IsPushforwardBlowupSeq j' s' t' := by
  obtain ⟨hlen1, σ, hσci, hσ0, hσstep, hσcen, hσker⟩ := hpush
  obtain ⟨hlen2, τ, hτ0, hτstep, hτcen⟩ := hs'
  obtain ⟨hlen3, ρ, hρ0, hρstep, hρcen⟩ := ht'
  have hA : ∀ i : ℕ, i ≤ s'.length → i ≤ s.length := fun i hi => by omega
  have hB : ∀ i : ℕ, i ≤ s'.length → i ≤ t'.length := fun i hi => by omega
  have Pt := isPullback_projectionToBase_of_isPullback_blowupMorphism g t' t t'.length ρ hρ0 hρstep
  have Ps := isPullback_projectionToBase_of_isPullback_blowupMorphism p s' s s'.length τ hτ0 hτstep
  have hσS := comp_projectionToBase_of_comp_blowupMorphism s t s.length j σ hσ0 hσstep
  have hflatρ : ∀ i : ℕ, ∀ hi : i ≤ t'.length, AlgebraicGeometry.Flat (ρ i hi) := fun i hi =>
    flat_of_isPullback (Pt i hi) inferInstance
  have hw : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      (τ i hi ≫ σ i (hA i hi)) ≫ t.projectionToBase i = (s'.projectionToBase i ≫ j') ≫ g := by
    intro i hi
    rw [Category.assoc, hσS i (hA i hi), ← Category.assoc, (Ps i hi).w, Category.assoc,
      ← hsq.w, Category.assoc]
  obtain ⟨σ', hσ'1, hσ'2⟩ :
      ∃ σ' : ∀ i : ℕ, i ≤ s'.length → (s'.schemeAt i ⟶ t'.schemeAt i),
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ ρ i (hB i hi) = τ i hi ≫ σ i (hA i hi)) ∧
        (∀ i : ℕ, ∀ hi : i ≤ s'.length,
          σ' i hi ≫ t'.projectionToBase i = s'.projectionToBase i ≫ j') :=
    ⟨fun i hi => (Pt i (hB i hi)).lift (τ i hi ≫ σ i (hA i hi)) (s'.projectionToBase i ≫ j') (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_fst _ _ (hw i hi),
      fun i hi => (Pt i (hB i hi)).lift_snd _ _ (hw i hi)⟩
  have Psq : ∀ i : ℕ, ∀ hi : i ≤ s'.length,
      IsPullback (σ' i hi) (τ i hi) (ρ i (hB i hi)) (σ i (hA i hi)) := by
    intro i hi
    refine IsPullback.of_right ?_ (hσ'1 i hi) (Pt i (hB i hi)).flip
    rw [hσ'2 i hi, hσS i (hA i hi)]
    exact ((Ps i hi).flip).paste_horiz hsq
  have hci' : ∀ i : ℕ, ∀ hi : i ≤ s'.length, IsClosedImmersion (σ' i hi) := fun i hi =>
    isClosedImmersion_of_isPullback (Psq i hi) (hσci i (hA i hi))
  have hzero' : σ' 0 (Nat.zero_le _) ≫ t'.isoZero.hom = s'.isoZero.hom ≫ j' := by
    have h := hσ'2 0 (Nat.zero_le _)
    rwa [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.projectionToBase_zero] at h
  have hstep' : ∀ i : ℕ, ∀ hi : i < s'.length,
      σ' (i + 1) hi ≫ t'.transitionMapSucc i = s'.transitionMapSucc i ≫ σ' i hi.le := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    refine (Pt i (hB i hi.le)).hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← (hρstep i hit).w, hσ'1 i hi.le, ← Category.assoc, hσ'1 (i + 1) hi,
        Category.assoc, hσstep i his, ← Category.assoc, (hτstep i hi).w, Category.assoc]
    · simp only [Category.assoc]
      rw [← SequenceOfBlowups.projectionToBase_succ, hσ'2 (i + 1) hi, hσ'2 i hi.le,
        SequenceOfBlowups.projectionToBase_succ, Category.assoc]
  have hcen' : ∀ i : ℕ, ∀ hi : i < s'.length,
      t'.center i = imageIdealSheaf (σ' i hi.le) (s'.center i) := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have := hσci i (hA i hi.le)
    have : QuasiCompact (σ i (hA i hi.le)) := inferInstance
    have := hflatρ i (hB i hi.le)
    rw [hρcen i hit, hτcen i hi, hσcen i his, ← map_eq_imageIdealSheaf, ← map_eq_imageIdealSheaf]
    exact comap_map_eq_map_comap_of_isPullback (Psq i hi.le).flip (s.center i)
  have hker' : ∀ i : ℕ, ∀ hi : i < s'.length,
      (σ' (i + 1) hi).ker =
        Blowup.strictTransform (t'.transitionMapSucc i) (t'.center i) (σ' i hi.le).ker := by
    intro i hi
    have hit : i < t'.length := by omega
    have his : i < s.length := by omega
    have hitt : i < t.length := by omega
    have := hσci i (hA i hi.le)
    have := hσci (i + 1) (hA (i + 1) hi)
    have := hci' i hi.le
    have := hci' (i + 1) hi
    have := hflatρ i (hB i hi.le)
    have := hflatρ (i + 1) (hB (i + 1) hi)
    have : IsLocallyNoetherian (t.schemeAt (i + 1)) := hnoeth (i + 1) (by omega)
    have : IsLocallyNoetherian (t'.schemeAt (i + 1)) := hnoeth' (i + 1) (by omega)
    rw [ker_eq_comap_ker_of_isPullback_of_flat (Psq (i + 1) hi).flip,
      ker_eq_comap_ker_of_isPullback_of_flat (Psq i hi.le).flip, hσker i his, hρcen i hit]
    exact comap_strictTransform_of_flat_of_isLocallyNoetherian (t.transitionMapSucc i)
      (ρ i (hB i hi.le)) (t'.transitionMapSucc i) (ρ (i + 1) (hB (i + 1) hi)) (hρstep i hit)
      (t.center i) (σ i (hA i hi.le)).ker (t.isBlowupAlongIdealSheaf_blowupMorphism i hitt)
  have hlen : s'.length = t'.length := by omega
  exact And.intro hlen (Exists.intro σ' ⟨hci', hzero', hstep', hcen', hker'⟩)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
end

