module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupRemoval
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem imageIdealSheaf_top {S X : Scheme.{u}} (σ : S ⟶ X) :
    imageIdealSheaf σ (⊤ : S.IdealSheafData) = ⊤ := by
  have hemp : IsEmpty ↥(⊤ : S.IdealSheafData).subscheme := inferInstance
  have hqc : QuasiCompact ((⊤ : S.IdealSheafData).subschemeι ≫ σ) := by
    constructor
    intro U _ _
    convert isCompact_empty
    exact Set.eq_empty_of_isEmpty _
  rw [imageIdealSheaf_eq_ker, ← Scheme.IdealSheafData.support_eq_bot_iff]
  have hs := Scheme.Hom.support_ker ((⊤ : S.IdealSheafData).subschemeι ≫ σ)
  rw [Set.range_eq_empty, closure_empty] at hs
  refine SetLike.coe_injective ?_
  rw [hs]
  simp

private theorem imageIdealSheaf_eq_top_iff {S X : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ]
    (I : S.IdealSheafData) : imageIdealSheaf σ I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro hI
    have h2 : (imageIdealSheaf σ I).comap σ = I := Blowup.comap_schemeImageIdeal σ I
    rw [hI] at h2
    rw [← h2]
    simp
  · rintro rfl
    exact imageIdealSheaf_top σ

private theorem eqToHom_projectionToBase {Sc : Scheme.{u}} (t : SequenceOfBlowups Sc) {a a' : ℕ} (ha : a = a') :
    eqToHom (congrArg t.schemeAt ha) ≫ t.projectionToBase a' = t.projectionToBase a := by
  subst ha
  simp

private theorem comp_eqToHom_comp_transitionMap {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a) (u : C ⟶ A)
    (H : g ≫ t.transitionMap hab = u ≫ f) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)) ≫ t.transitionMap hab'
      = u ≫ (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  subst hb
  simpa using H

private theorem isClosedImmersion_comp_eqToHom {Sc A : Scheme.{u}} (t : SequenceOfBlowups Sc) {a a' : ℕ}
    (ha : a = a') (f : A ⟶ t.schemeAt a) (hf : IsClosedImmersion f) :
    IsClosedImmersion (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  simpa using hf

private theorem center_eq_imageIdealSheaf_comp_eqToHom {Sc A : Scheme.{u}} (t : SequenceOfBlowups Sc)
    (I : A.IdealSheafData) {a a' : ℕ} (ha : a = a') (f : A ⟶ t.schemeAt a)
    (hf : t.center a = imageIdealSheaf f I) :
    t.center a' = imageIdealSheaf (f ≫ eqToHom (congrArg t.schemeAt ha)) I := by
  subst ha
  simpa using hf

private theorem ker_comp_eqToHom_eq_strictTransform {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc)
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a)
    (H : g.ker = Blowup.strictTransform (t.transitionMap hab) (t.center a) f.ker) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)).ker
      = Blowup.strictTransform (t.transitionMap hab') (t.center a') (f ≫ eqToHom (congrArg t.schemeAt ha)).ker := by
  subst ha
  subst hb
  simpa using H

theorem isPushforwardSequenceOfBlowups_withoutIsoBlowups {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (B : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (hN : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (h : IsPushforwardBlowupSeq j B t) :
    IsPushforwardBlowupSeq j B.withoutIsoBlowups t.withoutIsoBlowups := by
  obtain ⟨hlen, σ, hci, h0, hsq, hcen, hker⟩ := h
  have htriv : ∀ i : ℕ, i < B.length → (B.center i = ⊤ ↔ t.center i = ⊤) := by
    intro i hi
    have := hci i hi.le
    rw [hcen i hi]
    exact (imageIdealSheaf_eq_top_iff (σ i hi.le) (B.center i)).symm
  have hretf : B.nontrivialIndex = t.nontrivialIndex :=
    SequenceOfBlowups.nontrivialIndex_congr_of_center_eq_top_iff B t hlen htriv
  have hplen : B.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups :=
    SequenceOfBlowups.lengthWithoutIsoBlowups_congr_of_center_eq_top_iff B t hlen htriv
  have hret : ∀ i : ℕ, B.nontrivialIndex i = t.nontrivialIndex i := fun i => congrFun hretf i
  have hdown : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ B.length),
      σ b hb ≫ t.transitionMap hab = B.transitionMap hab ≫ σ a (le_trans hab hb) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro hb
        rw [t.transitionMap_self, B.transitionMap_self, Category.comp_id, Category.id_comp]
    | succ b hab ih =>
        intro hb
        have hbl : b < B.length := hb
        have e1 : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans hab (Nat.le_succ b)
        have e2 : B.transitionMapSucc b ≫ B.transitionMap hab = B.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact B.transitionMap_trans hab (Nat.le_succ b)
        rw [← e1, ← Category.assoc, hsq b hbl, Category.assoc, ih hbl.le, ← Category.assoc, e2]
  have hstruct : ∀ (i : ℕ) (hi : i ≤ B.length),
      σ i hi ≫ t.projectionToBase i = B.projectionToBase i ≫ j := by
    intro i hi
    have hd := hdown 0 i (Nat.zero_le i) hi
    rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.projectionToBase_def, ← Category.assoc (σ i hi), hd]
    simp only [Category.assoc, h0]
  have key : ∀ (a c : ℕ) (hac : a + 1 ≤ c), (∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤) →
      ∀ (hc : c ≤ B.length) (ha : a < B.length),
      (σ c hc).ker
        = Blowup.strictTransform (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) (σ a ha.le).ker := by
    intro a c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ hc ha
        have hk := hker a ha
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap] at hk
        exact hk
    | succ c hac ih =>
        intro htop hc ha
        have hcl : c < B.length := hc
        have hc' : c ≤ B.length := le_of_lt hcl
        have htopc : ∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤ :=
          fun d hd1 hd2 => htop d hd1 (Nat.lt_succ_of_lt hd2)
        have hctop : t.center c = ⊤ := htop c hac (Nat.lt_succ_self c)
        have : IsLocallyNoetherian (t.schemeAt c) := hN c (by omega)
        have : IsLocallyNoetherian (t.schemeAt (c + 1)) := hN (c + 1) (by omega)
        have ihc := ih htopc hc' ha
        have hk := hker c hcl
        rw [hctop, strictTransform_top_eq_comap (t.transitionMapSucc c) ((σ c hcl.le).ker), ihc] at hk
        have hiso : IsIso (t.transitionMapSucc c) := by
          have hB := t.isBlowupAlongIdealSheaf_blowupMorphism c (by omega)
          rw [hctop] at hB
          exact hB.isIso_of_top
        have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) := by
          have : IsIso (t.transitionMap hac) := t.isIso_transitionMap_of_center_eq_top hac (by omega) htopc
          have hB : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc a) (t.center a) := t.isBlowupAlongIdealSheaf_blowupMorphism a (by omega)
          have hcomp := hB.iso_hom_comp (asIso (t.transitionMap hac))
          have heq2 : (asIso (t.transitionMap hac)).hom ≫ t.transitionMapSucc a
              = t.transitionMap (Nat.le_of_succ_le hac) := by
            rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
            exact t.transitionMap_trans (Nat.le_succ a) hac
          rw [heq2] at hcomp
          exact hcomp
        have heq : t.transitionMapSucc c ≫ t.transitionMap (Nat.le_of_succ_le hac)
            = t.transitionMap (Nat.le_of_succ_le (le_trans hac (Nat.le_succ c))) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans (Nat.le_of_succ_le hac) (Nat.le_succ c)
        rw [hk, ← strictTransform_isIso_comp (t.transitionMapSucc c) (t.transitionMap (Nat.le_of_succ_le hac))
          (t.center a) ((σ a ha.le).ker) hbl, heq]
  have h1 : ∀ (i : ℕ) (hi : i ≤ B.lengthWithoutIsoBlowups),
      IsClosedImmersion (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
        eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    exact isClosedImmersion_comp_eqToHom t (hret i) _ (hci _ _)
  have h2 : (σ (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups)) ≫
      eqToHom (congrArg t.schemeAt (hret 0))) ≫ t.withoutIsoBlowups.isoZero.hom
      = B.withoutIsoBlowups.isoZero.hom ≫ j := by
    simp only [SequenceOfBlowups.withoutIsoBlowups_isoObjZero, SequenceOfBlowups.objNontrivialIndexZeroIso_hom]
    rw [Category.assoc, eqToHom_projectionToBase t (hret 0)]
    exact hstruct (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups))
  have h3 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))) ≫ t.withoutIsoBlowups.transitionMapSucc i
        = B.withoutIsoBlowups.transitionMapSucc i ≫
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism]
    exact comp_eqToHom_comp_transitionMap t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
      (t.nontrivialIndex_monotone (Nat.le_succ i) : t.nontrivialIndex i ≤ t.nontrivialIndex (i + 1)) _ _ _
      (hdown (B.nontrivialIndex i) (B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_le_length hi))
  have h4 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      t.withoutIsoBlowups.center i = imageIdealSheaf (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
        eqToHom (congrArg t.schemeAt (hret i))) (B.withoutIsoBlowups.center i) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_center]
    exact center_eq_imageIdealSheaf_comp_eqToHom t (B.center (B.nontrivialIndex i)) (hret i) _
      (hcen (B.nontrivialIndex i) (B.nontrivialIndex_lt_length hi))
  have h5 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))).ker
        = Blowup.strictTransform (t.withoutIsoBlowups.transitionMapSucc i) (t.withoutIsoBlowups.center i)
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))).ker := by
    intro i hi
    have htopd : ∀ d : ℕ, B.nontrivialIndex i + 1 ≤ d → d < B.nontrivialIndex (i + 1) → t.center d = ⊤ := by
      intro d hd1 hd2
      have hdlt : d < B.length := lt_of_lt_of_le hd2 (B.nontrivialIndex_le_length hi)
      exact (htriv d hdlt).1 (B.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hd1) hd2)
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism, SequenceOfBlowups.withoutIsoBlowups_center]
    exact ker_comp_eqToHom_eq_strictTransform t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i))
      (t.nontrivialIndex_monotone (Nat.le_succ i)) _ _
      (key (B.nontrivialIndex i) (B.nontrivialIndex (i + 1)) (B.succ_le_nontrivialIndex_succ i) htopd
        (B.nontrivialIndex_le_length hi) (B.nontrivialIndex_lt_length hi))
  exact ⟨hplen, fun i hi => σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
    eqToHom (congrArg t.schemeAt (hret i)), h1, h2, h3, h4, h5⟩

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem comap_eq_ker_of_mono {U V : Scheme.{u}} (j : U ⟶ V) [Mono j]
    (I : V.IdealSheafData) (lam : I.subscheme ⟶ U) (hlam : lam ≫ j = I.subschemeι) :
    I.comap j = Scheme.Hom.ker lam := by
  have hc : I.comap j = Scheme.Hom.ker (Limits.pullback.fst j I.subschemeι) := rfl
  have hcomm : lam ≫ j = 𝟙 I.subscheme ≫ I.subschemeι := by rw [hlam, Category.id_comp]
  obtain ⟨e, hefst, hesnd⟩ : ∃ e : I.subscheme ⟶ Limits.pullback j I.subschemeι,
      e ≫ Limits.pullback.fst j I.subschemeι = lam ∧
        e ≫ Limits.pullback.snd j I.subschemeι = 𝟙 I.subscheme :=
    ⟨Limits.pullback.lift lam (𝟙 I.subscheme) hcomm, Limits.pullback.lift_fst _ _ _,
      Limits.pullback.lift_snd _ _ _⟩
  have hsndlam : Limits.pullback.snd j I.subschemeι ≫ lam
      = Limits.pullback.fst j I.subschemeι := by
    rw [← cancel_mono j, Category.assoc, hlam, ← Limits.pullback.condition]
  have : IsIso e := by
    refine ⟨Limits.pullback.snd j I.subschemeι, hesnd, ?_⟩
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, hsndlam, Category.id_comp]
    · rw [Category.assoc, hesnd, Category.comp_id, Category.id_comp]
  rw [hc]
  exact (ker_eq_ker_of_isIso_comp lam (Limits.pullback.fst j I.subschemeι) e hefst).symm

theorem map_eq_ker_subschemeι_comp {U V : Scheme.{u}} (j : U ⟶ V) (K : U.IdealSheafData) :
    K.map j = Scheme.Hom.ker (K.subschemeι ≫ j) := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]

theorem ker_subschemeι_comp_eq_of_ker_le {U V : Scheme.{u}} (j : U ⟶ V) [IsClosedImmersion j]
    (L : V.IdealSheafData) (hL : Scheme.Hom.ker j ≤ L) (K : U.IdealSheafData)
    (hK : K = L.comap j) :
    Scheme.Hom.ker (K.subschemeι ≫ j) = L := by
  have hle : Scheme.Hom.ker j ≤ Scheme.Hom.ker L.subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact hL
  have hfac : IsClosedImmersion.lift j L.subschemeι hle ≫ j = L.subschemeι := by
    rw [IsClosedImmersion.lift_fac]
  have hcomap : L.comap j = Scheme.Hom.ker (IsClosedImmersion.lift j L.subschemeι hle) :=
    comap_eq_ker_of_mono j L (IsClosedImmersion.lift j L.subschemeι hle) hfac
  rw [hK, hcomap, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.Hom.ker_comp, hfac, Scheme.IdealSheafData.ker_subschemeι]

theorem strictTransform_eq_ker_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D =
      Scheme.Hom.ker
        (((D.comap π).comap (Scheme.Opens.ι (complComapSupport π Z))).subschemeι ≫
          Scheme.Opens.ι (complComapSupport π Z)) := by
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq,
    ← complComapSupport_eq]
  exact ker_ι_preimage_comp_subschemeι_eq_ker_comap (D.comap π) (complComapSupport π Z)

theorem preimage_complComapSupport_eq {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A') [IsClosedImmersion j]
    (Z : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    (hsq : j₁ ≫ π' = π ≫ j) :
    (Opens.map j₁.base).obj (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) =
      complComapSupport π Z := by
  have key : ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').comap j₁ = Z.comap π := by
    rw [← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
      ← map_eq_ker_subschemeι_comp, Blowup.comap_map_of_isClosedImmersion]
  have h2 : ((Z.comap π).support : Set A₁)
      = ⇑j₁.base ⁻¹'
        ((((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)) := by
    rw [← key, Scheme.IdealSheafData.support_comap
      ((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π') j₁]
    rfl
  apply TopologicalSpace.Opens.ext
  have h1 : (((Opens.map j₁.base).obj
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))) : Set A₁)
      = ⇑j₁.base ⁻¹' (((Scheme.Hom.ker (Z.subschemeι ≫ j)).comap π').support : Set A'₁)ᶜ := rfl
  rw [h1, coe_complComapSupport, h2, Set.preimage_compl]

private theorem map_ker_subschemeι_comp_restrict {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j]
    (D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁) [IsClosedImmersion j₁]
    (hsq : j₁ ≫ π' = π ≫ j) (V' : A'₁.Opens) [IsClosedImmersion (j₁ ∣_ V')]
    (hkerr : Scheme.Hom.ker (j₁ ∣_ V') ≤
      ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) :
    (Scheme.Hom.ker (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι)).map j₁
      = Scheme.Hom.ker
          ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι ≫ V'.ι) := by
  have hm : (j₁ ∣_ V') ≫ V'.ι ≫ π' = (j₁ ⁻¹ᵁ V').ι ≫ π ≫ j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hsq]
  have hMcomap :
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
    calc ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).comap (j₁ ∣_ V'))
        = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ∣_ V') ≫ V'.ι ≫ π') := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ∣_ V') (V'.ι ≫ π'),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) V'.ι π']
      _ = (Scheme.Hom.ker (D.subschemeι ≫ j)).comap ((j₁ ⁻¹ᵁ V').ι ≫ π ≫ j) := by rw [hm]
      _ = (D.comap π).comap (j₁ ⁻¹ᵁ V').ι := by
          rw [Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j))
              (j₁ ⁻¹ᵁ V').ι (π ≫ j),
            Scheme.IdealSheafData.comap_comp (Scheme.Hom.ker (D.subschemeι ≫ j)) π j,
            ← map_eq_ker_subschemeι_comp j D, Blowup.comap_map_of_isClosedImmersion j D]
  have hmor : ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ⁻¹ᵁ V').ι) ≫ j₁)
      = ((((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) ≫ V'.ι) := by
    simp only [Category.assoc, morphismRestrict_ι]
  rw [← Scheme.Hom.ker_comp, hmor,
    Scheme.Hom.ker_comp (((D.comap π).comap (j₁ ⁻¹ᵁ V').ι).subschemeι ≫ (j₁ ∣_ V')) V'.ι,
    ker_subschemeι_comp_eq_of_ker_le (j₁ ∣_ V')
      (((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι) hkerr
      ((D.comap π).comap (j₁ ⁻¹ᵁ V').ι) hMcomap.symm,
    Scheme.Hom.ker_comp
      ((((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap V'.ι).subschemeι) V'.ι,
    Scheme.IdealSheafData.ker_subschemeι]

theorem image_strictTransform_eq_strictTransform_image {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j)) (Scheme.Hom.ker j)) :
    Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) =
      Blowup.strictTransform π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker (D.subschemeι ≫ j)) := by
  have : IsClosedImmersion
      (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) := inferInstance
  have hDle : Scheme.Hom.ker j ≤ Scheme.Hom.ker (D.subschemeι ≫ j) := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι,
      ← Scheme.IdealSheafData.map_bot j]
    exact Scheme.IdealSheafData.map_mono j bot_le
  have hUeq : j₁ ⁻¹ᵁ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
      = complComapSupport π Z := preimage_complComapSupport_eq j Z π π' j₁ hsq
  have hkerr : Scheme.Hom.ker (j₁ ∣_ complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j)))
      ≤ ((Scheme.Hom.ker (D.subschemeι ≫ j)).comap π').comap
          (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι := by
    rw [← ker_comap_ι_eq_ker_morphismRestrict j₁
        (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))), hker,
      strictTransform_comap_complComapSupport_ι π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
        (Scheme.Hom.ker j)]
    exact Scheme.IdealSheafData.comap_mono
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))).ι
      (Scheme.IdealSheafData.comap_mono π' hDle)
  have hTmap : Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁)
      = (Blowup.strictTransform π Z D).map j₁ := by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  rw [hTmap, strictTransform_eq_ker_complComapSupport π Z D, ← hUeq,
    map_ker_subschemeι_comp_restrict j D π π' j₁ hsq
      (complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))) hkerr]
  exact (strictTransform_eq_ker_complComapSupport π' (Scheme.Hom.ker (Z.subschemeι ≫ j))
    (Scheme.Hom.ker (D.subschemeι ≫ j))).symm

theorem map_strictTransform_eq_strictTransform_map {A A' A₁ A'₁ : Scheme.{u}} (j : A ⟶ A')
    [IsClosedImmersion j] (Z D : A.IdealSheafData) (π : A₁ ⟶ A) (π' : A'₁ ⟶ A') (j₁ : A₁ ⟶ A'₁)
    [IsClosedImmersion j₁] [IsNoetherian A₁] [IsNoetherian A'₁]
    (hsq : j₁ ≫ π' = π ≫ j)
    (hker : Scheme.Hom.ker j₁ = Blowup.strictTransform π' (Z.map j) (Scheme.Hom.ker j)) :
    (Blowup.strictTransform π Z D).map j₁ = Blowup.strictTransform π' (Z.map j) (D.map j) := by
  have hZ : Z.map j = Scheme.Hom.ker (Z.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j Z
  have hD : D.map j = Scheme.Hom.ker (D.subschemeι ≫ j) := map_eq_ker_subschemeι_comp j D
  have hT : (Blowup.strictTransform π Z D).map j₁
      = Scheme.Hom.ker ((Blowup.strictTransform π Z D).subschemeι ≫ j₁) :=
    map_eq_ker_subschemeι_comp j₁ (Blowup.strictTransform π Z D)
  rw [hT, hD, hZ]
  exact image_strictTransform_eq_strictTransform_image j Z D π π' j₁ hsq (by rw [hker, hZ])

end FunctorialResolution.EmbeddedResolution
end
end

