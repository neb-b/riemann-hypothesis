module

public import Mathlib
public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_fst_snd_over {S : Scheme.{0}} {T G : Over S} :
    IsPullback (fst T G).left (snd T G).left T.hom G.hom :=
  IsPullback.of_hasPullback T.hom G.hom

theorem UpperTheory.clopProj_finite_etale_of_isClosed :
    ∀ {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → IsFinite (UpperTheory.RepresentationRank.proj V) ∧ Etale (UpperTheory.RepresentationRank.proj V) := by
  intro S T G V hf he hV
  have hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom := UpperTheory.isPullback_fst_snd_over.flip
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  haveI : IsFinite (fst T G).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hf
  haveI : Etale (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Etale) hpb he
  exact ⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)),
    inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopRepUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private theorem UpperTheory.preimage_whiskerRight_comp_over {S : Scheme.{0}} {A B C G : Over S} (f : A ⟶ B) (g : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((f ≫ g) ▷ G).left ⁻¹ᵁ W = (f ▷ G).left ⁻¹ᵁ ((g ▷ G).left ⁻¹ᵁ W) := by
  simp

theorem UpperTheory.clopRep_unique :
    ∀ {S : Scheme.{0}} (G Y Y' : Over S) (U : (Y ⊗ G).left.Opens) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → UpperTheory.RepresentationRank.Rep G Y' U' → Nonempty (Y ≅ Y') := by
  intro S G Y Y' U U' hU hU'
  obtain ⟨φ, hφ, -⟩ := hU'.2 Y U hU.1
  obtain ⟨ψ, hψ, -⟩ := hU.2 Y' U' hU'.1
  have hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W := by
    intro Z W
    simp
  have e1 : φ ≫ ψ = 𝟙 Y := by
    obtain ⟨y, -, huniq⟩ := hU.2 Y U hU.1
    have a := huniq (φ ≫ ψ) (by
      show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U
      rw [UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])
    have b := huniq (𝟙 Y) (hid U)
    rw [a, b]
  have e2 : ψ ≫ φ = 𝟙 Y' := by
    obtain ⟨y, -, huniq⟩ := hU'.2 Y' U' hU'.1
    have a := huniq (ψ ≫ φ) (by
      show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'
      rw [UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])
    have b := huniq (𝟙 Y') (hid U')
    rw [a, b]
  exact ⟨⟨φ, ψ, e1, e2⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepOfDisjointOpenCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopSum

variable {S : Scheme.{0}}

private theorem isPullback_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    IsPullback (T ◁ i).left (snd T A).left (snd T B).left i.left := by
  have eq1 : (T ◁ i).left ≫ (fst T B).left = (fst T A).left := Over.whiskerLeft_left_fst i
  have eq2 : i.left ≫ B.hom = A.hom := Over.w i
  have s : IsPullback ((T ◁ i).left ≫ (fst T B).left) (snd T A).left T.hom (i.left ≫ B.hom) := by
    rw [eq1, eq2]
    exact IsPullback.of_hasPullback T.hom A.hom
  exact IsPullback.of_right s (Over.whiskerLeft_left_snd i) (IsPullback.of_hasPullback T.hom B.hom)

private theorem range_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    Set.range (T ◁ i).left = (snd T B).left ⁻¹' Set.range i.left := by
  have h := isPullback_wl T i
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨h.isoPullback.hom a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨h.isoPullback.inv b, ?_⟩
    show (h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst _ _) b = _
    rw [Iso.inv_hom_id_assoc]

private theorem opens_ext {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    (hr : Set.range j₁ = (Set.range j₂)ᶜ) {V V' : C.Opens}
    (h₁ : j₁ ⁻¹ᵁ V = j₁ ⁻¹ᵁ V') (h₂ : j₂ ⁻¹ᵁ V = j₂ ⁻¹ᵁ V') : V = V' := by
  ext x
  by_cases hx : x ∈ Set.range j₁
  · obtain ⟨a, rfl⟩ := hx
    have := SetLike.ext_iff.mp h₁ a
    simpa using this
  · have hx2 : x ∈ Set.range j₂ := by
      rw [hr] at hx
      simpa using hx
    obtain ⟨b, rfl⟩ := hx2
    have := SetLike.ext_iff.mp h₂ b
    simpa using this

private theorem glue {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (hr : Set.range j₁ = (Set.range j₂)ᶜ)
    (V₁ : A₁.Opens) (V₂ : A₂.Opens) (h₁ : IsClosed (V₁ : Set A₁)) (h₂ : IsClosed (V₂ : Set A₂)) :
    ∃ V : C.Opens, IsClosed (V : Set C) ∧ j₁ ⁻¹ᵁ V = V₁ ∧ j₂ ⁻¹ᵁ V = V₂ := by
  have hc1 : IsClosed (Set.range j₁) := by
    rw [hr]
    exact j₂.isOpenEmbedding.isOpen_range.isClosed_compl
  have hc2 : IsClosed (Set.range j₂) := by
    have e : Set.range j₂ = (Set.range j₁)ᶜ := by rw [hr, compl_compl]
    rw [e]
    exact j₁.isOpenEmbedding.isOpen_range.isClosed_compl
  have e1 : Topology.IsClosedEmbedding j₁ := ⟨j₁.isOpenEmbedding.isEmbedding, hc1⟩
  have e2 : Topology.IsClosedEmbedding j₂ := ⟨j₂.isOpenEmbedding.isEmbedding, hc2⟩
  have hopen : IsOpen (j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂)) :=
    (j₁.isOpenEmbedding.isOpenMap _ V₁.isOpen).union (j₂.isOpenEmbedding.isOpenMap _ V₂.isOpen)
  refine ⟨⟨_, hopen⟩, (e1.isClosedMap _ h₁).union (e2.isClosedMap _ h₂), ?_, ?_⟩
  · ext a
    show j₁ a ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ a ∈ V₁
    constructor
    · rintro (⟨a', ha', he⟩ | ⟨b, hb, he⟩)
      · rw [← j₁.isOpenEmbedding.injective he]
        exact ha'
      · exfalso
        have hm : j₁ a ∈ Set.range j₁ := ⟨a, rfl⟩
        rw [hr] at hm
        exact hm ⟨b, he⟩
    · intro ha
      exact Or.inl ⟨a, ha, rfl⟩
  · ext b
    show j₂ b ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ b ∈ V₂
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨b', hb', he⟩)
      · exfalso
        have hm : j₂ b ∈ Set.range j₁ := ⟨a, he⟩
        rw [hr] at hm
        exact hm ⟨b, rfl⟩
      · rw [← j₂.isOpenEmbedding.injective he]
        exact hb'
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩

end UpperTheory.ClopSum

private theorem UpperTheory.preimage_comp_scheme_opens {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.preimage_whisker_left_right_comm {S : Scheme.{0}} {T Y G' G : Over S} (y : T ⟶ Y) (i : G' ⟶ G)
    (W : (Y ⊗ G).left.Opens) :
    (T ◁ i).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ W) = (y ▷ G').left ⁻¹ᵁ ((Y ◁ i).left ⁻¹ᵁ W) := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, ← Over.comp_left,
    whisker_exchange]

private theorem UpperTheory.preimage_whiskerRight_whiskerRight_comp {S : Scheme.{0}} {T Y Z G : Over S} (y : T ⟶ Y) (f : Y ⟶ Z)
    (W : (Z ⊗ G).left.Opens) :
    (y ▷ G).left ⁻¹ᵁ ((f ▷ G).left ⁻¹ᵁ W) = ((y ≫ f) ▷ G).left ⁻¹ᵁ W := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, comp_whiskerRight]

open UpperTheory.ClopSum in
theorem UpperTheory.exists_clopRep_of_disjoint_open_cover :
    ∀ {S : Scheme.{0}} (G G₁ G₂ Y₁ Y₂ : Over S) (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (U₁ : (Y₁ ⊗ G₁).left.Opens) (U₂ : (Y₂ ⊗ G₂).left.Opens), IsOpenImmersion i₁.left → IsOpenImmersion i₂.left → Set.range i₁.left = (Set.range i₂.left)ᶜ → UpperTheory.RepresentationRank.Rep G₁ Y₁ U₁ → UpperTheory.RepresentationRank.Rep G₂ Y₂ U₂ → ∃ U : ((Y₁ ⊗ Y₂) ⊗ G).left.Opens, UpperTheory.RepresentationRank.Rep G (Y₁ ⊗ Y₂) U := by
  intro S G G₁ G₂ Y₁ Y₂ i₁ i₂ U₁ U₂ ho₁ ho₂ hr hU₁ hU₂
  have o1 : ∀ T : Over S, IsOpenImmersion (T ◁ i₁).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₁).flip ho₁
  have o2 : ∀ T : Over S, IsOpenImmersion (T ◁ i₂).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₂).flip ho₂
  have rr : ∀ T : Over S, Set.range (T ◁ i₁).left = (Set.range (T ◁ i₂).left)ᶜ := by
    intro T
    rw [UpperTheory.ClopSum.range_wl, UpperTheory.ClopSum.range_wl, hr]
    rfl
  haveI := o1 (Y₁ ⊗ Y₂)
  haveI := o2 (Y₁ ⊗ Y₂)
  obtain ⟨U, hUc, hU1, hU2⟩ := UpperTheory.ClopSum.glue ((Y₁ ⊗ Y₂) ◁ i₁).left ((Y₁ ⊗ Y₂) ◁ i₂).left
    (rr _) ((fst Y₁ Y₂ ▷ G₁).left ⁻¹ᵁ U₁) ((snd Y₁ Y₂ ▷ G₂).left ⁻¹ᵁ U₂)
    (hU₁.1.preimage (Scheme.Hom.continuous _)) (hU₂.1.preimage (Scheme.Hom.continuous _))
  refine ⟨U, hUc, ?_⟩
  intro T V hV
  have c1 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₁).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU1, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  have c2 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₂).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU2, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  obtain ⟨y₁, hy₁, hu₁⟩ := hU₁.2 T ((T ◁ i₁).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  obtain ⟨y₂, hy₂, hu₂⟩ := hU₂.2 T ((T ◁ i₂).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  refine ⟨lift y₁ y₂, ?_, ?_⟩
  · show ((lift y₁ y₂) ▷ G).left ⁻¹ᵁ U = V
    apply UpperTheory.ClopSum.opens_ext (T ◁ i₁).left (T ◁ i₂).left (rr T)
    · rw [c1, lift_fst]
      exact hy₁
    · rw [c2, lift_snd]
      exact hy₂
  · intro y hy
    have hy' : (y ▷ G).left ⁻¹ᵁ U = V := hy
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact hu₁ _ (by
        show ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ = _
        rw [← c1, hy'])
    · rw [lift_snd]
      exact hu₂ _ (by
        show ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ = _
        rw [← c2, hy'])
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopPullback

variable {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S)

private noncomputable def fwd (T' : Over S') :
    (T' ⊗ (Over.pullback t).obj G).left ⟶ ((Over.map t).obj T' ⊗ G).left :=
  pullback.lift (pullback.fst T'.hom (pullback.snd G.hom t))
    (pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t) (by
      have h := pullback.condition (f := T'.hom) (g := pullback.snd G.hom t)
      have h2 := pullback.condition (f := G.hom) (g := t)
      simp only [Over.map_obj_hom, Category.assoc, h2]
      rw [reassoc_of% h])

private noncomputable def bwd (T' : Over S') :
    ((Over.map t).obj T' ⊗ G).left ⟶ (T' ⊗ (Over.pullback t).obj G).left :=
  pullback.lift (pullback.fst (T'.hom ≫ t) G.hom)
    (pullback.lift (pullback.snd (T'.hom ≫ t) G.hom) (pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom)
      (by simpa using (pullback.condition (f := T'.hom ≫ t) (g := G.hom)).symm))
    (pullback.lift_snd _ _ _).symm

private theorem fwd_fst (T' : Over S') :
    fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = pullback.fst T'.hom (pullback.snd G.hom t) :=
  pullback.lift_fst _ _ _

private theorem fwd_snd (T' : Over S') :
    fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t :=
  pullback.lift_snd _ _ _

private theorem bwd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = pullback.fst (T'.hom ≫ t) G.hom :=
  pullback.lift_fst _ _ _

private theorem bwd_snd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t =
      pullback.snd (T'.hom ≫ t) G.hom := by
  unfold bwd
  erw [pullback.lift_snd_assoc, pullback.lift_fst]

private theorem fwd_bwd (T' : Over S') : fwd t G T' ≫ bwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)
    rw [bwd_fst, fwd_fst, Category.id_comp]
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]
      exact (Category.id_comp _).symm
    · have hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t =
          pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom := by
        unfold bwd
        erw [pullback.lift_snd_assoc, pullback.lift_snd]
      rw [Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]
      exact (Category.id_comp _).symm

private theorem bwd_fwd (T' : Over S') : bwd t G T' ≫ fwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom
    rw [fwd_fst, bwd_fst, Category.id_comp]
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom
    rw [fwd_snd, bwd_snd_fst, Category.id_comp]

private noncomputable def cmp :
    ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left ⟶ (Y ⊗ G).left :=
  pullback.map _ _ _ _ (pullback.fst Y.hom t) (pullback.fst G.hom t) t
    (by simp [pullback.condition]) (by simp [pullback.condition])

private theorem key {T' : Over S'} (y' : T' ⟶ (Over.pullback t).obj Y) :
    (y' ▷ (Over.pullback t).obj G).left ≫ cmp t G Y =
      fwd t G T' ≫ (((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left := by
  set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx
  have a1 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.fst T'.hom ((Over.pullback t).obj G).hom ≫ y'.left :=
    Over.whiskerRight_left_fst _
  have a2 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.snd T'.hom ((Over.pullback t).obj G).hom :=
    Over.whiskerRight_left_snd _
  have b1 : (x ▷ G).left ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.map t).obj T').hom G.hom ≫ x.left :=
    Over.whiskerRight_left_fst _
  have b2 : (x ▷ G).left ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.map t).obj T').hom G.hom :=
    Over.whiskerRight_left_snd _
  have c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst Y.hom t :=
    pullback.lift_fst _ _ _
  have c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst G.hom t :=
    pullback.lift_snd _ _ _
  have hxl : x.left = y'.left ≫ pullback.fst Y.hom t := by
    simp [hx, Over.mapPullbackAdj]
  apply pullback.hom_ext
  · rw [Category.assoc, c1, ← Category.assoc, a1, Category.assoc, Category.assoc, b1,
      ← Category.assoc, hxl]
    exact congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm
  · rw [Category.assoc, c2, ← Category.assoc, a2, Category.assoc, b2]
    exact (fwd_snd t G T').symm

end UpperTheory.ClopPullback

open UpperTheory.ClopPullback

private theorem UpperTheory.preimage_comp_scheme_opens_of_pullback {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.isClosed_preimage_opens_of_isClosed {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Opens}
    (hW : IsClosed (W : Set Y)) : IsClosed ((f ⁻¹ᵁ W : X.Opens) : Set X) :=
  hW.preimage f.continuous

private theorem UpperTheory.preimage_preimage_eq_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (W : X.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ W) = W := by
  rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]
  simp

theorem UpperTheory.exists_clopRep_pullback :
    ∀ {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → ∃ U' : ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left.Opens, UpperTheory.RepresentationRank.Rep ((Over.pullback t).obj G) ((Over.pullback t).obj Y) U' := by
  intro S S' t G Y U hU
  refine ⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩
  intro T' V' hV'
  obtain ⟨y, hy, huniq⟩ := hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V')
    (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')
  have hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y,
      (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) =
        fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U) := by
    intro y'
    rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]
  refine ⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩
  · show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ
        (cmp t G Y ⁻¹ᵁ U) = V'
    rw [hpre, Equiv.symm_apply_apply, hy]
    exact UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'
  · intro y'' hy''
    have hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V' := hy''
    have h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) =
        bwd t G T' ⁻¹ᵁ V' := by
      rw [← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]
    have h2 := huniq _ h1
    rw [← h2, Equiv.apply_symm_apply]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClosedLocusOfTorsionAbelianScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem UpperTheory.exists_closed_locus_of_torsion_abelianScheme :
    ∀ {S T : Scheme.{0}} (x : T ⟶ S) (A G : Over S) [GrpObj A] (inc : G ⟶ A) (k : ℕ), (∀ (T' : Over S) (a : T' ⟶ G), (a ≫ inc) ^ k = 1) → IsUnit (k : Γ(T, ⊤)) → ∀ (A₁ : Over T) [GrpObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → ∃ V : (Over.mk x ⊗ G).left.Opens, IsClosed (V : Set (Over.mk x ⊗ G).left) ∧ ∀ (T' : Over S) (t : T' ⟶ Over.mk x) (a : T' ⟶ G) (g : Over.mk t.left ⟶ A₁), g.left ≫ φ₁ = a.left ≫ inc.left → (g ≫ f = 1 ↔ Set.range (lift t a).left ⊆ V) := by
  intro S T x A G _ inc k hk hu A₁ _ φ₁ B₁ _ f hP hB hf
  have hfe := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion B₁ (hG := hB) hu
  obtain ⟨hfin, het⟩ := hfe.2
  let pr : (Over.mk x ⊗ G).left ⟶ T := (fst (Over.mk x) G).left
  have hpr : pr ≫ x = (Over.mk x ⊗ G).hom := Over.w (fst (Over.mk x) G)
  obtain ⟨τ, hτ, -⟩ := UpperTheory.SubRep.pull_existsUnique hP (Over.mk x ⊗ G) pr hpr (snd (Over.mk x) G ≫ inc)
  have hτk : τ ^ k = 1 := by
    apply UpperTheory.SubRep.pull_ext hP
    rw [UpperTheory.SubRep.pull_pow hP _ pr hpr hτ k, hk _ (snd (Over.mk x) G), UpperTheory.SubRep.pull_one hP _ pr hpr]
  have hpow : ∀ n : ℕ, (τ ≫ f) ^ n = (τ ^ n) ≫ f := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]
  have hwk : (τ ≫ f) ^ k = 1 := by
    rw [hpow, hτk, MonObj.one_comp]
  obtain ⟨c, hc, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (τ ≫ f) hwk
  obtain ⟨c₀, hc₀, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk pr ⟶ B₁) (one_pow k)
  obtain ⟨V, hV, H⟩ := GlobalTheory.LevCover.clopenCond_eq c c₀
  refine ⟨V, hV, fun T' t a g hg => ?_⟩
  have hl : (lift t a).left ≫ pr = t.left := by
    change ((lift t a) ≫ fst (Over.mk x) G).left = t.left
    rw [lift_fst]
  let h : Over.mk t.left ⟶ Over.mk pr := Over.homMk (lift t a).left hl
  have hhτ : h ≫ τ = g := by
    apply UpperTheory.SubRep.pull_ext hP
    have e : (lift t a).left ≫ (snd (Over.mk x) G ≫ inc).left = a.left ≫ inc.left := by
      change (lift t a ≫ snd (Over.mk x) G ≫ inc).left = _
      rw [lift_snd_assoc]; rfl
    change (lift t a).left ≫ τ.left ≫ φ₁ = _
    rw [hτ, e, hg]
  have hgf : g ≫ f = h ≫ τ ≫ f := by rw [← hhτ, Category.assoc]
  have key : g ≫ f = 1 ↔ h ≫ c = h ≫ c₀ := by
    constructor
    · intro e
      have h1 : (h ≫ c) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc, ← hgf, e]
      have h2 : (h ≫ c₀) ≫ torsion.ι B₁ k = 1 := by
        rw [Category.assoc, hc₀, MonObj.comp_one]
      exact (GlobalTheory.LatticeTorsion.existsUnique_torsion B₁ k (1 : Over.mk t.left ⟶ B₁) (one_pow k)).unique h1 h2
    · intro e
      rw [hgf, ← hc, ← Category.assoc, e, Category.assoc, hc₀, MonObj.comp_one]
  exact key.trans (H _ h)
end

