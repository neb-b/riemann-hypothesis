module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianQuotient

variable {S : Scheme.{0}}

lemma exists_desc {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  have : MorphismProperty.IsStableUnderComposition @Surjective.{0} :=
    ⟨fun _ _ _ _ => inferInstance⟩
  exact MorphismProperty.pullbackMap (P := @Surjective) hf hg (Over.w f).symm (Over.w g).symm

lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

theorem exists_grpObj {A H Q : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H] (i : H ⟶ A)
    [IsMonHom i] (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q ∧ IsPullback i (toUnit H) q η[Q] := by
  have rel : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q ↔ ∃ t : W ⟶ H, a = (t ≫ i) * b := by
    intro W a b
    constructor
    · intro h
      refine ⟨hq.lift a b h ≫ fst H A, ?_⟩
      have h1 := hq.lift_fst a b h
      rw [comp_mul, hq.lift_snd] at h1
      rw [Category.assoc, h1]
    · rintro ⟨t, rfl⟩
      have := lift t b ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel (a ≫ fst A A) (b ≫ fst A A)).1 (by simpa using h =≫ fst Q Q)
    obtain ⟨t, ht⟩ := (rel (a ≫ snd A A) (b ≫ snd A A)).1 (by simpa using h =≫ snd Q Q)
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s * t, ?_⟩
    rw [MonObj.mul_eq_mul, comp_mul, comp_mul, hs, ht, mul_comp, _root_.mul_mul_mul_comm])
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel a b).1 h
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s⁻¹, ?_⟩
    rw [← Hom.inv_def, ← Hom.inv_def, hs, GrpObj.inv_comp, mul_inv])
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom, ?_⟩
  · rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
      IsCommMonObj.mul_comm_assoc]
  · have hk : IsPullback (lift (𝟙 H) (toUnit H ≫ η[A])) (toUnit H) (snd H A) η[A] := by
      refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst H A) ?_ ?_ ?_⟩⟩
      · intro s
        ext
        · simp
        · simp [s.condition, toUnit_unique (toUnit _) s.snd]
      · intro s
        exact toUnit_unique _ _
      · intro s l h1 _
        simp [← h1]
    have := hk.flip.paste_vert hq.flip
    have e : lift (𝟙 H) (toUnit H ≫ η[A]) ≫ ((fst H A ≫ i) * snd H A) = i := by
      simp [comp_mul, ← Hom.one_def]
    rw [e] at this
    exact this.flip

lemma isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (p : X ⟶ Y) [Flat p] [Surjective p]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := p.surjective y
    exact isReduced_of_injective (p.stalkMap x).hom
      (faithfullyFlat_stalkMap_of_flat p x).injective
  exact isReduced_of_isReduced_stalk Y

lemma geometricallyReduced_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Flat p]
    [Surjective p] [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact isReduced_of_flat_of_surjective (pullback.snd p a)

lemma geometricallyConnected_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [h : GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : ConnectedSpace ↥(pullback p a) :=
    h.geometrically_connectedSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact (pullback.snd p a).surjective.connectedSpace (pullback.snd p a).continuous

lemma smooth_of_grpObj_of_flat (Q : Over S) [GrpObj Q] [Flat Q.hom]
    [LocallyOfFinitePresentation Q.hom] [GeometricallyReduced Q.hom] : Smooth Q.hom := by
  refine Smooth.of_smooth_fiberToSpecResidueField _ fun y => ?_
  letI : GrpObj (Over.mk Q.hom) := inferInstanceAs (GrpObj Q)
  letI : GrpObj (Over.mk (pullback.snd Q.hom (S.fromSpecResidueField y))) :=
    Over.grpObjMkPullbackSnd
  exact smooth_of_grpObj (K := S.residueField y) (pullback.snd Q.hom (S.fromSpecResidueField y))

end AbelianQuotient


open AbelianQuotient in
theorem quotient_isAbelianScheme_of_quotientScheme :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
      (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i →
      IsFinite H.hom → Flat H.hom →
      ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧
        Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
        IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q) →
    QuotientSt := by
  intro hint hquot R _ _ P H _ i hi hmono hfin hflat
  obtain ⟨Q, q, h1, h2, h3, h4, h5, hq⟩ := hquot R P H i hi hmono hfin hflat
  have := P.isAb.comm
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h1, h2, h3, hker⟩
  have hw : q.left ≫ Q.hom = P.A.hom := Over.w q
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := hint _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_comp_section_of_local_rigidity {X T Y S : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X)
    (g : X ⟶ Y) (π : T ⟶ S) (q : Y ⟶ S) [IsSeparated q] (he : ε ≫ p = 𝟙 T)
    (hg : g ≫ q = p ≫ π) (hp : IsOpenMap p)
    (hloc : ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) →
      ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g)
    (hconn : ∀ s : S, _root_.IsPreconnected (π ⁻¹' {s}))
    (hmeet : ∀ s : S, ∃ (t : T) (y : Y), π t = s ∧ ∀ x : X, p x = t → g x = y) :
    g = p ≫ ε ≫ g := by
  have hab : g ≫ q = (p ≫ ε ≫ g) ≫ q := by
    simp only [Category.assoc, hg, reassoc_of% he]
  have hcl := isClosedImmersion_equalizer_ι_of_isSeparated q hab
  let Z : Set X := Set.range (equalizer.ι g (p ≫ ε ≫ g))
  have hZ : IsClosed Z := (equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range
  let T₀ : Set T := (p '' Zᶜ)ᶜ
  have hT₀c : IsClosed T₀ := (hp _ hZ.isOpen_compl).isClosed_compl
  have hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t) := by
    intro t ht x hx
    have hxZ : x ∈ Z := by
      by_contra h
      exact ht ⟨x, h, hx⟩
    obtain ⟨z, rfl⟩ := hxZ
    rw [← hx, ← Scheme.Hom.comp_apply, equalizer.condition]
    simp only [Scheme.Hom.comp_apply]
  have hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀ := by
    rintro V hV t ht ⟨x, hx, rfl⟩
    exact hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)
  have hT₀o : IsOpen T₀ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t _ (hfib t ht)
    exact ⟨V, hsub V hV, V.2, htV⟩
  have hall : ∀ t : T, t ∈ T₀ := by
    intro t
    obtain ⟨t', y, ht', hy⟩ := hmeet (π t)
    obtain ⟨V, htV, hV⟩ := hloc t' y hy
    exact (hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, htV, hV⟩ := hloc (p x) _ (hfib _ (hall _))
  exact ⟨p ⁻¹ᵁ V, htV, hV⟩

theorem surjective_app_of_isAbelianScheme (hG : GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (V : S.Opens) :
    Function.Surjective (A.hom.app V).hom := by
  have h1 : Function.Surjective (pullback.snd A.hom V.ι).appTop.hom :=
    (hG _ _ (TLinPf.isAb_pullback V.ι A hA)).2
  have h2 : Function.Surjective (A.hom ∣_ V).appTop.hom := by
    have e : A.hom ∣_ V = (pullbackRestrictIsoRestrict A.hom V).inv ≫ pullback.snd A.hom V.ι := rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      ((pullbackRestrictIsoRestrict A.hom V).inv.app ⊤)).2.comp h1
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Surjective (A.hom.app (V.ι ''ᵁ ⊤)).hom := by
    have hb : Function.Bijective (A.left.presheaf.map
        (eqToHom (image_morphismRestrict_preimage A.hom V ⊤)).op).hom := by
      rw [eqToHom_op]
      exact ConcreteCategory.bijective_of_isIso (A.left.presheaf.map (eqToHom _))
    exact (Function.Surjective.of_comp_iff' hb _).1 h2
  rwa [V.ι_image_top] at h3

theorem rigidity_of_local_rigidity : GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → RigiditySt := by
  intro hG hR S A B _ _ hA hB f hf
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := hB.proper
  let g : A ⊗ A ⟶ B := (fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)
  let ε : A ⟶ A ⊗ A := lift 1 (𝟙 A)
  let j : A ⟶ A ⊗ A := lift (𝟙 A) 1
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf, Hom.one_def]
  have hε : ε ≫ g = f := by
    simp only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      inv_one, _root_.one_mul, Category.id_comp]
  have hj : j ≫ g = 1 := by
    simp only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
      _root_.mul_one, inv_mul_cancel]
  have hεp : ε.left ≫ (snd A A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd A A).left := by
    change Smooth (pullback.snd A.hom A.hom); infer_instance
  have huc : UniversallyClosed (snd A A).left := by
    change UniversallyClosed (pullback.snd A.hom A.hom); infer_instance
  have hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left := by
    have hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom := .of_hasPullback A.hom A.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst A A).left = 𝟙 A.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hη]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]
      rfl
  have key : g.left = (snd A A).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp
      ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap
      (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_
    intro s
    refine ⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hη]; rfl
    · intro x hx
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left,
        Scheme.Hom.comp_apply]
      rfl
  have key' : g = snd A A ≫ f := by
    rw [← hε]
    exact Over.OverMorphism.ext key
  have hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f) := by
    rw [← key', mul_inv_cancel_left]
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  rw [hmul]
  congr 1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra! hz
    have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hz
    exact top_ne_bot (hs.symm.trans hbot)
  have hPt := hP t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hPt
  have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  have : Algebra.IsStandardSmooth K (Localization.Away t) := hPt.isStandardSmooth
  have hdim : ringKrullDim (Localization.Away t) = g :=
    AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := K)
  obtain ⟨d, hd1, hd2⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (Localization.Away t)
  have hdg : d = g := by
    rw [hdim] at hd1
    exact_mod_cast hd1.symm
  have : FaithfulSMul B (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic B (Localization.Away t) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers t)
  have : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K B).injective
  rw [← trdeg_eq_of_isAlgebraic_top K B (Localization.Away t), hd2, hdg]

theorem trdeg_eq_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g := by
  intro K _ X _ f g hf B _ _ _ j hj hjf
  have : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  have : IsDomain B := (affine_isIntegral_iff (CommRingCat.of B)).mp this
  have h0 : SmoothOfRelativeDimension (0 + g) (j ≫ f) := inferInstance
  rw [Nat.zero_add, hjf] at h0
  have hloc := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h0
  exact trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension hloc

end GlobalTheory
end

