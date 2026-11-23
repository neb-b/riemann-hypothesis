module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyPulledBackNearPointOfEtaleCoordinates
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtalePull

theorem range_pt {Ω : Type} [Field Ω] {X : Scheme.{0}} (p : Sp Ω ⟶ X) (t : Sp Ω) : Set.range p = {p t} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    have : s = t := Subsingleton.elim (α := PrimeSpectrum Ω) s t
    simp [this]
  · rintro rfl
    exact ⟨t, rfl⟩

theorem range_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) : Set.range (f ≫ g) = g '' Set.range f := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext fun t => Scheme.Hom.comp_apply f g t)

theorem exists_isIso_restrict {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [Etale f] [UniversallyClosed f]
    [UniversallyClosed q] (x : U)
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  have hΔ : IsOpenImmersion (pullback.diagonal f) := inferInstance
  let r : pullback f f ⟶ U := pullback.fst f f ≫ f ≫ q
  have h1 : IsClosed (r '' (Set.range (pullback.diagonal f))ᶜ) :=
    r.isClosedMap _ (pullback.diagonal f).isOpenEmbedding.isOpen_range.isClosed_compl
  have h2 : IsClosed (q '' (Set.range f)ᶜ) :=
    q.isClosedMap _ f.isOpenMap.isOpen_range.isClosed_compl
  let W : U.Opens := ⟨(r '' (Set.range (pullback.diagonal f))ᶜ)ᶜ ∩ (q '' (Set.range f)ᶜ)ᶜ,
    h1.isOpen_compl.inter h2.isOpen_compl⟩
  refine ⟨W, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨z, hz, hzx⟩
    apply hz
    let w := (pullback f f).fromSpecResidueField z
    have hw : w ≫ pullback.fst f f = w ≫ pullback.snd f f := by
      refine hinj ((pullback f f).residueField z) _ _ ?_ ?_
      · have : Set.range (w ≫ r) = {x} := by
          rw [range_comp', Scheme.range_fromSpecResidueField, Set.image_singleton, hzx]
        have e : (w ≫ pullback.fst f f) ≫ f ≫ q = w ≫ r := Category.assoc _ _ _
        exact (congrArg (fun k : Spec ((pullback f f).residueField z) ⟶ U => Set.range k) e).trans this
      · simp [pullback.condition]
    have hw2 : w = (w ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp
      · simp [hw]
    have : z ∈ Set.range w := by rw [Scheme.range_fromSpecResidueField]; rfl
    obtain ⟨t, ht⟩ := this
    refine ⟨(w ≫ pullback.fst f f) t, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hw2, ht]
  · rintro ⟨y, hy, hyx⟩
    exact hy (hsurj y hyx)
  · have hm : Mono (f ∣_ (q ⁻¹ᵁ W)) := by
      refine ⟨fun {T} u v huv => ?_⟩
      have e : (u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f = (v ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι) ≫ f := by
        simp only [Category.assoc, ← morphismRestrict_ι]
        rw [← Category.assoc, huv, Category.assoc]
      let w : T ⟶ pullback f f := pullback.lift _ _ e
      have hr : Set.range w ⊆ Set.range (pullback.diagonal f) := by
        rintro _ ⟨t, rfl⟩
        by_contra hn
        have hW : q (f ((f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι (u t))) ∈ W := (u t).2
        refine hW.1 ⟨w t, hn, ?_⟩
        have e3 : w ≫ r = u ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι ≫ f ≫ q := by
          simp only [w, r, pullback.lift_fst_assoc, Category.assoc]
        rw [← Scheme.Hom.comp_apply, e3]
        simp only [Scheme.Hom.comp_apply]
      have hl := IsOpenImmersion.lift_fac (pullback.diagonal f) w hr
      have e1 := congrArg (· ≫ pullback.fst f f) hl
      have e2 := congrArg (· ≫ pullback.snd f f) hl
      simp only [w, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        pullback.lift_fst, pullback.lift_snd] at e1 e2
      rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ W)).ι, ← e1, e2]
    have ho : IsOpenImmersion (f ∣_ (q ⁻¹ᵁ W)) := IsOpenImmersion.of_flat_of_mono _
    refine (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨ho, ⟨fun y => ?_⟩⟩
    have hW : q y.1 ∈ W := y.2
    have : y.1 ∈ Set.range f := by
      by_contra hn
      exact hW.2 ⟨y.1, hn, rfl⟩
    obtain ⟨s, hs⟩ := this
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ W
      rw [hs]; exact hW
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs

theorem exists_isIso_restrict' {X Y U : Scheme.{0}} (f : X ⟶ Y) (q : Y ⟶ U) [UniversallyClosed f]
    [UniversallyClosed q] (x : U) (V : U.Opens) (hx : x ∈ V) [Etale (f ∣_ (q ⁻¹ᵁ V))]
    (hinj : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ f ≫ q) = {x} → p ≫ f = p' ≫ f → p = p')
    (hsurj : ∀ y : Y, q y = x → y ∈ Set.range f) :
    ∃ W : U.Opens, x ∈ W ∧ W ≤ V ∧ IsIso (f ∣_ (q ⁻¹ᵁ W)) := by
  obtain ⟨W, hW, hiso⟩ := exists_isIso_restrict (f ∣_ (q ⁻¹ᵁ V)) (q ∣_ V) ⟨x, hx⟩ (by
    intro Ω _ p p' h1 h2
    rw [← cancel_mono (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι]
    apply hinj
    · have e : (p ≫ (f ⁻¹ᵁ (q ⁻¹ᵁ V)).ι) ≫ f ≫ q = (p ≫ f ∣_ (q ⁻¹ᵁ V) ≫ q ∣_ V) ≫ V.ι := by
        simp
      rw [e, range_comp', h1]
      exact Set.image_singleton
    · simp only [Category.assoc, ← morphismRestrict_ι]
      rw [← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    have h1 : q y.1 = x := (morphismRestrict_base_coe q V y).symm.trans (congrArg Subtype.val hy)
    obtain ⟨s, hs⟩ := hsurj y.1 h1
    refine ⟨⟨s, ?_⟩, ?_⟩
    · show q (f s) ∈ V
      rw [hs, h1]; exact hx
    · apply Subtype.ext
      exact (morphismRestrict_base_coe _ _ _).trans hs)
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hW, rfl⟩, V.ι_image_le W, ?_⟩
  rw [← image_morphismRestrict_preimage]
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f (q ⁻¹ᵁ V) ((q ∣_ V) ⁻¹ᵁ W))).1 hiso

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ V : U.left.Opens, x ∈ V → Etale (V.ι ≫ τ) → ∃ V : U.left.Opens, x ∈ V ∧ Etale (V.ι ≫ τ) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ b) (V.ι ≫ U.hom) π := by
  intro R _ _ _ _ S X π U a b g τ c hπ _ _ _ hU ha _ hτ hc1 hc2 hc x _ _ hinj hsurj V hxV hV
  have hcomm : a ≫ U.hom = b ≫ π := by
    rw [← hτ, ← Category.assoc, ← hc1, ← hc2, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨f, hf1, hf2⟩ : ∃ f : X ⟶ pullback U.hom π, f ≫ pullback.fst _ _ = a ∧ f ≫ pullback.snd _ _ = b :=
    ⟨pullback.lift a b hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  subst hf1
  have hfp : IsProper f := IsProper.of_comp f (pullback.fst U.hom π)
  let G : pullback U.hom π ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π :=
    pullback.lift (pullback.fst _ _ ≫ τ) (pullback.snd _ _) (by rw [Category.assoc, hτ, pullback.condition])
  have hG1 : G ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ := pullback.lift_fst _ _ _
  have hG2 : G ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hG : IsPullback G (pullback.fst U.hom π) (pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π) τ := by
    refine IsPullback.of_right ?_ hG1 (IsPullback.of_hasPullback _ π).flip
    rw [hG2, hτ]
    exact (IsPullback.of_hasPullback _ π).flip
  have hfG : f ≫ G = c := by
    apply pullback.hom_ext
    · rw [Category.assoc, hG1, hc1, Category.assoc]
    · rw [Category.assoc, hG2, hc2, hf2]
  have hG' := (isPullback_morphismRestrict (pullback.fst U.hom π) V).flip.paste_horiz hG
  have hGe : Etale ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) :=
    MorphismProperty.of_isPullback (P := @Etale) hG'.flip hV
  have hfe : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V)) := by
    have : Etale (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ V) ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G) := by
      rw [morphismRestrict_ι_assoc, hfG]; infer_instance
    exact Etale.of_comp _ ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ G)
  obtain ⟨W, hxW, hWV, hiso⟩ := exists_isIso_restrict' f (pullback.fst U.hom π) x V hxV (by
    intro Ω _ p p' h1 h2
    refine hinj Ω p p' h1 ?_ ?_
    · rw [← Category.assoc, h2, Category.assoc]
    · rw [← hf2, ← Category.assoc, h2, Category.assoc]) (by
    intro y hy
    let K := (pullback U.hom π).residueField y
    let w : Sp (AlgebraicClosure K) ⟶ pullback U.hom π :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ (pullback U.hom π).fromSpecResidueField y
    let t : Sp (AlgebraicClosure K) := closedPoint (AlgebraicClosure K)
    have hw : w t = y := by
      have : w t ∈ Set.range ((pullback U.hom π).fromSpecResidueField y) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    obtain ⟨p, hp1, hp2⟩ := hsurj (AlgebraicClosure K) (w ≫ pullback.fst _ _) (w ≫ pullback.snd _ _)
      (by rw [range_pt _ t, Scheme.Hom.comp_apply, hw, hy]) (by simp [pullback.condition])
    have : p ≫ f = w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hp1]
      · rw [Category.assoc, hf2, hp2]
    exact ⟨p t, by rw [← Scheme.Hom.comp_apply, this, hw]⟩)
  refine ⟨W, hxW, ?_, ?_⟩
  · rw [← U.left.homOfLE_ι hWV, Category.assoc]
    infer_instance
  · have P1 := (isPullback_morphismRestrict (pullback.fst U.hom π) W).paste_vert (IsPullback.of_hasPullback U.hom π)
    have P0 : IsPullback (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ pullback.fst U.hom π ∣_ W)
        (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W) ≫ (pullback.fst U.hom π ⁻¹ᵁ W).ι ≫ pullback.snd U.hom π)
        (W.ι ≫ U.hom) π :=
      P1.of_iso (asIso (f ∣_ (pullback.fst U.hom π ⁻¹ᵁ W))).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp only [Iso.symm_hom, asIso_inv, IsIso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id])
        (by simp) (by simp)
    rw [morphismRestrict_ι_assoc, hf2, ← morphismRestrict_comp] at P0
    exact P0

end GlobalTheory.Mum.EtalePull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreEtaleRestrictOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem fibre_etale_restrict_open : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  intro T X Z T' X' Z' S p q h hh p' q' h' hh' iT iX iZ _ _ _ sZ sh x x' sx W w hw hz hE
  have hp : p' ≫ iT = iX ≫ p := by
    simp only [← hh, ← hh', Category.assoc, ← sZ]
    simp only [← Category.assoc, sh]
  have hs : x' ≫ iT = 𝟙 S ≫ x := by simp [sx]
  let j := pullback.map p' x' p x iX (𝟙 S) iT hp hs
  let jZ := pullback.map q' x' q x iZ (𝟙 S) iT sZ.symm hs
  obtain ⟨a', ha'⟩ := hz
  have hwr : w ∈ Set.range j := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨a', ha'⟩, ⟨pullback.snd p x w, by simp⟩⟩
  obtain ⟨w', rfl⟩ := hwr
  set F := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp) with hF
  set F' := pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp) with hF'
  have hnat : j ≫ F = F' ≫ jZ := by
    apply pullback.hom_ext
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, sh]
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.comp_id]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨j ⁻¹ᵁ W, w', hw, ?_, ?_⟩
  · have e1 : j ≫ pullback.fst p x = pullback.fst p' x' ≫ iX := pullback.lift_fst _ _ _
    have e2 := congrArg (fun f : pullback p' x' ⟶ X => f w') e1
    simp only [Scheme.Hom.comp_apply] at e2
    exact e2.symm
  · have e : ((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ = (j ∣_ W) ≫ (W.ι ≫ F) := by
      rw [Category.assoc, ← hnat, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have : Etale (((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ) := by
      rw [e]; infer_instance
    exact Etale.of_comp _ jZ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtCompIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FinExtComp

theorem finExt_comp_isPullDeg : ∀ (R R₀ R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₀ : R →+* R₀) (ρ₁ : R₀ →+* R₁) (D : DegPre R) (D₀ : DegPre R₀) (D₁ : DegPre R₁), FinExt ρ₀ → FinExt ρ₁ → Nonempty (IsPullDeg ρ₀ D D₀) → Nonempty (IsPullDeg ρ₁ D₀ D₁) → FinExt (ρ₁.comp ρ₀) ∧ Nonempty (IsPullDeg (ρ₁.comp ρ₀) D D₁) := by
  intro R R₀ R₁ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ D D₀ D₁ h₀ h₁ ⟨p⟩ ⟨q⟩
  exact ⟨⟨h₁.1, h₁.2.1.comp h₀.2.1, h₁.2.2.comp h₀.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp h₀.2.1 h₁.2.1 p q⟩

end GlobalTheory.Mum.FinExtComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Mum

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

abbrev baseMap (R : Type) [CommRing R] [IsDomain R] (E : Type) [Field E] [Algebra (FractionRing R) E] : R →+* E :=
  (algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

variable {R : Type} [CommRing R] [IsDomain R] {E : Type} [Field E] [Algebra (FractionRing R) E]

theorem finExt_integralClosure [IsLocalRing R] (hR : Base R) [FiniteDimensional (FractionRing R) E]
    [IsGalois (FractionRing R) E] :
    letI := (baseMap R E).toAlgebra
    ∃ _ : IsLocalRing (integralClosure R E), FinExt (algebraMap R (integralClosure R E)) := by
  letI := (baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨⟨hN, -, hI, hC⟩, -⟩ := hR
  set R₂ := integralClosure R E
  haveI : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) E R₂
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_isAdicComplete R
  haveI : IsLocalRing R₂ := GlobalTheory.TameKummer.isLocalRing_of_finite R R₂
  refine ⟨inferInstance, ⟨IsNoetherianRing.of_finite R R₂, inferInstance,
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, ?_, ?_⟩
  · intro a b h
    have := congrArg (algebraMap R₂ E) h
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) E).injective this)
  · exact RingHom.finite_algebraMap.2 inferInstance

end GlobalTheory.GalClosure

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

end GlobalTheory.GalClosure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem finiteFlat_proper_baseChange_facts : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  intro R R' _ _ _ _ ρ hinj hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  have h1 : IsFinite (spMap ρ) := (IsFinite.SpecMap_iff _).mpr hfin
  have h2 : IsFinite k := MorphismProperty.of_isPullback (P := @IsFinite) hk.flip h1
  have h3 : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) hk' hp
  have h4 : Surjective (spMap ρ) :=
    ⟨RingHom.IsIntegral.comap_surjective hfin.to_isIntegral hinj⟩
  have h5 : Surjective k := MorphismProperty.of_isPullback (P := @Surjective) hk.flip h4
  have h6 : Surjective k' := MorphismProperty.of_isPullback (P := @Surjective) hk'.flip h5
  refine ⟨h2, inferInstance, inferInstance, h6.surj, (p' ≫ k).isClosedMap, p.isClosedMap, ?_, ?_⟩
  · intro V hV
    refine ⟨QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact, ?_⟩
    haveI : IsAffine V := hV
    haveI : QuasiSeparatedSpace (p ⁻¹ᵁ V : Z.Opens).toScheme :=
      quasiSeparatedSpace_of_quasiSeparated (p ∣_ V)
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (p ⁻¹ᵁ V).isOpen).mpr this
  · letI := ρ.toAlgebra
    haveI : Module.Finite R R' := hfin
    haveI : Module.Flat R R' := hflat
    haveI : Module.Free R R' := Module.free_of_flat_of_isLocalRing
    let b := Module.finBasis R R'
    refine ⟨_, b, fun r' => ⟨b.repr r', ?_, ?_⟩⟩
    · exact (b.sum_repr r').symm
    · intro c hc
      have : r' = ∑ l, c l • b l := hc
      rw [this, b.repr_sum_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundary
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem coboundary_locally_of_cocycle : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (V : Y.Opens) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    ∀ y ∈ V, ∃ V' : Y.Opens, V' ≤ V ∧ y ∈ V' ∧ ∃ u : Γ(X, f ⁻¹ᵁ V')ˣ,
      ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  intro X Y f _ _ _ _ V c hc y hy
  obtain ⟨V₀, hV₀, hyV₀, hV₀V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy
  have h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀ := fun z hz => by
    show f (pullback.snd f f z) ∈ V₀
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact hz
  have hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V := fun z hz => hV₀V hz
  letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
  obtain ⟨hN, hF, hFF⟩ := GlobalTheory.T.finite_faithfullyFlat_algebra_over_affine_open f V₀ hV₀
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_tensorSquare_equiv_fibreSquare_sections f V₀ hV₀ h
  have hcoc := GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps f V V₀ hV₀ h hle c hc e he
  let c₀ : (Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀))ˣ := Units.map e.symm.toMonoidHom (res hle c)
  obtain ⟨r, hr, m, s, n, hm, hs⟩ := GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor _ _ c₀ hcoc
    (Ideal.comap (Y.presheaf.germ V₀ y hyV₀).hom (IsLocalRing.maximalIdeal _)) inferInstance
  have hm' : ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom m * (res hle c).val =
      ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom m := by
    have := congrArg e hm
    rw [map_mul, he, he] at this
    simpa [c₀] using this
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.LBDescent.coboundary_unit_basicOpen f V V₀ h hle c r m s n hm' hs
  refine ⟨Y.basicOpen r, (Y.basicOpen_le r).trans hV₀V, ?_, u, hu⟩
  rw [Scheme.mem_basicOpen _ _ _ hyV₀]
  by_contra hh
  exact hr (by simpa [IsLocalRing.mem_maximalIdeal] using hh)

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem finrank_range_relFrob_dual_add_finrank_ker_verschiebung (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (h : (p : k) = 0) (G : PDivGroup p k) : Module.finrank k (LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap) + Module.finrank k (LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap) = Module.finrank k (G.A 1) := by
  let e : G.dual.A 1 ≃ₗ[k] Module.Dual k (G.A 1) := CartierDual.toDual k (G.A 1)
  set W := LinearMap.range ((relFrob h G.dual).app 1 : (frobTwist h G.dual).A 1 →ₐ[k] G.dual.A 1).toLinearMap with hW
  have hker : LinearMap.ker ((verschiebung h G).app 1 : G.A 1 →ₐ[k] (frobTwist h G).A 1).toLinearMap
      = (W.map e.toLinearMap).dualCoannihilator := by
    ext a
    rw [Submodule.mem_dualCoannihilator, LinearMap.mem_ker]
    change (verschiebung h G).app 1 a = 0 ↔ _
    constructor
    · rintro ha _ ⟨_, ⟨x, rfl⟩, rfl⟩
      change e ((relFrob h G.dual).app 1 x) a = 0
      induction x using frobTwist_induction h (G := G.dual) 1 with
      | h0 => simp
      | h2 x y hx hy => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
      | h1 r χ =>
        rw [map_smul, map_smul, LinearMap.smul_apply, relFrob_app_frobProj]
        have := frobTwistDual_verschiebung h 1 χ a
        rw [ha, map_zero] at this
        exact (congrArg (r • ·) this.symm).trans (smul_zero r)
    · intro ha
      refine frobTwist_ext_dual h 1 fun χ => ?_
      rw [frobTwistDual_verschiebung, map_zero]
      refine ha _ ⟨_, ⟨(frobProj h G.dual).app 1 χ, rfl⟩, ?_⟩
      exact congrArg e (relFrob_app_frobProj h (G := G.dual) 1 χ)
  rw [hker, ← e.finrank_map_eq W]
  exact Subspace.finrank_add_finrank_dualCoannihilator_eq _

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMoritaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  first | (exact @GlobalTheory.HTRho.finrank_homO_morita) | (exact GlobalTheory.HTRho.finrank_homO_morita) | (intros; apply GlobalTheory.HTRho.finrank_homO_morita <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedTorsionTransferJointlyMonicHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedTorsion_transfer_jointlyMonic_homs : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | exact GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic | (intros; apply GlobalTheory.TorsionTransfer.fixed_of_jointlyMonic <;> assumption)
end

