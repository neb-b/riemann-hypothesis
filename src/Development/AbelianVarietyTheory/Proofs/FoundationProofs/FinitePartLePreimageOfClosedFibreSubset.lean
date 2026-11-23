module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013

@[expose] public section

noncomputable section

namespace GlobalTheory

open IsLocalRing TensorProduct CategoryTheory Limits AlgebraicGeometry

universe u

theorem exists_idempotent_finite_away_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)] [Algebra.QuasiFiniteAt R q] :
    ∃ e : S, IsIdempotentElem e ∧ e ∉ q ∧ Module.Finite R (Localization.Away e) := by
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hbij, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (maximalIdeal R) q
  let ε : (maximalIdeal R).ResidueField ≃ₐ[R] P.ResidueField := .ofBijective _ hbij
  let ε' : (R ⧸ maximalIdeal R) ≃ₐ[R] (maximalIdeal R).ResidueField :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (Ideal.bijective_algebraMap_quotient_residueField _)
  obtain ⟨σ, hσ⟩ := exists_algHom_lift_of_etale_of_isLocalRing (maximalIdeal R)
    ((ε'.trans ε).symm.toAlgHom.comp (IsScalarTower.toAlgHom R R' P.ResidueField))
  have hσP : ∀ a, σ a ∈ maximalIdeal R ↔ a ∈ P := fun a ↦ by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hσ, ← Ideal.algebraMap_residueField_eq_zero (I := P)]
    simp
  let τ : R' ⊗[R] S →ₐ[R] S :=
    Algebra.TensorProduct.lift ((Algebra.ofId R S).comp σ) (.id R S) fun _ _ ↦ .all _ _
  have hlies : (q.comap τ).LiesOver P := ⟨by
    ext a
    rw [← hσP, q.over_def (maximalIdeal R)]
    simp [τ, Ideal.under, Algebra.TensorProduct.algebraMap_apply]⟩
  have hcomap : (q.comap τ).comap Algebra.TensorProduct.includeRight.toRingHom = q := by
    ext a
    simp [τ]
  have hP' : q.comap τ = P' :=
    Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hbij _ _ (by rw [hcomap, hP'q])
  refine ⟨τ e, he.map τ, by rw [← hP'] at heP'; exact heP', ?_⟩
  have hτ : Function.Surjective τ := fun s ↦ ⟨1 ⊗ₜ s, by simp [τ]⟩
  have h1 : (Localization.awayMap τ.toRingHom e).Finite :=
    .of_surjective _ (Localization.awayMap_surjective_iff.2 fun s ↦ by
      obtain ⟨a, rfl⟩ := hτ s
      exact ⟨a, 0, by simp⟩)
  have h2 := h1.comp (RingHom.finite_algebraMap.2 hfin)
  have h3 : (Localization.awayMap τ.toRingHom e).comp (algebraMap R' (Localization.Away e)) =
      (algebraMap R (Localization.Away (τ e))).comp σ.toRingHom := by
    ext a
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R' (R' ⊗[R] S), Localization.awayMap,
      IsLocalization.Away.map, IsLocalization.map_eq, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply R S]
    simp [τ]
  rw [h3] at h2
  exact RingHom.finite_algebraMap.1 h2.of_comp_finite

section General

variable {X Y Z S : Scheme.{u}}

theorem isFinite_opensRange_ι_comp (i : Y ⟶ X) [IsOpenImmersion i] (f : X ⟶ S)
    [IsFinite (i ≫ f)] : IsFinite (i.opensRange.ι ≫ f) := by
  have : i.opensRange.ι ≫ f = i.isoOpensRange.inv ≫ i ≫ f := by simp
  rw [this]
  infer_instance

theorem isFinite_of_comp_surjective (p : Y ⟶ X) [Surjective p] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [IsFinite (p ≫ f)] : IsFinite f := by
  have : UniversallyClosed f := .of_comp_surjective p _
  have : LocallyQuasiFinite f := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((p ≫ f).finite_preimage_singleton s).image p).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := p.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  have : IsProper f := {}
  exact .of_isProper_of_locallyQuasiFinite _

theorem isFinite_sup_ι_comp (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] (U V : X.Opens)
    [IsFinite (U.ι ≫ f)] [IsFinite (V.ι ≫ f)] : IsFinite ((U ⊔ V).ι ≫ f) := by
  let a : U.toScheme ⟶ (U ⊔ V).toScheme := X.homOfLE le_sup_left
  let b : V.toScheme ⟶ (U ⊔ V).toScheme := X.homOfLE le_sup_right
  have ha : a ≫ (U ⊔ V).ι = U.ι := X.homOfLE_ι _
  have hb : b ≫ (U ⊔ V).ι = V.ι := X.homOfLE_ι _
  have hsurj : Surjective (coprod.desc a b) := ⟨by
    rintro ⟨x, hx | hx⟩
    · exact ⟨(coprod.inl : _ ⟶ U.toScheme ⨿ V.toScheme) ⟨x, hx⟩,
        (U ⊔ V).ι.isOpenEmbedding.injective congr($(show coprod.inl ≫ coprod.desc a b ≫ (U ⊔ V).ι
          = U.ι by rw [coprod.inl_desc_assoc, ha]) ⟨x, hx⟩)⟩
    · exact ⟨(coprod.inr : _ ⟶ U.toScheme ⨿ V.toScheme) ⟨x, hx⟩,
        (U ⊔ V).ι.isOpenEmbedding.injective congr($(show coprod.inr ≫ coprod.desc a b ≫ (U ⊔ V).ι
          = V.ι by rw [coprod.inr_desc_assoc, hb]) ⟨x, hx⟩)⟩⟩
  have hfin : IsFinite (coprod.desc a b ≫ (U ⊔ V).ι ≫ f) := by
    rw [coprod.desc_comp, reassoc_of% ha, reassoc_of% hb]
    infer_instance
  exact isFinite_of_comp_surjective (coprod.desc a b) _

theorem isFinite_bot_ι_comp (f : X ⟶ S) : IsFinite ((⊥ : X.Opens).ι ≫ f) :=
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  inferInstance

def finitePart (f : X ⟶ S) : X.Opens := sSup {U : X.Opens | IsFinite (U.ι ≫ f)}

theorem mem_finitePart {f : X ⟶ S} {x : X} :
    x ∈ finitePart f ↔ ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ x ∈ U :=
  TopologicalSpace.Opens.mem_sSup

theorem le_finitePart (f : X ⟶ S) (U : X.Opens) [h : IsFinite (U.ι ≫ f)] : U ≤ finitePart f :=
  le_sSup h

end General

section Local

variable {R : CommRingCat.{u}} [IsLocalRing R] {X Y Z : Scheme.{u}}

theorem opens_eq_top_of_closedFibre_subset (g : Y ⟶ Spec R) [UniversallyClosed g] (V : Y.Opens)
    (hV : ∀ y : Y, g y = closedPoint R → y ∈ V) : V = ⊤ := by
  by_contra h
  have hne : (g '' (V : Set Y)ᶜ).Nonempty := by
    refine Set.Nonempty.image _ (Set.nonempty_compl.2 fun h' ↦ h ?_)
    exact TopologicalSpace.Opens.ext h'
  obtain ⟨s, hs⟩ := hne
  have hcl : IsClosed (g '' (V : Set Y)ᶜ) := g.isClosedMap _ V.isOpen.isClosed_compl
  obtain ⟨y, hy, e⟩ := (specializes_closedPoint (R := R) s).mem_closed hcl hs
  exact hy (hV y e)

theorem preimage_eq_top_of_closedFibre_subset (f : X ⟶ Spec R) (U : X.Opens)
    (hU : ∀ x : X, f x = closedPoint R → x ∈ U) (h : Y ⟶ X) [UniversallyClosed (h ≫ f)] :
    h ⁻¹ᵁ U = ⊤ :=
  opens_eq_top_of_closedFibre_subset (h ≫ f) _ fun y hy ↦ hU (h y) (by simpa using hy)

theorem finitePart_le_preimage_of_closedFibre_subset (f : X ⟶ Spec R) (U : X.Opens)
    (hU : ∀ x : X, f x = closedPoint R → x ∈ U) (h : Y ⟶ X) :
    finitePart (h ≫ f) ≤ h ⁻¹ᵁ U := by
  refine sSup_le fun V hV x hx ↦ ?_
  have : IsFinite ((V.ι ≫ h) ≫ f) := by rwa [Category.assoc]
  have := (preimage_eq_top_of_closedFibre_subset f U hU (V.ι ≫ h)).ge (Set.mem_univ ⟨x, hx⟩)
  exact this

theorem finitePart_eq_of_closedFibre_subset (f : X ⟶ Spec R) (U : X.Opens) [IsFinite (U.ι ≫ f)]
    (hU : ∀ x : X, f x = closedPoint R → x ∈ U) : finitePart f = U :=
  le_antisymm (by simpa using finitePart_le_preimage_of_closedFibre_subset f U hU (𝟙 X))
    (le_finitePart f U)

end Local

section Henselian

variable {R : CommRingCat.{u}} [HenselianLocalRing R] {X Y Z : Scheme.{u}}

theorem mem_finitePart_of_eq_closedPoint (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (x : X) (hx : f x = closedPoint R) : x ∈ finitePart f := by
  obtain ⟨A, i, _, y, rfl⟩ : ∃ (A : CommRingCat.{u}) (i : Spec A ⟶ X), IsOpenImmersion i ∧
      ∃ y, i y = x := by
    obtain ⟨j, y, hy⟩ := X.affineOpenCover.openCover.exists_eq x
    exact ⟨_, X.affineOpenCover.f j, X.affineOpenCover.map_prop j, y, hy⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have h₁ : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    infer_instance
  have h₂ : φ.hom.QuasiFinite := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite), hφ]
    infer_instance
  algebraize [φ.hom]
  have : y.asIdeal.LiesOver (maximalIdeal R) := by
    have : Spec.map φ y = closedPoint R := by rw [hφ]; simpa using hx
    exact ⟨congr(($this).asIdeal).symm⟩
  have := y.isPrime
  obtain ⟨e, -, hey, hfin⟩ := exists_idempotent_finite_away_of_henselian R y.asIdeal
  let j : Spec (.of (Localization.Away e)) ⟶ Spec A :=
    Spec.map (CommRingCat.ofHom (algebraMap A _))
  have : IsFinite ((j ≫ i) ≫ f) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 hfin
  refine mem_finitePart.2 ⟨(j ≫ i).opensRange, isFinite_opensRange_ι_comp _ f, ?_⟩
  obtain ⟨z, hz⟩ : y ∈ Set.range j :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).ge hey
  exact ⟨z, by simp [hz]⟩

theorem preimage_finitePart_eq_top (f : X ⟶ Spec R) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (h : Y ⟶ X) [IsFinite (h ≫ f)] : h ⁻¹ᵁ finitePart f = ⊤ :=
  preimage_eq_top_of_closedFibre_subset f _ (mem_finitePart_of_eq_closedPoint f) h

variable (f : X ⟶ Spec R) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyQuasiFinite f]

instance isFinite_finitePart : IsFinite ((finitePart f).ι ≫ f) := by
  have key : ∀ s : Set X, s.Finite → (∀ x ∈ s, x ∈ finitePart f) →
      ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x ∈ s, x ∈ U := by
    intro s hs
    induction s, hs using Set.Finite.induction_on with
    | empty => exact fun _ ↦ ⟨⊥, isFinite_bot_ι_comp f, by simp⟩
    | @insert a s _ _ ih =>
      intro H
      obtain ⟨U, _, hU⟩ := ih fun x hx ↦ H x (.inr hx)
      obtain ⟨V, _, hV⟩ := mem_finitePart.1 (H a (.inl rfl))
      refine ⟨U ⊔ V, isFinite_sup_ι_comp f U V, ?_⟩
      rintro x (rfl | hx)
      exacts [.inr hV, .inl (hU x hx)]
  obtain ⟨U, _, hU⟩ := key _ (f.finite_preimage_singleton (closedPoint R))
    (mem_finitePart_of_eq_closedPoint f)
  rwa [finitePart_eq_of_closedFibre_subset f U hU]

end Henselian

section Lift

variable {R : CommRingCat.{u}} [HenselianLocalRing R] {X Y Z : Scheme.{u}}

def finitePartLift (f : X ⟶ Spec R) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (h : Y ⟶ X) [IsFinite (h ≫ f)] : Y ⟶ finitePart f :=
  IsOpenImmersion.lift (finitePart f).ι h (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (preimage_finitePart_eq_top f h).ge (Set.mem_univ y))

theorem finitePartLift_ι (f : X ⟶ Spec R) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (h : Y ⟶ X) [IsFinite (h ≫ f)] : finitePartLift f h ≫ (finitePart f).ι = h :=
  IsOpenImmersion.lift_fac _ _ _

theorem existsUnique_lift_finitePart (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] (g : Y ⟶ Spec R) [IsFinite g] (h : Y ⟶ X) (w : h ≫ f = g) :
    ∃! l : Y ⟶ finitePart f, l ≫ (finitePart f).ι = h := by
  subst w
  exact ⟨finitePartLift f h, finitePartLift_ι f h, fun l hl ↦ by
    rw [← cancel_mono (finitePart f).ι, hl, finitePartLift_ι]⟩

end Lift

section Pullback

variable {R : CommRingCat.{u}} [HenselianLocalRing R] {P X Y Z : Scheme.{u}}

theorem isPullback_opens_inf {a : X ⟶ Z} {b : Y ⟶ Z} {p : P ⟶ X} {q : P ⟶ Y}
    (H : IsPullback p q a b) (U : X.Opens) (V : Y.Opens) (W : P.Opens)
    (hW : W = p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ V) :
    IsPullback (p.resLE U W (hW.trans_le inf_le_left)) (q.resLE V W (hW.trans_le inf_le_right))
      (U.ι ≫ a) (V.ι ≫ b) := by
  have hr (s : PullbackCone (U.ι ≫ a) (V.ι ≫ b)) : Set.range
      (H.lift (s.fst ≫ U.ι) (s.snd ≫ V.ι) (by simpa using s.condition)) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hW]
    refine ⟨?_, ?_⟩
    · change p _ ∈ U
      rw [← Scheme.Hom.comp_apply, H.lift_fst]
      exact (s.fst x).2
    · change q _ ∈ V
      rw [← Scheme.Hom.comp_apply, H.lift_snd]
      exact (s.snd x).2
  refine ⟨⟨by simp [H.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ IsOpenImmersion.lift W.ι _ (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    simp [← cancel_mono U.ι]
  · intro s
    simp [← cancel_mono V.ι]
  · intro s m h₁ h₂
    rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac]
    apply H.hom_ext
    · simp [← h₁]
    · simp [← h₂]

end Pullback

section Group

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {R : CommRingCat.{u}}

end Group

end GlobalTheory
