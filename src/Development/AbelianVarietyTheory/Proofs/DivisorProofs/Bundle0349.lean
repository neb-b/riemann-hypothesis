module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZmodActionModelOfIsColimitFiltered
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.TorsorColim

theorem exists_common_under {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    (k : K) (l : I → K) (f : ∀ i, k ⟶ l i) :
    ∃ (m : K) (p : k ⟶ m) (r : ∀ i, l i ⟶ m), ∀ i, f i ≫ r i = p := by
  classical
  letI := Fintype.ofFinite I
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan k l f)
  exact ⟨c'.pt, c'.ι.app none, fun i => c'.ι.app (some i), fun i => c'.w (.init i)⟩

theorem exists_stage_eq {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.EssFiniteType) {k : K}
    (a b : I → (S ⟶ E.obj k)) (ha : ∀ i, φ ≫ a i = α.app k) (hb : ∀ i, φ ≫ b i = α.app k)
    (hab : ∀ i, a i ≫ c.ι.app k = b i ≫ c.ι.app k) :
    ∃ (m : K) (p : k ⟶ m), ∀ i, a i ≫ E.map p = b i ≫ E.map p := by
  choose l f₁ f₂ h using fun i => RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit R E α φ c hc
    hφ (a i) (ha i) (b i) (hb i) (hab i)
  obtain ⟨m, p, r, hr⟩ := exists_common_under k (fun i => IsFiltered.coeq (f₁ i) (f₂ i))
    (fun i => f₁ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i))
  refine ⟨m, p, fun i => ?_⟩
  have h2 : (f₂ i ≫ IsFiltered.coeqHom (f₁ i) (f₂ i)) ≫ r i = p := by
    rw [← IsFiltered.coeq_condition]; exact hr i
  conv_lhs => rw [← hr i]
  conv_rhs => rw [← h2]
  simp only [E.map_comp, Category.assoc]
  rw [reassoc_of% (h i)]

theorem exists_stage_factor {K : Type} [SmallCategory K] [IsFiltered K] {I : Type} [Finite I]
    {R S : CommRingCat.{0}} (E : K ⥤ CommRingCat.{0}) (α : (Functor.const _).obj R ⟶ E)
    (φ : R ⟶ S) (c : Cocone E) (hc : IsColimit c) (hφ : φ.hom.FinitePresentation)
    (a : I → (S ⟶ c.pt)) (ha : ∀ i k, φ ≫ a i = α.app k ≫ c.ι.app k) :
    ∃ (m : K) (s : I → (S ⟶ E.obj m)), ∀ i, φ ≫ s i = α.app m ∧ s i ≫ c.ι.app m = a i := by
  classical
  choose l s h₁ h₂ using fun i => RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R E α φ c
    hc hφ (a i) (ha i)
  letI := Fintype.ofFinite I
  obtain ⟨m, hm⟩ := IsFiltered.sup_objs_exists (Finset.univ.image l)
  have r : ∀ i, l i ⟶ m := fun i => (hm (Finset.mem_image_of_mem l (Finset.mem_univ i))).some
  refine ⟨m, fun i => s i ≫ E.map (r i), fun i => ⟨?_, ?_⟩⟩
  · rw [reassoc_of% (h₁ i), ← α.naturality]
    exact Category.id_comp _
  · rw [Category.assoc, c.w, ← h₂]

theorem exists_stage_action {K : Type} [SmallCategory K] [IsFiltered K] {G : Type} [Monoid G]
    [Finite G] {R S : CommRingCat.{0}} (P E : K ⥤ CommRingCat.{0})
    (β : ∀ k, R ⟶ P.obj k) (φ : R ⟶ S) (hφ : φ.hom.FinitePresentation)
    (u : P ⟶ E) (v : (Functor.const _).obj S ⟶ E)
    (hpo : ∀ k, IsPushout φ (β k) (v.app k) (u.app k))
    (c : Cocone E) (hc : IsColimit c) (τ : G → (c.pt ⟶ c.pt)) (τ1 : τ 1 = 𝟙 _)
    (τm : ∀ g h, τ (g * h) = τ h ≫ τ g)
    (τu : ∀ g k, u.app k ≫ c.ι.app k ≫ τ g = u.app k ≫ c.ι.app k) :
    ∃ (m : K) (σ : G → (E.obj m ⟶ E.obj m)), σ 1 = 𝟙 _ ∧ (∀ g h, σ (g * h) = σ h ≫ σ g) ∧
      (∀ g, u.app m ≫ σ g = u.app m) ∧ ∀ g, σ g ≫ c.ι.app m = c.ι.app m ≫ τ g := by
  let α : (Functor.const K).obj R ⟶ E := (Functor.const K).map φ ≫ v
  let w : ∀ k, S ⟶ E.obj k := fun k => v.app k
  let ι : ∀ k, E.obj k ⟶ c.pt := fun k => c.ι.app k
  have hα : ∀ k, α.app k = φ ≫ w k := fun k => rfl
  have hι : ∀ {k l} (f : k ⟶ l), E.map f ≫ ι l = ι k := fun f => c.w f
  have hw : ∀ {k l} (f : k ⟶ l), w k ≫ E.map f = w l := fun f =>
    (v.naturality f).symm.trans (Category.id_comp _)
  have hpo' : ∀ k, IsPushout φ (β k) (w k) (u.app k) := hpo
  have τu' : ∀ g k, u.app k ≫ ι k ≫ τ g = u.app k ≫ ι k := τu
  have k₀ : K := IsFiltered.nonempty.some
  have hwι : ∀ k, w k ≫ ι k = w k₀ ≫ ι k₀ := fun k => by
    rw [← hι (IsFiltered.leftToMax k k₀), ← hι (IsFiltered.rightToMax k k₀), reassoc_of% hw,
      reassoc_of% hw]
  obtain ⟨k, s, hs⟩ := exists_stage_factor E α φ c hc hφ (fun g : G => w k₀ ≫ ι k₀ ≫ τ g)
    (fun g k => by
      change φ ≫ w k₀ ≫ ι k₀ ≫ τ g = (φ ≫ w k) ≫ ι k
      rw [← reassoc_of% (hwι k), (hpo' k).w, reassoc_of% (hpo' k).w, τu', Category.assoc])
  have hs1 : ∀ g, φ ≫ s g = φ ≫ w k := fun g => (hs g).1
  have hs2 : ∀ g, s g ≫ ι k = w k₀ ≫ ι k₀ ≫ τ g := fun g => (hs g).2
  let σ : ∀ {l} (_ : k ⟶ l), G → (E.obj l ⟶ E.obj l) := fun {l} f g =>
    (hpo' l).desc (s g ≫ E.map f) (u.app l) (by
      rw [reassoc_of% hs1, hw, (hpo' l).w])
  have σw : ∀ {l} (f : k ⟶ l) g, w l ≫ σ f g = s g ≫ E.map f := fun f g => (hpo' _).inl_desc _ _ _
  have σu : ∀ {l} (f : k ⟶ l) g, u.app l ≫ σ f g = u.app l := fun f g => (hpo' _).inr_desc _ _ _
  have σι : ∀ {l} (f : k ⟶ l) g, σ f g ≫ ι l = ι l ≫ τ g := fun {l} f g => by
    apply (hpo' l).hom_ext
    · rw [reassoc_of% σw, hι, hs2, reassoc_of% (hwι l)]
    · rw [reassoc_of% σu, τu']
  have σmap : ∀ {l} (f : k ⟶ l) g, σ (𝟙 k) g ≫ E.map f = E.map f ≫ σ f g := fun {l} f g => by
    apply (hpo' k).hom_ext
    · rw [reassoc_of% σw, reassoc_of% hw, σw, E.map_id, Category.id_comp]
    · rw [reassoc_of% σu, ← u.naturality_assoc, σu, u.naturality]
  obtain ⟨m, p, hp⟩ := exists_stage_eq (I := Option (G × G)) E α φ c hc
    (RingHom.FiniteType.essFiniteType (RingHom.FiniteType.of_finitePresentation hφ)) (k := k)
    (fun i => i.elim (s 1) (fun x => s (x.1 * x.2)))
    (fun i => i.elim (w k) (fun x => s x.2 ≫ σ (𝟙 k) x.1))
    (by
      rintro (_ | x)
      · exact hs1 _
      · exact hs1 _)
    (by
      rintro (_ | x)
      · rfl
      · change φ ≫ s x.2 ≫ σ (𝟙 k) x.1 = φ ≫ w k
        rw [reassoc_of% hs1, σw, E.map_id, Category.comp_id, hs1])
    (by
      rintro (_ | x)
      · change s 1 ≫ ι k = w k ≫ ι k
        rw [hs2, τ1, Category.comp_id, hwι k]
      · change s (x.1 * x.2) ≫ ι k = (s x.2 ≫ σ (𝟙 k) x.1) ≫ ι k
        rw [Category.assoc, σι, reassoc_of% hs2, hs2, τm])
  refine ⟨m, σ p, ?_, fun g h => ?_, σu p, σι p⟩
  · apply (hpo' m).hom_ext
    · rw [σw, Category.comp_id, ← hw p]
      exact hp none
    · rw [σu, Category.comp_id]
  · apply (hpo' m).hom_ext
    · rw [σw, reassoc_of% σw, ← σmap, ← Category.assoc]
      exact hp (some (g, h))
    · rw [σu, reassoc_of% σu, σu]

theorem finitePresentation_of_isPushout {R S R' S' : CommRingCat.{0}} {φ : R ⟶ S} {β : R ⟶ R'}
    {v : S ⟶ S'} {u : R' ⟶ S'} (h : IsPushout φ β v u) (hφ : φ.hom.FinitePresentation) :
    u.hom.FinitePresentation := by
  algebraize [φ.hom, β.hom, v.hom, u.hom, v.hom.comp φ.hom]
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R S R' S' := CommRingCat.isPushout_iff_isPushout.1 h
  exact RingHom.finitePresentation_isStableUnderBaseChange R S R' S' hφ

theorem exists_algEquiv_of_isPushout {R C B D : Type} [CommRing R] [CommRing C] [CommRing B]
    [CommRing D] [Algebra R C] [Algebra R B] [Algebra C D] (ι : B →+* D)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R C)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap C D)) (CommRingCat.ofHom ι)) :
    ∃ e : C ⊗[R] B ≃ₐ[C] D, ∀ x y, e (x ⊗ₜ y) = algebraMap C D x * ι y := by
  algebraize [ι, (algebraMap C D).comp (algebraMap R C)]
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have : Algebra.IsPushout R C B D := CommRingCat.isPushout_iff_isPushout.1 h
  exact ⟨Algebra.IsPushout.equiv R C B D, fun x y => Algebra.IsPushout.equiv_tmul R C B D x y⟩

theorem exists_action_model_of_isColimit : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (q : ℕ), 0 < q → ∀ (j : J) (A : Type) [CommRing A] [Algebra (F.obj j) A]
    [Algebra.FinitePresentation (F.obj j) A] (D : Type) [CommRing D] [Algebra c.pt D]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[c.pt] D)),
    letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
    Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) →
    ∃ (k : J) (B : Type) (_ : CommRing B) (_ : Algebra (F.obj k) B)
      (_ : Algebra.FinitePresentation (F.obj k) B)
      (actB : Multiplicative (ZMod q) →* (B ≃ₐ[F.obj k] B)),
      letI : Algebra (F.obj k) c.pt := (c.ι.app k).hom.toAlgebra
      ∃ e : c.pt ⊗[F.obj k] B ≃ₐ[c.pt] D, ∀ (g : Multiplicative (ZMod q)) (x : c.pt ⊗[F.obj k] B),
        e (GlobalTheory.TorsorColim.bcAct c.pt actB g x) = act g (e x) := by
  intro J _ _ F c hc q hq j A _ _ _ D _ _ act
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  rintro ⟨e₀⟩
  haveI : NeZero q := ⟨hq.ne'⟩
  let φ : F.obj j ⟶ CommRingCat.of A := CommRingCat.ofHom (algebraMap (F.obj j) A)
  have hφ : φ.hom.FinitePresentation := RingHom.finitePresentation_algebraMap.2 inferInstance
  let g₀ : c.pt ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap c.pt D)
  let h₀ : CommRingCat.of A ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (e₀.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := F.obj j) (A := c.pt) (B := A)).toRingHom)
  let ιc : ∀ k, F.obj k ⟶ c.pt := fun k => c.ι.app k
  have hsq : IsPushout φ (ιc j) h₀ g₀ := by
    refine (CommRingCat.isPushout_tensorProduct (F.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e₀.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · ext x
      exact e₀.commutes x
  obtain ⟨E, ι, u, v, ⟨hE⟩, hk⟩ :=
    GlobalTheory.BaseChangeColim.exists_isColimit_pushout_under J F c hc j _ _ φ h₀ g₀ hsq
  let τ : Multiplicative (ZMod q) → (CommRingCat.of D ⟶ CommRingCat.of D) := fun g =>
    CommRingCat.ofHom (act g).toRingEquiv.toRingHom
  have hτ : ∀ g, g₀ ≫ τ g = g₀ := fun g => by
    ext x
    exact (act g).commutes x
  let ι' : ∀ k, E.obj k ⟶ CommRingCat.of D := fun k => ι.app k
  let u' : ∀ k : Under j, F.obj k.right ⟶ E.obj k := fun k => u.app k
  let v' : ∀ k : Under j, CommRingCat.of A ⟶ E.obj k := fun k => v.app k
  have hu : ∀ k, u' k ≫ ι' k = ιc k.right ≫ g₀ := fun k => (hk k).2.2
  have hv : ∀ k, v' k ≫ ι' k = h₀ := fun k => (hk k).2.1
  have hpo : ∀ k : Under j, IsPushout φ (F.map k.hom) (v' k) (u' k) := fun k => (hk k).1
  obtain ⟨m, σ, σ1, σm, σu, σι⟩ := exists_stage_action (Under.forget j ⋙ F) E
    (fun k => F.map k.hom) φ hφ u v hpo (Cocone.mk _ ι) hE τ
    (by
      ext x
      change act 1 x = x
      simp)
    (fun g h => by
      ext x
      change act (g * h) x = act g (act h x)
      simp)
    (fun g k => by
      change u' k ≫ ι' k ≫ τ g = u' k ≫ ι' k
      rw [reassoc_of% hu, hτ, hu])
  letI : Algebra (F.obj m.right) (E.obj m) := (u' m).hom.toAlgebra
  letI : Algebra (F.obj m.right) c.pt := (c.ι.app m.right).hom.toAlgebra
  let σ' : Multiplicative (ZMod q) →* (E.obj m →ₐ[F.obj m.right] E.obj m) :=
    { toFun := fun g => ⟨(σ g).hom, fun x => congr(($(σu g)).hom x)⟩
      map_one' := AlgHom.ext fun x => congr(($σ1).hom x)
      map_mul' := fun g h => AlgHom.ext fun x => congr(($(σm g h)).hom x) }
  have hsq' : IsPushout (u' m) (ιc m.right) (ι' m) g₀ := by
    have hcw : F.map m.hom ≫ ιc m.right = ιc j := c.w m.hom
    refine IsPushout.of_top ?_ (hu m) (hpo m)
    rw [hv]
    exact hcw ▸ hsq
  obtain ⟨e, he⟩ := exists_algEquiv_of_isPushout (R := F.obj m.right) (C := c.pt) (B := E.obj m)
    (D := D) (ι' m).hom hsq'.flip
  refine ⟨m.right, E.obj m, inferInstance, inferInstance,
    finitePresentation_of_isPushout (hpo m) hφ,
    (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp σ'.toHomUnits, e, fun g x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul s b =>
    rw [bcAct_tmul, he, he, map_mul, AlgEquiv.commutes]
    congr 1
    exact congr(($(σι g)).hom b)

end GlobalTheory.TorsorColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIntegralClosureOverGenericFibreOfEtaleStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_integralClosureOverGenericFibre_of_etale : ∀ (A R D : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra A R] [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    Module.Finite R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  first | (exact @GlobalTheory.KeyOriginNoeth.finite_closure) | (exact GlobalTheory.KeyOriginNoeth.finite_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.finite_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosure
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

open KaehlerDifferential in
private theorem projective_of_isScalarTower_projective (R A M : Type) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Projective R A]
    [Module.Projective A M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective A M)
  have : Module.Projective R (M →₀ A) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R : (M →₀ A) ≃ₗ[R] Π₀ _ : M, A).symm
  exact Module.Projective.of_split ((s.restrictScalars R))
    ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun m => LinearMap.congr_fun hs m)


open KaehlerDifferential in
theorem _root_.GlobalTheory.finite_projective_span_of_integralClosure :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  intro k F K _ _ _ _ _ _ _ A B hB hfin hproj W _ _ _ _ S hS hfinB hprojB
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a =>
    (hB _).2 ((integralClosure A K).algebraMap_mem a)
  letI : Algebra A B := ((algebraMap A K).codRestrict B hAB).toAlgebra
  have hcoe : ∀ (a : A) (b : B), ((a • b : B) : K) = algebraMap F K (a : F) * (b : K) := by
    intro a b
    rw [Algebra.smul_def]
    rfl
  haveI : IsScalarTower A B W := ⟨fun a b w => by
    rw [Subalgebra.smul_def, hcoe, mul_smul, algebraMap_smul, Subalgebra.smul_def,
      Subalgebra.smul_def]⟩
  let ψ : B ≃ₗ[A] integralClosure A K :=
    { toFun := fun b => ⟨b, (hB b).1 b.2⟩
      invFun := fun c => ⟨c, (hB c).2 c.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => Subtype.ext <| by
        rw [hcoe, RingHom.id_apply, SetLike.val_smul, Algebra.smul_def]
        rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite A B := Module.Finite.equiv ψ.symm
  haveI : Module.Projective A B := Module.Projective.of_equiv ψ.symm
  haveI : Module.Finite A (Submodule.span B S) := Module.Finite.trans B _
  haveI : Module.Projective A (Submodule.span B S) := projective_of_isScalarTower_projective A B _
  have hclosed : ∀ c : B, ∀ w ∈ Submodule.span A S, c • w ∈ Submodule.span A S := by
    intro c w hw
    induction hw using Submodule.span_induction with
    | mem s hs =>
      rw [Subalgebra.smul_def]
      exact Submodule.subset_span (hS c c.2 s hs)
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
    | smul a v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ a hv
  let SB : Submodule B W :=
    { carrier := Submodule.span A S
      add_mem' := Submodule.add_mem _
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun c w hw => hclosed c w hw }
  have hsets : ∀ w, w ∈ Submodule.span A S ↔ w ∈ Submodule.span B S := by
    intro w
    constructor
    · intro hw
      have hle : Submodule.span A S ≤ (Submodule.span B S).restrictScalars A :=
        Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
      exact hle hw
    · intro hw
      have hle : Submodule.span B S ≤ SB :=
        Submodule.span_le.mpr fun s hs => (Submodule.subset_span hs : s ∈ Submodule.span A S)
      exact hle hw
  let χ : Submodule.span A S ≃ₗ[A] Submodule.span B S :=
    { toFun := fun w => ⟨w, (hsets w).1 w.2⟩
      invFun := fun w => ⟨w, (hsets w).2 w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.equiv χ.symm, Module.Projective.of_equiv χ.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomain
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B], IsField B → SH B := by
  first | (exact @GlobalTheory.field_finiteType_algClosed_SH) | (exact GlobalTheory.field_finiteType_algClosed_SH) | (intros; apply GlobalTheory.field_finiteType_algClosed_SH  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCuspMulStarChG
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_GL_toLin' {F : Type} [Field F] (m : ℕ) (f : Module.End F (Fin m → F) → ℂ) :
    ∑ᶠ x : GL (Fin m) F, f (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) =
      ∑ᶠ g ∈ {g : Module.End F (Fin m → F) | IsUnit g}, f g := by
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn
    (fun x : GL (Fin m) F => (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F) : Module.End F (Fin m → F)))
    ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro x _
    exact (Units.isUnit x).map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
  · intro x _ y _ h
    exact Units.ext (Matrix.toLin'.injective h)
  · intro g hg
    have h : IsUnit ((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).symm g) := IsUnit.map _ hg
    refine ⟨h.unit, Set.mem_univ _, ?_⟩
    exact (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).apply_symm_apply g

theorem finsum_cusp_mul_star_chG : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k l : ℕ, 0 < m → ∑ᶠ x, cusp θ m k x * star (chG (rootSum θ l) m x) = (-1) ^ (m - 1) * (Nat.card (GL (Fin m) F) : ℂ) * (((Finset.range m).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ m - 1)])).card : ℂ) := by
  intro F _ _ θ hθ m k l hm
  have hr : Module.finrank F (Fin m → F) = m := by simp
  have h := ipGL_psi_rootSum F (Fin m → F) θ hθ (by rw [hr]; exact hm) k l
  rw [hr, ipGL, ← finsum_GL_toLin', glCard] at h
  rw [mul_assoc, ← h, mul_finsum]
  refine finsum_congr fun x => ?_
  simp only [cusp, psiG, chG, Matrix.charpoly_toLin', mul_assoc]

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStageStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage : ∀ (Λ : Type 1) [AddCommGroup Λ] (J : Type) [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q), (∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x) → (∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y) → ∀ j (x : P.obj j →₀ Λ), Finsupp.mapDomain (ι j) x = 0 → ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  first | (exact @GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (exact GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (intros; apply GlobalTheory.finsupp_mapDomain_eq_zero_at_stage  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  first | exact @GlobalTheory.DiagVol.colE_mem_symN_KO | exact GlobalTheory.DiagVol.colE_mem_symN_KO | (intros; apply GlobalTheory.DiagVol.colE_mem_symN_KO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUnique
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem expOf_twoSided_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧
      ∀ ex, IsExp G ex → ex = expOf G := by
  intro C _ _ v d G
  obtain ⟨h1, h2, h3⟩ := expOf_spec G
  exact ⟨h1, h3, h2⟩

end GlobalTheory.FGDepth
end

