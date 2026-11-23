module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitOnProductEqOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
section
section

open TensorProduct

namespace GlobalTheory.UnitRigidity

end GlobalTheory.UnitRigidity

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnitRigidity

theorem geometricallyConnected_of_isPullback_of_surjective {P X Y Z : Scheme.{0}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) [Surjective g]
    [GeometricallyConnected b] : GeometricallyConnected f := by
  refine ⟨fun k _ y W fst snd hW => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd g y).surjective (Classical.arbitrary _)
  let p := (pullback g y).fromSpecResidueField z
  have : Surjective (p ≫ pullback.snd g y) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have h1 := (IsPullback.of_hasPullback snd (p ≫ pullback.snd g y)).paste_horiz hW
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at h1
  have h2 := IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ h1.w) h
  have : ConnectedSpace ↥(pullback snd (p ≫ pullback.snd g y)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h2
  exact (pullback.fst snd (p ≫ pullback.snd g y)).surjective.connectedSpace
    (pullback.fst snd (p ≫ pullback.snd g y)).continuous

theorem isPullback_act {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]
    (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) :
    IsPullback ((fst T G ≫ i) * snd T G) (snd T G) q q := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  refine ⟨⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · rw [MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.one_mul]
  · have hW := ex (W.fst / W.snd) (by rw [GrpObj.div_comp, W.condition, div_self'])
    refine ⟨lift hW.choose W.snd, ?_, lift_snd _ _, ?_⟩
    · change lift _ _ ≫ (_ * _) = _
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, hW.choose_spec, div_mul_cancel]
    · intro (m : W.pt ⟶ T ⊗ G) (h1 : m ≫ (_ * _) = W.fst) (h2 : m ≫ snd T G = W.snd)
      change m = _
      refine CartesianMonoidalCategory.hom_ext _ _ (inj ?_) (by rw [lift_snd, h2])
      rw [lift_fst, hW.choose_spec, ← h1, ← h2, MonObj.comp_mul, mul_div_cancel_right,
        Category.assoc]

theorem smooth_geometricallyConnected_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G]
    (h : E.IsGt G) : Smooth G.hom ∧ GeometricallyConnected G.hom := by
  obtain ⟨D⟩ := h
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := E.isAbelian.smooth
  have := E.isAbelian.geomConnected
  obtain ⟨-, -, -, -, h1, -, -, h2, -⟩ := (splitTorus_properties S).1 E.X
  have : Smooth (splitTorus S E.X).hom := SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have H := (isPullback_act D.i D.q D.isKernel).map (Over.forget S)
  have a1 : Smooth (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (Smooth (pullback.snd (splitTorus S E.X).hom G.hom))
  have a2 : GeometricallyConnected (snd (splitTorus S E.X) G).left :=
    inferInstanceAs (GeometricallyConnected (pullback.snd (splitTorus S E.X).hom G.hom))
  have b1 : Smooth D.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) H.flip ⟨⟨‹_›, ‹_›⟩, (inferInstance : QuasiCompact D.q.left)⟩ a1
  have b2 : GeometricallyConnected D.q.left :=
    @geometricallyConnected_of_isPullback_of_surjective _ _ _ _ _ _ _ _ H D.q_surjective a2
  rw [← Over.w D.q]
  exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

open scoped TensorProduct

theorem noZeroDivisors_tensor {K A : Type} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f]
    (g : Spec (.of A) ⟶ X) [IsOpenImmersion g]
    (hg : g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (F : Type) [Field F] [Algebra K F] : NoZeroDivisors (F ⊗[K] A) := by
  let y := Spec.map (CommRingCat.ofHom (algebraMap K F))
  have : IsIntegral (pullback y f) :=
    pullback_of_geometrically' GeometricallyIntegral.geometrically_isIntegral F y
  let m : Spec (.of (F ⊗[K] A)) ⟶ pullback y f := (pullbackSpecIso K F A).inv ≫
    pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp [y]) (by simp [hg])
  have : IsIntegral (Spec (.of (F ⊗[K] A))) := isIntegral_of_isOpenImmersion m
  have : IsDomain (F ⊗[K] A) := (affine_isIntegral_iff (.of (F ⊗[K] A))).mp this
  infer_instance

theorem unit_eq_one_of_axes {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) [GeometricallyIntegral f] (e : Spec (.of K) ⟶ X) (he : e ≫ f = 𝟙 _)
    (a₁ a₂ : X ⟶ pullback f f) (h₁ : a₁ ≫ pullback.fst f f = 𝟙 X) (h₁' : a₁ ≫ pullback.snd f f = f ≫ e)
    (h₂ : a₂ ≫ pullback.fst f f = f ≫ e) (h₂' : a₂ ≫ pullback.snd f f = 𝟙 X)
    (u : Γ(pullback f f, ⊤)) (hu : IsUnit u) (u₁ : a₁.appTop.hom u = 1) (u₂ : a₂.appTop.hom u = 1) :
    u = 1 := by
  first
  | exact @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one
  | (apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimitiveUnitProduct.unit_on_product_eq_one ..)

end GlobalTheory.UnitRigidity

namespace GlobalTheory


open UnitRigidity in
theorem unit_eq_one_of_axes_of_isGt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ u : Γ((G ⊗ G).left, ⊤), IsUnit u → (lift (𝟙 G) (1 : G ⟶ G)).left.appTop.hom u = 1 → (lift (1 : G ⟶ G) (𝟙 G)).left.appTop.hom u = 1 → u = 1 := by
  intro K _ _ E G _ h u hu u₁ u₂
  obtain ⟨_, _⟩ := UnitRigidity.smooth_geometricallyConnected_of_isGt E G h
  have := geometricallyIntegral_of_smooth G.hom
  have h1 : (1 : G ⟶ G).left = G.hom ≫ (η[G] : 𝟙_ _ ⟶ G).left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  refine UnitRigidity.unit_eq_one_of_axes G.hom (η[G] : 𝟙_ _ ⟶ G).left (Over.w _) _ _ ?_ ?_ ?_ ?_ u hu u₁ u₂
  · exact congrArg (·.left) (lift_fst (𝟙 G) (1 : G ⟶ G))
  · exact (congrArg (·.left) (lift_snd (𝟙 G) (1 : G ⟶ G))).trans h1
  · exact (congrArg (·.left) (lift_fst (1 : G ⟶ G) (𝟙 G))).trans h1
  · exact congrArg (·.left) (lift_snd (1 : G ⟶ G) (𝟙 G))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private theorem surjective_flat_quasiCompact_spMap {k K : Type} [Field k] [Field K] (σ : k →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Surjective (Spec.map (CommRingCat.ofHom σ))
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · show Flat (Spec.map (CommRingCat.ofHom σ))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    show Module.Flat k K
    infer_instance
  · show QuasiCompact (Spec.map (CommRingCat.ofHom σ))
    infer_instance


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.hom_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  intro k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f
  letI : Algebra k K := σ.toAlgebra
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) :=
    surjective_flat_quasiCompact_spMap σ
  haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc
  haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc
  haveI : QuasiCompact X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc
  haveI : QuasiSeparated X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs
  haveI : LocallyOfFiniteType Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft
  haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance
  haveI : LocallyOfFinitePresentation Y₀.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) := hX
  have hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom =
      pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom := by
    simp only [Category.assoc, hY.w, Over.w_assoc]
    rw [hX'.isoPullback_inv_snd_assoc]
    exact pullback.condition.symm
  obtain ⟨R, Ψ, hRfg, hΨ, hRΨ⟩ :=
    _root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ
  obtain ⟨s, hs⟩ := hRfg
  refine ⟨s, ?_⟩
  intro k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s
  letI : Algebra k k₁ := α.toAlgebra
  have hβα' : ∀ r : k, β (α r) = σ r := fun r => by rw [← hβα]; rfl
  let β' : k₁ →ₐ[k] K := { β with commutes' := fun r => hβα' r }
  have hβinj : Function.Injective β' := β.injective
  have hle : R ≤ β'.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsβ hx
    exact ⟨y, rfl⟩
  let g : R →ₐ[k] k₁ :=
    (AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hg : ∀ x : R, β' (g x) = R.val x := fun x =>
    congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))
  have hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hX₁
  have hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hY₁
  have hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom =
      X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁) := by
    simp only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc,
      hX₁'.isoPullback_hom_fst_assoc]
    exact hX₁'.w
  have key : φ₁ ≫ hX₁'.isoPullback.hom =
      hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]
    · rw [Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]
  refine ⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩
  show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁
  apply hY₁'.hom_ext
  · rw [Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key,
      _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtOfSplit
section
universe u

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtTorus

theorem isTorus_splitTorus (k : Type u) [Field k] (X : Type u) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] : IsTorus (splitTorus (Spec (CommRingCat.of k)) X) :=
  ⟨GlobalTheory.Diag.isCommMonObj _ X, inferInstance, inferInstance,
    ⟨k, inferInstance, inferInstance, X, inferInstance, inferInstance, inferInstance,
      GlobalTheory.Diag.baseChangeIso _ X, GlobalTheory.Diag.baseChangeIso_isMonHom _ X⟩⟩

def torusExtOfSplit {k : Type u} [Field k] {G : Over (Spec (CommRingCat.of k))} [GrpObj G]
    (E : TorusExtension G) : TorusExt G :=
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  { B := E.B
    isAbelian := E.isAbelian
    q := E.q
    q_hom := E.q_hom
    q_flat := E.q_flat
    q_surjective := E.q_surjective
    q_quasiCompact := E.q_quasiCompact
    T₀ := splitTorus (Spec (CommRingCat.of k)) E.X
    isTorus := isTorus_splitTorus k E.X
    i := E.i
    i_hom := E.i_hom
    isKernel := E.isKernel }

theorem nonempty_torusExt_of_split : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Nonempty (TorusExtension G) → Nonempty (TorusExt G) :=
  fun _ _ _ _ h => h.map torusExtOfSplit

end GlobalTheory.SplitExtTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactor
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.SymLift

theorem odd_root_iff {U : Type} [CommGroup U] (j : ℕ) (E P w : U) (h : E ^ (2 * j + 1) = P ^ 2) :
    w = P / E ^ j ↔ (w ^ 2 = E ∧ w ^ (2 * j + 1) = P) := by
  constructor
  · rintro rfl
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_pow] at h'
    constructor
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -h'
    · apply Additive.ofMul.injective
      simp only [ofMul_pow, ofMul_div]
      linear_combination (norm := module) -(j • h')
  · rintro ⟨rfl, rfl⟩
    rw [← pow_mul, pow_succ, mul_div_cancel_left]

variable {O : Type} [CommRing O] (N : NumD O)

theorem tk_pow {k : ℕ} (p p' : N.QT k) :
    N.tk p p' ^ k = N.τ p.1.1.toAdd p'.1.1.toAdd *
      (cubN N.θ k 1 p.1.2.b (p'.1.2.b ^ k) * cubN N.θ k 1 p'.1.2.b p.1.2.b ^ k) := by
  have a := NumD.Gt.pow_s p.1.2 k p'.1.1.toAdd
  rw [N.mem_QT.1 p.2, NumD.io_s, ← N.QT_pow_b p'] at a
  rw [NumD.tk, mul_pow, ← a, mul_assoc]

theorem tk_mul_left {k : ℕ} (p p' p'' : N.QT k) :
    N.tk (p * p') p'' * N.θ p''.1.2.b p.1.2.b p'.1.2.b ^ k = N.tk p p'' * N.tk p' p'' := by
  have a := N.cub.N_add k 1 p''.1.2.b p.1.2.b p'.1.2.b
  rw [N.cub.face, mul_one, one_mul, N.QT_pow_b p''] at a
  change p.1.2.s p''.1.1.toAdd * p'.1.2.s p''.1.1.toAdd / N.θ (N.c p''.1.1.toAdd) p.1.2.b p'.1.2.b *
    cubN N.θ k 1 p''.1.2.b (p.1.2.b * p'.1.2.b) * _ = _
  replace a := congrArg Additive.ofMul a
  apply Additive.ofMul.injective
  simp only [NumD.tk, ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) a

theorem tk_one_left {k : ℕ} (p : N.QT k) : N.tk 1 p = 1 := by
  change 1 * cubN N.θ k 1 p.1.2.b 1 = 1
  rw [N.cub.N_one, one_mul]

theorem wQ_iff {k : ℕ} (hk : Odd k) (p : N.QT k) (w : Oˣ) :
    w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧
      w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b) := by
  obtain ⟨j, rfl⟩ := hk
  have e : N.wQ p = N.ψ p.1.1.toAdd * mulq N.θ N.σ (2 * j + 1) p.1.2.b /
      (N.tk p p / dbl N.θ N.σ p.1.2.b ^ (2 * j + 1)) ^ j := by
    have : (2 * j + 1 - 1) / 2 = j := by omega
    simp only [NumD.wQ, NumB.wS, NumD.tk, this]
  rw [e, odd_root_iff, eq_div_iff_mul_eq']
  have a := tk_pow N p p
  have b := (_root_.GlobalTheory.PsiQuadratic.main O N 0 p.1.1.toAdd).1
  have c := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB (2 * j + 1) 0 p.1.2.b 1).2.2.1
  rw [← N.QT_pow_b p] at b
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c ⊢
  linear_combination (norm := module) a + b + c

theorem dbl_mul (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by
  have a := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB 2 0 x y).2.1
  have c := N.cub.coc x y y x
  rw [N.cub.s12 (x * y), N.cub.s12 x y x, N.cub.s12 x (y * y), N.cub.s12 y y x] at c
  simp only [mulq, cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul, mul_one,
    N.cub.face, div_one, sq] at a
  rw [N.cub.s12 y y x] at a
  replace a := congrArg Additive.ofMul a
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a c ⊢
  linear_combination (norm := abel) c - a

theorem wQ_mul {k : ℕ} (hk : Odd k) (p p' : N.QT k) :
    N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  obtain ⟨b₁, b₂⟩ := (wQ_iff N hk p' _).1 rfl
  rw [← div_eq_iff_eq_mul', wQ_iff N hk]
  have k₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).2.2.2.1
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  constructor
  · have t₁ := tk_mul_left N p p' (p * p')
    have t₂ := tk_mul_left N p p' p
    have t₃ := tk_mul_left N p p' p'
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p).1
    have w₃ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p' p').1
    have d := dbl_mul N p.1.2.b p'.1.2.b
    have e : (p * p').1.2.b = p.1.2.b * p'.1.2.b := rfl
    rw [e] at t₁ ⊢
    obtain ⟨j, rfl⟩ := hk
    have : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    rw [this]
    have a₁ := E a₁; have b₁ := E b₁; have k₁ := E k₁; have t₁ := E t₁; have t₂ := E t₂; have t₃ := E t₃
    have w₂ := E w₂; have w₃ := E w₃; have d := E d
    apply Additive.ofMul.injective
    simp only [NumD.wp, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ b₁ k₁ t₁ t₂ t₃ w₂ w₃ d ⊢
    linear_combination (norm := module) a₁ + b₁ - k₁ - t₁ - t₂ - t₃ + w₂ + w₃ + (2 * j + 1) • d
  · have t := tk_pow N p p'
    have m := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB k 0 p.1.2.b p'.1.2.b).2.1
    have s := N.ψ_add p.1.1.toAdd p'.1.1.toAdd
    change _ = N.ψ (p.1.1.toAdd + p'.1.1.toAdd) * mulq N.θ N.σ k (p.1.2.b * p'.1.2.b)
    have a₂ := E a₂; have b₂ := E b₂; have k₁ := E k₁; have t := E t; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₂ b₂ k₁ t m s ⊢
    linear_combination (norm := module) a₂ + b₂ - ((k + 1) / 2) • k₁ + t - m - s

theorem wQ_inv {k : ℕ} (hk : Odd k) (p : N.QT k) : N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p := by
  obtain ⟨a₁, a₂⟩ := (wQ_iff N hk p _).1 rfl
  rw [← eq_div_iff_mul_eq', eq_comm, wQ_iff N hk]
  have E := fun {u v : Oˣ} (e : u = v) => congrArg Additive.ofMul e
  have e : (p⁻¹).1.2.b = p.1.2.b⁻¹ := rfl
  constructor
  · have t₁ := tk_mul_left N p p⁻¹ p⁻¹
    have t₂ := tk_mul_left N p p⁻¹ p
    have w₁ := (GlobalTheory.T.degenerationWeilPairing_properties O N k p p⁻¹ p).1
    have w₂ := (GlobalTheory.T.degenerationWeilPairing_properties O N k 1 1 p).1
    have s := N.σ_inv p.1.2.b
    rw [mul_inv_cancel] at t₁ t₂ w₁
    rw [mul_one, left_eq_mul] at w₂
    rw [w₂] at w₁
    rw [tk_one_left, e] at t₁ t₂
    rw [N.cub.s01 p.1.2.b p.1.2.b p.1.2.b⁻¹, N.cub.s12 p.1.2.b p.1.2.b p.1.2.b⁻¹] at t₂
    rw [e]
    have a₁ := E a₁; have t₁ := E t₁; have t₂ := E t₂; have w₁ := E w₁; have s := E s
    apply Additive.ofMul.injective
    simp only [NumD.wp, dbl, inv_inv, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a₁ t₁ t₂ w₁ s ⊢
    linear_combination (norm := module) a₁ + t₁ - t₂ + w₁ - k • s
  · have m := (_root_.GlobalTheory.Ex.mulq_laws O N.toNumB k 0 p.1.2.b 1).2.2.2
    have s := N.even p.1.1.toAdd
    rw [← N.QT_pow_b p] at s
    change _ = N.ψ (-p.1.1.toAdd) * mulq N.θ N.σ k p.1.2.b⁻¹
    have a₂ := E a₂; have m := E m; have s := E s
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a₂ m s ⊢
    linear_combination (norm := module) a₂ - m - s

theorem normalising_factor : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ), Odd k → ∀ p p' : N.QT k, (∀ w : Oˣ, w = N.wQ p ↔ (w ^ 2 * dbl N.θ N.σ p.1.2.b ^ k = N.tk p p ∧ w ^ k = N.ψ p.1.1.toAdd * mulq N.θ N.σ k p.1.2.b)) ∧ N.wQ p * N.wQ p' * N.tk p p' = N.wp p p' ^ ((k + 1) / 2) * N.wQ (p * p') ∧ N.wQ p⁻¹ * N.σ p.1.2.b ^ k = N.wQ p :=
  fun _ _ N _ hk p p' => ⟨wQ_iff N hk p, wQ_mul N hk p p', wQ_inv N hk p⟩

end GlobalTheory.Ex.SymLift
end

