module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SemiProd

theorem torus_prod_iso : ∀ (S : Scheme.{0}) (X₁ X₂ : Type) [AddCommGroup X₁] [AddCommGroup X₂], IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂)) (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) := by
  intro S X₁ X₂ _ _
  let comb : ∀ {M : Type} [CommGroup M], (Multiplicative X₁ →* M) → (Multiplicative X₂ →* M) →
      (Multiplicative (X₁ × X₂) →* M) := fun u v =>
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X₁ X₂)) *
      v.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X₁ X₂))
  let l : ∀ {Z : Over S}, (Z ⟶ splitTorus S X₁) → (Z ⟶ splitTorus S X₂) → (Z ⟶ splitTorus S (X₁ × X₂)) :=
    fun {Z} f g => (splitTorusPointsEquiv S (X₁ × X₂) Z).symm
      (comb (splitTorusPointsEquiv S X₁ Z f) (splitTorusPointsEquiv S X₂ Z g))
  have f₁ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂) = f := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₁ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have f₂ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂) = g := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₂ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have u : ∀ {Z : Over S} (m : Z ⟶ splitTorus S (X₁ × X₂)),
      m = l (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
        (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    intro Z m
    apply (splitTorusPointsEquiv S (X₁ × X₂) Z).injective
    rw [MulEquiv.apply_symm_apply, SplitTorusPow.points_comp_torusMap,
      SplitTorusPow.points_comp_torusMap]
    refine MonoidHom.ext fun x => ?_
    have hx : x = Multiplicative.ofAdd (AddMonoidHom.inl X₁ X₂ x.toAdd.1) *
        Multiplicative.ofAdd (AddMonoidHom.inr X₁ X₂ x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_lhs => rw [hx]
    rw [map_mul]
    rfl
  have hl : IsLimit (BinaryFan.mk (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) :=
    BinaryFan.IsLimit.mk _ (fun f g => l f g) (fun f g => f₁ f g) (fun f g => f₂ f g)
      (fun f g m h₁ h₂ => by rw [u m]; exact congrArg₂ l h₁ h₂)
  have e : lift (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) =
      (hl.conePointUniqueUpToIso (tensorProductIsBinaryProduct _ _)).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.left⟩).symm
    · rw [lift_snd]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.right⟩).symm
  rw [e]
  infer_instance

theorem tensorHom_prop : ∀ (S : Scheme.{0}) (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange] (A B C D : Over S) (f : A ⟶ B) (g : C ⟶ D), P f.left → P g.left → P (f ⊗ₘ g).left := by
  intro S P _ _ A B C D f g hf hg
  have e : (f ⊗ₘ g).left = pullback.map A.hom C.hom B.hom D.hom f.left g.left (𝟙 S) (by simp) (by simp) := by
    first | rfl | simp
  rw [e]
  exact P.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

theorem kernel_tensor : ∀ (S : Scheme.{0}) (T₁ T₂ G₁ G₂ B₁ B₂ : Over S) [GrpObj B₁] [GrpObj B₂] (i₁ : T₁ ⟶ G₁) (i₂ : T₂ ⟶ G₂) (q₁ : G₁ ⟶ B₁) (q₂ : G₂ ⟶ B₂), IsPullback i₁ (toUnit T₁) q₁ (η : 𝟙_ (Over S) ⟶ B₁) → IsPullback i₂ (toUnit T₂) q₂ (η : 𝟙_ (Over S) ⟶ B₂) → IsPullback (i₁ ⊗ₘ i₂) (toUnit (T₁ ⊗ T₂)) (q₁ ⊗ₘ q₂) (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
  intro S T₁ T₂ G₁ G₂ B₁ B₂ _ _ i₁ i₂ q₁ q₂ h₁ h₂
  have e₁ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ fst _ _ = η := by simp [MonObj.tensorObj.one_def]
  have e₂ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ snd _ _ = η := by simp [MonObj.tensorObj.one_def]
  have c₁ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ fst _ _) ≫ q₁ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ fst _ _) h
    simp only [Category.assoc, tensorHom_fst, e₁] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have c₂ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ snd _ _) ≫ q₂ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ snd _ _) h
    simp only [Category.assoc, tensorHom_snd, e₂] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have w : (i₁ ⊗ₘ i₂) ≫ (q₁ ⊗ₘ q₂) = toUnit (T₁ ⊗ T₂) ≫ (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, e₁, tensorHom_fst_assoc]
      rw [h₁.w, ← Category.assoc, toUnit_unique (fst T₁ T₂ ≫ toUnit T₁) (toUnit _)]
    · simp only [Category.assoc, tensorHom_snd, e₂, tensorHom_snd_assoc]
      rw [h₂.w, ← Category.assoc, toUnit_unique (snd T₁ T₂ ≫ toUnit T₂) (toUnit _)]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (h₁.lift (s.fst ≫ fst _ _) (toUnit _) (c₁ _ _ s.condition))
      (h₂.lift (s.fst ≫ snd _ _) (toUnit _) (c₂ _ _ s.condition)))
    (fun s => ?_) (fun s => toUnit_unique _ _) (fun s m hm _ => ?_)⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, h₂.lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← tensorHom_fst, ← Category.assoc, hm]
      · exact toUnit_unique _ _
    · rw [lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← tensorHom_snd, ← Category.assoc, hm]
      · exact toUnit_unique _ _

variable {S : Scheme.{0}}

theorem isAbelianScheme_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  haveI := hA.comm; haveI := hB.comm; haveI := hA.smooth; haveI := hB.smooth
  haveI := hA.proper; haveI := hB.proper; haveI := hA.geomConnected; haveI := hB.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · show Smooth (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show IsProper (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom); exact GeometricallyConnected.comp _ _

theorem torusExtension_of_prod {K : Type} [Field K] {G G₁ G₂ : Over (Spec (.of K))} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] (a₁ : G ⟶ G₁) (a₂ : G ⟶ G₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)]
    (E₁ : TorusExtension G₁) (E₂ : TorusExtension G₂) : Nonempty (TorusExtension G) := by
  letI := E₁.addCommGroup; haveI := E₁.free; haveI := E₁.finite; letI := E₁.grpB
  letI := E₂.addCommGroup; haveI := E₂.free; haveI := E₂.finite; letI := E₂.grpB
  haveI := E₁.q_hom; haveI := E₂.q_hom; haveI := E₁.i_hom; haveI := E₂.i_hom
  haveI := torus_prod_iso (Spec (.of K)) E₁.X E₂.X
  have hmon : ∀ {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X'),
      IsMonHom (SplitTorusPow.torusMap (Spec (.of K)) φ) := by
    intro X X' _ _ φ
    constructor
    · have h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus _ X') ≫ SplitTorusPow.torusMap _ φ = 1 := by
        apply (splitTorusPointsEquiv _ X _).injective
        rw [SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h : ∀ {Z : Over (Spec (.of K))} (a b : Z ⟶ splitTorus _ X'),
          (a * b) ≫ SplitTorusPow.torusMap _ φ = (a ≫ SplitTorusPow.torusMap _ φ) * (b ≫ SplitTorusPow.torusMap _ φ) := by
        intro Z a b
        apply (splitTorusPointsEquiv _ X Z).injective
        rw [map_mul, SplitTorusPow.points_comp_torusMap, SplitTorusPow.points_comp_torusMap,
          SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus _ X') (splitTorus _ X')) (snd _ _)
  haveI := hmon (AddMonoidHom.inl E₁.X E₂.X)
  haveI := hmon (AddMonoidHom.inr E₁.X E₂.X)
  have key := kernel_tensor _ _ _ _ _ _ _ E₁.i E₂.i E₁.q E₂.q E₁.isKernel E₂.isKernel
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a₁ a₂)))
  haveI : IsMonHom (inv (lift a₁ a₂)) := inferInstanceAs (IsMonHom (asIso (lift a₁ a₂)).inv)
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P E₁.q.left → P E₂.q.left → P (lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)).left := by
    intro P _ _ h₁ h₂
    rw [Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _) (tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂)
  refine ⟨{ X := E₁.X × E₂.X
            B := E₁.B ⊗ E₂.B
            isAbelian := isAbelianScheme_tensor E₁.isAbelian E₂.isAbelian
            q := lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)
            q_hom := inferInstance
            q_flat := hP @Flat E₁.q_flat E₂.q_flat
            q_surjective := hP @Surjective E₁.q_surjective E₂.q_surjective
            q_quasiCompact := hP @QuasiCompact E₁.q_quasiCompact E₂.q_quasiCompact
            i := lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
                (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)) ≫ (E₁.i ⊗ₘ E₂.i) ≫ inv (lift a₁ a₂)
            i_hom := inferInstance
            isKernel := ?_ }⟩
  refine IsPullback.of_iso key (asIso (lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
    (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)))).symm (asIso (lift a₁ a₂)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact toUnit_unique _ _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem isSemiAbelian_tensor : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  intro S G₁ G₂ _ _ h₁ h₂
  haveI := h₁.comm; haveI := h₂.comm; haveI := h₁.smooth; haveI := h₂.smooth
  haveI := h₁.separated; haveI := h₂.separated; haveI := h₁.quasiCompact; haveI := h₂.quasiCompact
  haveI := h₁.geomConnected; haveI := h₂.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, fun Ω _ _ p => ?_⟩
  · show Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show QuasiCompact (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show GeometricallyConnected (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); exact GeometricallyConnected.comp _ _
  · obtain ⟨E₁⟩ := h₁.fibres Ω p
    obtain ⟨E₂⟩ := h₂.fibres Ω p
    haveI : IsIso (lift ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂))) :=
      isIso_prodComparison_of_preservesLimit_pair (Over.pullback p) G₁ G₂
    exact torusExtension_of_prod ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂)) E₁ E₂

end GlobalTheory.SemiProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialCubicalThetaFinsuppTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal

section Alg

variable {r : ℕ} {U : Type} [CommGroup U]

theorem prod_theta (a b c : Vec r) (F : Vec r → U) :
    ∏ v ∈ (theta a b c).support, F v ^ theta a b c v =
      F (a + b + c) * (F (a + b))⁻¹ * (F (a + c))⁻¹ * (F (b + c))⁻¹ * F a * F b * F c * (F 0)⁻¹ := by
  have h0 : ∀ v, F v ^ (0 : ℤ) = 1 := fun v => zpow_zero _
  have hadd : ∀ v (m n : ℤ), F v ^ (m + n) = F v ^ m * F v ^ n := fun v m n => zpow_add _ _ _
  change (theta a b c).prod (fun v n => F v ^ n) = _
  simp only [theta, sub_eq_add_neg, ← Finsupp.single_neg, Finsupp.prod_add_index' h0 hadd]
  simp only [Finsupp.prod_single_index (h := fun v (n : ℤ) => F v ^ n) (h0 _), zpow_one, zpow_neg]

end Alg

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem vecHom_add (T : Tens D D' W) (u v : Vec r) : vecHom T (u + v) = vecHom T u * vecHom T v := by
  simp only [vecHom, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

theorem vecHom_zero (T : Tens D D' W) : vecHom T 0 = 1 := by
  simp only [vecHom, Pi.zero_apply, zpow_zero, Finset.prod_const_one, _root_.mul_one]

theorem vecLat_add (T : Tens D D' W) (u v : Vec r) (y y' : D'.X) :
    vecLat T (u + v) y y' = vecLat T u y y' + vecLat T v y y' := by
  simp only [vecLat, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem vecLat_zero (T : Tens D D' W) (y y' : D'.X) : vecLat T 0 y y' = 0 := by
  simp only [vecLat, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

theorem comp_vecHom (T : Tens D D' W) {Z : Over (Spec (CommRingCat.of R))} (p q : Z ⟶ D'.P.A) (v : Vec r) :
    lift p q ≫ vecHom T v = (∏ k, (p ≫ T.pr k) ^ v (Sum.inl k)) * ∏ k, (q ≫ T.pr k) ^ v (Sum.inr k) := by
  have e := (preHom (G := D.P.A) (lift p q)).map_mul (∏ k, (fst D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inl k))
    (∏ k, (snd D'.P.A D'.P.A ≫ T.pr k) ^ v (Sum.inr k))
  simp only [map_prod, map_zpow] at e
  rw [vecHom]
  simpa only [preHom, MonoidHom.mk'_apply, lift_fst_assoc, lift_snd_assoc] using e

theorem zero_vecHom (T : Tens D D' W) (v : Vec r) : lift η[D'.P.A] η[D'.P.A] ≫ vecHom T v = 1 := by
  have h : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    haveI := T.pr_hom k
    rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  simp only [comp_vecHom, h, one_zpow, Finset.prod_const_one, _root_.mul_one]

def cPHom (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) : Multiplicative D.X →* (T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => DVR.cP D T x.toAdd) fun a b => DVR.cPoint_add D T a.toAdd b.toAdd

theorem pt_vecHom (T : Tens D D' W) (y y' : D'.X) (v : Vec r) :
    lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y') ≫ vecHom T v = DVR.cP D (TK R) (vecLat T v y y') := by
  have hp : ∀ x k, DVR.cP D' (TK R) x ≫ T.pr k = cPHom D (TK R) (Multiplicative.ofAdd (T.xe x k)) := fun x k => by
    simp only [DVR.cP, Category.assoc, T.c_pr]; rfl
  rw [comp_vecHom, show DVR.cP D (TK R) (vecLat T v y y') = cPHom D (TK R) (Multiplicative.ofAdd (vecLat T v y y')) from rfl]
  simp only [hp, vecLat, ofAdd_add, ofAdd_sum, ofAdd_zsmul, map_mul, map_prod, map_zpow]

theorem cubV_psi (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (p q s : D.X) :
    cubV D.cub (T := TK R) z J (DVR.cP D _ p) (DVR.cP D _ q) (DVR.cP D _ s) =
      (val (D.psi (p + q + s)) (𝟙 _) z J)⁻¹ * val (D.psi (p + q)) (𝟙 _) z J * val (D.psi (p + s)) (𝟙 _) z J *
        val (D.psi (q + s)) (𝟙 _) z J * (val (D.psi p) (𝟙 _) z J)⁻¹ * (val (D.psi q) (𝟙 _) z J)⁻¹ *
        (val (D.psi s) (𝟙 _) z J)⁻¹ * val (D.psi 0) (𝟙 _) z J := by
  have t := DVR.tauK_mul hJ hB p q s
  have t0 := GlobalTheory.TauBalElem.tau_zero_left hB hJ 0
  rw [GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ, GlobalTheory.TauBalBox.tau_val D hJ] at t
  rw [GlobalTheory.TauBalBox.tau_val D hJ, add_zero] at t0
  apply Additive.ofMul.injective
  have t' := congrArg Additive.ofMul t
  have t0' := congrArg Additive.ofMul t0
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at t' t0' ⊢
  linear_combination (norm := abel) t' + t0'

theorem triv_theta : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), D.TauBimult → ∀ a b c : GlobalTheory.TensBal.Vec r, GlobalTheory.TensBal.Triv T (GlobalTheory.TensBal.theta a b c) := by
  intro R _ _ D D' r W T hB a b c
  have hF : FormEq (fun I => (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left ≫ thφ D.P.A (x3 D.P.A) I) thε
      (fun v : (theta a b c).support => (vecHom T v.1).left) (fun v => theta a b c v.1) := fun U _ h => by
    refine (prod_cub (vecHom T a) (vecHom T b) (vecHom T c) h).trans ?_
    rw [Finset.prod_coe_sort (theta a b c).support (fun v => h (vecHom T v).left ^ theta a b c v), prod_theta,
      vecHom_add, vecHom_add, vecHom_add, vecHom_add, vecHom_zero]
  obtain ⟨Ξ, hΞ, hv⟩ := exists_gen D.P.isLB hF
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift (vecHom T a) (lift (vecHom T b) (vecHom T c))).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨Ξ, hΞ, fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift η[D'.P.A] η[D'.P.A]) hJ _ _ _).trans ?_)
    rw [zero_vecHom, zero_vecHom, zero_vecHom]
    exact (isCub_cubV D.cub hJ).face _ _
  · refine (hv _ _ z J hJ).trans ((val_cub D.cub (lift (DVR.cP D' (TK R) y) (DVR.cP D' (TK R) y')) hJ _ _ _).trans ?_)
    rw [pt_vecHom, pt_vecHom, pt_vecHom, cubV_psi hB hJ]
    simp only [zpow_neg, ← inv_zpow]
    rw [prod_theta (F := fun v => (val (D.psi (vecLat T v y y')) (𝟙 _) z J)⁻¹)]
    rw [vecLat_add T (a + b) c, vecLat_add T a b, vecLat_add T a c, vecLat_add T b c, vecLat_zero]
    simp only [inv_inv]

end GlobalTheory.TensBal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorAdd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal

theorem prod_support_eq {U : Type} [CommGroup U] {r : ℕ} (g : Vec r → ℤ → U) (d : Vec r →₀ ℤ) :
    ∏ v : d.support, g v.1 (d v.1) = d.prod g :=
  Finset.prod_coe_sort d.support (fun v => g v (d v))

theorem triv_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c c' : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T c' →
    GlobalTheory.TensBal.Triv T (c + c') := by
  intro R _ _ D D' r W T c c' ⟨Ξ, hΞ, h1, h2⟩ ⟨Ξ', hΞ', h1', h2'⟩
  have hform : FormEq (Sum.elim (fun v : c.support => (vecHom T v.1).left) (fun v : c'.support => (vecHom T v.1).left))
      (Sum.elim (fun v : c.support => c v.1) (fun v : c'.support => c' v.1))
      (fun v : (c + c').support => (vecHom T v.1).left) (fun v => (c + c') v.1) := by
    intro U _ h
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [prod_support_eq (fun v n => h (vecHom T v).left ^ n) c,
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) c',
      prod_support_eq (fun v n => h (vecHom T v).left ^ n) (c + c'),
      Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun _ _ _ => zpow_add _ _ _)]
  obtain ⟨Ξ'', hΞ'', hv⟩ := exists_gen D.P.isLB hform _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ hΞ hΞ')
  refine ⟨Ξ'', hΞ'', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_mul hJ, h1 z J hJ, h1' z J hJ, _root_.mul_one]
  · rw [hv _ _ z J hJ, val_mul hJ, h2 z J hJ y y', h2' z J hJ y y']
    exact (Finsupp.prod_add_index' (f := c) (g := c')
      (h := fun v n => val (D.psi (vecLat T v y y')) (𝟙 _) z J ^ (-n))
      (fun _ => by simp only [neg_zero, zpow_zero]) (fun _ _ _ => by simp only [neg_add, zpow_add])).symm

end GlobalTheory.TensBal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStronglyTrivialFormalSumTensorNeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBalNeg

theorem triv_neg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W) (c : GlobalTheory.TensBal.Vec r →₀ ℤ), GlobalTheory.TensBal.Triv T c → GlobalTheory.TensBal.Triv T (-c) := by
  intro R _ _ D D' r W T c ⟨Ξ, hΞ, h1, h2⟩
  have hF : FormEq (fun v : c.support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => -(c v.1))
      (fun v : (-c).support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => (-c) v.1) := by
    intro U _ h
    rw [Finset.prod_coe_sort c.support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ (-(c v))),
      Finset.prod_coe_sort (-c).support (fun v => h (GlobalTheory.TensBal.vecHom T v).left ^ ((-c) v)),
      Finsupp.support_neg]
    simp only [Finsupp.neg_apply]
  obtain ⟨Ξ', hΞ', hv⟩ := exists_gen D.P.isLB hF (LB.invGen D.P.L _ _ Ξ) (LB.isGen_invGen D.P.L _ _ Ξ hΞ)
  refine ⟨Ξ', hΞ', fun z J hJ => ?_, fun z J hJ y y' => ?_⟩
  · rw [hv _ _ z J hJ, val_inv, h1 z J hJ, inv_one]
  · rw [hv _ _ z J hJ, val_inv, h2 z J hJ y y', Finsupp.support_neg, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Finsupp.neg_apply, neg_neg, zpow_neg, inv_inv]

end GlobalTheory.TensBalNeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThPull
open GlobalTheory.ThetaPtMove

theorem thG_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)} {y : T ⟶ G} {c : Γ(T.left, ⊤)}
    (H : ThG G L ρ m θ y c) : ThG G L ρ m (VVRank.pullS G _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS G _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec G ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec G t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thList_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  intro S G _ _ L ρ hL hρ m N K K' _ _ i x θ pt c H
  let β : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hβ : β.left = spMap i := Over.homMk_left _ _
  refine ⟨fun a => β ≫ pt a, fun a => by simp only [Over.comp_left, hβ], fun a b h => H.1 (TorsionFieldExt.comp_injective β _ h), fun a => ?_,
    fun F _ _ k => ?_⟩
  · have q := thG_pull hL hρ β (H.2.1 a)
    have e : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.ZH.fn (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e] at q
    exact q
  · have e : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
    rw [e]
    intro p hp
    obtain ⟨a, ha⟩ := H.2.2 F (k.comp i) p hp
    refine ⟨a, ?_⟩
    rw [ha, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Over.comp_left, hβ, Category.assoc]

end GlobalTheory.UMin.ThPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeEqHilbertEisensteinJet
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem iterD_eq_jet_of_count : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t : ℂ) (κ : Emb F → ℕ) (u : List (Emb F)), 0 < τ.im → (∀ i, u.count i = κ i) → iterD u (fun z ↦ (cK F (2 * s) : ℂ) * gval (2 * s) L (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 = jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t κ u hτ hu
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  obtain ⟨Z, a, -, ha⟩ := _root_.GlobalTheory.HilbFam.exists_isCoef hE F hf 𝔞 𝔟 s hs
  have h1 := _root_.GlobalTheory.HilbFam.hasSum_iterD_gval_split F (2 * s) 𝔞 𝔟 _ a x τ c t u (even_two_mul s) ha hτ
  have h2 := _root_.GlobalTheory.HilbFam.hasSum_iterD_gval_split F (2 * s) 𝔞 𝔟 _ a x τ c t (word κ) (even_two_mul s) ha hτ
  simp only [hu] at h1
  simp only [count_word_eq] at h2
  have h3 := h1.unique h2
  have hω : (omegaFactor 𝔞 : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF
      exact abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
    have hn : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 ≠ 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
      exact_mod_cast mt FractionalIdeal.absNorm_eq_zero_iff.1 𝔞.ne_zero
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor
    exact_mod_cast mul_ne_zero (Real.rpow_pos_of_pos hd _).ne' hn
  have hc : ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ (2 * s) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ Complex.two_pi_I_ne_zero) hω)
  exact (div_left_inj' hc).1 h3

end GlobalTheory.HilbFam
end

