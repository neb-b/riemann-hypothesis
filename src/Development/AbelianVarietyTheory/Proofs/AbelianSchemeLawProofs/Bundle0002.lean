module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusHom

variable {S : Scheme.{0}}

theorem appTop_comp {A B C : Over S} (a : A ⟶ B) (b : B ⟶ C) (r : Γ(C.left, ⊤)) :
    (a ≫ b).left.appTop.hom r = a.left.appTop.hom (b.left.appTop.hom r) := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem appTop_id {A : Over S} (r : Γ(A.left, ⊤)) : (𝟙 A : A ⟶ A).left.appTop.hom r = r := by
  rw [Over.id_left, Scheme.Hom.id_appTop]
  rfl

variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem appTop_mul_charUnit {Z : Over S} (a b : Z ⟶ splitTorus S X) (χ : X) :
    (a * b).left.appTop.hom (charUnit S X χ).val =
      a.left.appTop.hom (charUnit S X χ).val * b.left.appTop.hom (charUnit S X χ).val := by
  rw [← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val, ← splitTorusPointsEquiv_val,
    map_mul]
  rfl

theorem charUnit_add (x y : X) :
    (charUnit S X (x + y)).val = (charUnit S X x).val * (charUnit S X y).val := by
  have h (z : X) := (splitTorusPointsEquiv_val S X _ (𝟙 _) z).trans (appTop_id _)
  rw [← h, ← h, ← h, ofAdd_add, map_mul, Units.val_mul]

theorem existsUnique_pullback_charUnit [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] (χ : X) :
    ∃! x : X', f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' x).val := by
  haveI : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  obtain ⟨x, hx, hu⟩ := existsUnique_character_of_mul S X' (𝟙_ (Over S))
    (splitTorusPointsEquiv S X _ (fst (splitTorus S X') (𝟙_ (Over S)) ≫ f)
      (Multiplicative.ofAdd χ)) (fun Z t t' y => by
        rw [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, ← appTop_comp,
          lift_fst_assoc, lift_fst_assoc, lift_fst_assoc, MonObj.mul_comp, appTop_mul_charUnit])
  refine ⟨x, ?_, fun x' hx' => hu x' ?_⟩
  · have := congrArg (lift (𝟙 (splitTorus S X')) (toUnit _)).left.appTop.hom hx
    rwa [splitTorusPointsEquiv_val, ← appTop_comp, ← appTop_comp, lift_fst_assoc, lift_fst,
      Category.id_comp, appTop_id] at this
  · beta_reduce at hx' ⊢
    rw [splitTorusPointsEquiv_val, appTop_comp, hx']

theorem charUnit_injective [ConnectedSpace S] {x y : X}
    (h : (charUnit S X x).val = (charUnit S X y).val) : x = y :=
  (existsUnique_pullback_charUnit (𝟙 (splitTorus S X)) x).unique (appTop_id _)
    ((appTop_id _).trans h)

theorem exists_addMonoidHom [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] :
    ∃ φ : X →+ X', ∀ χ, f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  choose c hc using fun χ => (existsUnique_pullback_charUnit f χ).exists
  refine ⟨AddMonoidHom.mk' c fun a b => charUnit_injective (S := S) ?_, hc⟩
  rw [← hc, charUnit_add, charUnit_add, map_mul, hc, hc]

end SplitTorusHom


open SplitTorusHom in
theorem exists_addEquiv_of_splitTorus_iso :
    ∀ (S : Scheme.{0}) [ConnectedSpace S] (X X' : Type) [AddCommGroup X] [AddCommGroup X']
      (θ : splitTorus S X' ≅ splitTorus S X), IsMonHom θ.hom →
      ∃ xe : X' ≃+ X, ∀ x : X',
        θ.hom.left.appTop.hom (charUnit S X (xe x)).val = (charUnit S X' x).val := by
  intro S _ X X' _ _ θ hθ
  letI : IsMonHom θ.hom := hθ
  obtain ⟨φ, hφ⟩ := SplitTorusHom.exists_addMonoidHom θ.hom
  obtain ⟨ψ, hψ⟩ := SplitTorusHom.exists_addMonoidHom θ.inv
  have h1 (x : X') : φ (ψ x) = x := SplitTorusHom.charUnit_injective (S := S) (by
    rw [← hφ, ← hψ, ← SplitTorusHom.appTop_comp, Iso.hom_inv_id,
      SplitTorusHom.appTop_id])
  have h2 (x : X) : ψ (φ x) = x := SplitTorusHom.charUnit_injective (S := S) (by
    rw [← hψ, ← hφ, ← SplitTorusHom.appTop_comp, Iso.inv_hom_id,
      SplitTorusHom.appTop_id])
  refine ⟨{ ψ with invFun := φ, left_inv := h1, right_inv := h2 }, fun x => ?_⟩
  rw [hφ]
  exact congrArg (fun z => (charUnit S X' z).val) (h1 x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusTrivial

theorem exists_isPullback {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {T G B W V : C} [GrpObj T] [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : T ⟶ G)
    [IsMonHom q] [IsMonHom i] (hk : IsPullback i (toUnit _) q η[B])
    {j : W ⟶ G} {k : V ⟶ B} {q' : W ⟶ V} (hW : IsPullback j q' q k) [Mono j] (τ : W ⟶ T)
    (hτ : ∀ (Z : C) (t : Z ⟶ T) (g g' : Z ⟶ W), g' ≫ j = (t ≫ i) * (g ≫ j) →
      g' ≫ τ = t * (g ≫ τ)) :
    ∃ a : T ⊗ W ⟶ W, IsPullback (𝟙 _) a (T ◁ q') (lift τ q') := by
  have hiq : ∀ {Z : C} (t : Z ⟶ T), (t ≫ i) ≫ q = 1 := by
    intro Z t
    rw [Category.assoc, hk.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  let s : T ⊗ W ⟶ T := fst T W * (snd T W ≫ τ)⁻¹
  have hw : ((s ≫ i) * (snd T W ≫ j)) ≫ q = (snd T W ≫ q') ≫ k := by
    rw [MonObj.mul_comp, hiq, _root_.one_mul, Category.assoc, Category.assoc, hW.w]
  let a : T ⊗ W ⟶ W := hW.lift _ _ hw
  have ha₁ : a ≫ j = (s ≫ i) * (snd T W ≫ j) := hW.lift_fst _ _ _
  have ha₂ : a ≫ q' = snd T W ≫ q' := hW.lift_snd _ _ _
  have ha₃ : a ≫ τ = fst T W := by
    rw [hτ _ _ _ _ ha₁]
    simp [s]
  have hsq : 𝟙 _ ≫ T ◁ q' = a ≫ lift τ q' := by
    ext <;> simp [ha₂, ha₃]
  refine ⟨a, ⟨hsq⟩, ⟨PullbackCone.IsLimit.mk hsq (fun c => c.fst) (fun c => by simp)
    (fun c => ?_) (fun c m h _ => by simpa using h)⟩⟩
  have h₁ : c.fst ≫ fst T W = c.snd ≫ τ := by
    simpa using c.condition =≫ fst _ _
  have h₂ : c.fst ≫ snd T W ≫ q' = c.snd ≫ q' := by
    simpa using c.condition =≫ snd _ _
  have h₃ : ((c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ← Hom.one_def]
    simp only [Category.assoc, hW.w]
    rw [reassoc_of% h₂, mul_inv_cancel]
  let r : c.pt ⟶ T := hk.lift _ _ h₃
  have hr : r ≫ i = (c.snd ≫ j) * (c.fst ≫ snd T W ≫ j)⁻¹ := hk.lift_fst _ _ _
  have h₄ : c.snd ≫ j = (r ≫ i) * ((c.fst ≫ snd T W) ≫ j) := by
    rw [hr]; simp
  have h₅ := hτ _ _ _ _ h₄
  have h₆ : c.fst ≫ s = r := by
    simp only [s, MonObj.comp_mul, GrpObj.comp_inv, h₁, h₅, Category.assoc, mul_inv_cancel_right]
  rw [← cancel_mono j, Category.assoc, ha₁, MonObj.comp_mul, reassoc_of% h₆, h₄, Category.assoc]

theorem isAffine_and_bijective {S : Scheme.{0}} {X : Type} [AddCommGroup X] {W V : Over S}
    [IsAffine V.left] (τ : W ⟶ splitTorus S X) (q : W ⟶ V) [IsIso (lift τ q)]
    {A : CommRingCat.{0}} (e : A ≅ Γ(V.left, ⊤)) (f : AddMonoidAlgebra A X →+* Γ(W.left, ⊤))
    (hf₁ : ∀ a : A, f (AddMonoidAlgebra.single 0 a) = q.left.appTop.hom (e.hom.hom a))
    (hf₂ : ∀ χ : X, f (AddMonoidAlgebra.single χ 1) = τ.left.appTop.hom (charUnit S X χ).val) :
    IsAffine W.left ∧ Function.Bijective f := by
  let R : CommRingCat.{0} := .of (AddMonoidAlgebra A X)
  let F : R ⟶ Γ(W.left, ⊤) := CommRingCat.ofHom f
  let φ : W.left ⟶ Spec R := W.left.toSpecΓ ≫ Spec.map F
  have hφ : (Scheme.ΓSpecIso R).inv ≫ φ.appTop = F := by
    rw [SplitTorusPoints.ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
      Category.comp_id]
  have hφ' : ∀ x, φ.appTop.hom ((Scheme.ΓSpecIso R).inv.hom x) = f x := fun x =>
    congrArg (fun g => g.hom x) hφ
  let c : A ⟶ R := CommRingCat.ofHom (AddMonoidAlgebra.singleZeroRingHom)
  let v : Spec R ⟶ V.left := Spec.map (e.inv ≫ c) ≫ V.left.isoSpec.inv
  have hv : e.hom ≫ v.appTop = c ≫ (Scheme.ΓSpecIso R).inv := by
    have : V.left.isoSpec.inv.appTop = (Scheme.ΓSpecIso _).inv := by
      rw [← cancel_epi (Scheme.ΓSpecIso Γ(V.left, ⊤)).hom, Iso.hom_inv_id,
        ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop V.left.isoSpec.inv_hom_id
    rw [Scheme.Hom.comp_appTop, this, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hv' : ∀ a : A, v.appTop.hom (e.hom.hom a) =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a) := fun a =>
    congrArg (fun g => g.hom a) hv
  let P : Over S := Over.mk (v ≫ V.hom)
  let v' : P ⟶ V := Over.homMk v rfl
  let t : P ⟶ splitTorus S X := (splitTorusPointsEquiv S X P).symm
    ((Scheme.ΓSpecIso R).inv.hom.toMonoidHom.comp (AddMonoidAlgebra.of A X)).toHomUnits
  have ht : ∀ χ : X, t.left.appTop.hom (charUnit S X χ).val =
      (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1) := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hφv : φ ≫ v = q.left := by
    apply ext_of_isAffine
    rw [← cancel_epi e.hom, Scheme.Hom.comp_appTop, reassoc_of% hv, hφ]
    ext a
    exact hf₁ a
  let φ' : W ⟶ P := Over.homMk φ (by
    change φ ≫ v ≫ V.hom = _
    rw [reassoc_of% hφv, Over.w])
  have h₁ : φ' ≫ v' = q := Over.OverMorphism.ext hφv
  have h₂ : φ' ≫ t = τ := by
    apply (splitTorusPointsEquiv S X W).injective
    ext χ
    change (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X W _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← hf₂, ← hφ', ← ht]
    rfl
  let σ : P ⟶ W := lift t v' ≫ inv (lift τ q)
  have hσ : σ ≫ lift τ q = lift t v' := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hσ₁ : σ ≫ τ = t := by simpa using hσ =≫ fst _ _
  have hσ₂ : σ ≫ q = v' := by simpa using hσ =≫ snd _ _
  have h₃ : φ' ≫ σ = 𝟙 _ := by
    rw [← cancel_mono (lift τ q), Category.assoc, hσ, comp_lift, h₁, h₂, Category.id_comp]
  let σ' : Spec R ⟶ W.left := σ.left
  have h₄ : σ' ≫ φ = 𝟙 _ := by
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso R).inv, Scheme.Hom.comp_appTop, reassoc_of% hφ]
    ext1
    apply AddMonoidAlgebra.ringHom_ext
    · intro a
      change σ'.appTop.hom (f (AddMonoidAlgebra.single 0 a)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single 0 a)
      rw [hf₁, ← hv']
      exact congrArg (fun g : P ⟶ V => g.left.appTop.hom (e.hom.hom a)) hσ₂
    · intro χ
      change σ'.appTop.hom (f (AddMonoidAlgebra.single χ 1)) =
        (Scheme.ΓSpecIso R).inv.hom (AddMonoidAlgebra.single χ 1)
      rw [hf₂, ← ht]
      exact congrArg (fun g : P ⟶ _ => g.left.appTop.hom (charUnit S X χ).val) hσ₁
  have : IsIso φ := ⟨σ', congrArg CommaMorphism.left h₃, h₄⟩
  refine ⟨.of_isIso φ, ?_⟩
  have : IsIso φ.appTop := inferInstanceAs (IsIso (φ.app ⊤))
  have : IsIso F := by rw [← hφ]; infer_instance
  exact ConcreteCategory.bijective_of_isIso F

theorem app_comp_topIso_inv {Y Z : Scheme.{0}} (f : Y ⟶ Z) (V : Z.Opens) :
    f.app V ≫ (f ⁻¹ᵁ V).topIso.inv = V.topIso.inv ≫ (f ∣_ V).appTop := by
  rw [Scheme.Hom.appTop, morphismRestrict_app', Scheme.Opens.topIso_inv, Scheme.Opens.topIso_inv,
    Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.map_appLE _ _ _).symm

theorem cover_of_isPullback {P Y Z W : Scheme.{0}} {a : P ⟶ Y} {b : P ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback a b f g)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) b :=
  ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) h hf.1.1,
    MorphismProperty.of_isPullback (P := @Flat) h hf.1.2⟩,
    MorphismProperty.of_isPullback (P := @QuasiCompact) h hf.2⟩

end TorusTrivial


open TorusTrivial in
theorem isAffineOpen_and_bijective_of_weight_units :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∀ (V : B.left.Opens), IsAffineOpen V → ∀ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, (∀ (χ : X) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom (u (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom (u (Multiplicative.ofAdd χ)).val) → IsAffineOpen (q.left ⁻¹ᵁ V) ∧ Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)) := by
  intro S X _ G B _ _ q i _ _ hfl hsu hqc hk V hV u hu
  let U : G.left.Opens := q.left ⁻¹ᵁ V
  let W : Over S := Over.mk (U.ι ≫ G.hom)
  let V' : Over S := Over.mk (V.ι ≫ B.hom)
  let j : W ⟶ G := Over.homMk U.ι rfl
  let k : V' ⟶ B := Over.homMk V.ι rfl
  let q' : W ⟶ V' := Over.homMk (q.left ∣_ V) (by
    change (q.left ∣_ V) ≫ V.ι ≫ B.hom = U.ι ≫ G.hom
    rw [morphismRestrict_ι_assoc, Over.w])
  have hW₀ : IsPullback U.ι (q.left ∣_ V) q.left V.ι := (isPullback_morphismRestrict q.left V).flip
  have hW : IsPullback j q' q k :=
    IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext hW₀.w) hW₀
  have : Mono j.left := inferInstanceAs (Mono U.ι)
  have : Mono j := Over.mono_of_mono_left j
  let τ : W ⟶ splitTorus S X := (splitTorusPointsEquiv S X W).symm
    ((Units.map U.topIso.inv.hom.toMonoidHom).comp u)
  have hτ₀ : ∀ χ : X, τ.left.appTop.hom (charUnit S X χ).val =
      U.topIso.inv.hom (u (Multiplicative.ofAdd χ)).val := by
    intro χ
    rw [← splitTorusPointsEquiv_val, MulEquiv.apply_symm_apply]
    rfl
  have hle : ∀ {Z : Over S} (g : Z ⟶ W), ⊤ ≤ (g ≫ j).left ⁻¹ᵁ U := by
    intro Z g x _
    exact (g.left x).2
  have hτ₁ : ∀ {Z : Over S} (g : Z ⟶ W) (χ : X), (g ≫ τ).left.appTop.hom (charUnit S X χ).val =
      ((g ≫ j).left.appLE U ⊤ (hle g)).hom (u (Multiplicative.ofAdd χ)).val := by
    intro Z g χ
    let g' : Z.left ⟶ U := g.left
    have h : U.topIso.inv ≫ g'.appTop = (g' ≫ U.ι).appLE U ⊤ (hle g) := by
      rw [← Scheme.Hom.appLE_comp_appLE g' U.ι U ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
      rfl
    change g'.appTop.hom (τ.left.appTop.hom (charUnit S X χ).val) = _
    rw [hτ₀]
    exact congrArg (fun f => f.hom (u (Multiplicative.ofAdd χ)).val) h
  obtain ⟨a, ha⟩ := exists_isPullback q i hk hW τ (by
    intro Z t g g' hg
    apply (splitTorusPointsEquiv S X Z).injective
    rw [map_mul]
    ext χ
    change (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val =
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val *
      (splitTorusPointsEquiv S X Z _ (Multiplicative.ofAdd χ)).val
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, hτ₁, hτ₁,
      TorusInj.appLE_of_eq (congrArg Over.Hom.left hg)]
    exact hu χ Z t (g ≫ j) _ _)
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q'.left :=
    cover_of_isPullback hW₀ ⟨⟨hsu, hfl⟩, hqc⟩
  have hT : IsPullback (snd (splitTorus S X) W) (splitTorus S X ◁ q') q'
      (snd (splitTorus S X) V') := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst)
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have hQ' : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
      (splitTorus S X ◁ q').left :=
    cover_of_isPullback (hT.map (Over.forget S)) hQ
  have : IsIso (lift τ q').left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms Scheme.{0})
      (ha.map (Over.forget S)) hQ' (MorphismProperty.isomorphisms.infer_property _)
  have : IsIso ((Over.forget S).map (lift τ q')) := this
  have : IsIso (lift τ q') := isIso_of_reflects_iso _ (Over.forget S)
  have : IsAffine V'.left := hV
  obtain ⟨h₁, h₂⟩ := isAffine_and_bijective τ q' (A := Γ(B.left, V)) V.topIso.symm
    (U.topIso.inv.hom.comp (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp u) (fun _ _ => Commute.all _ _)))
    (fun a => by
      refine Eq.trans ?_ (congrArg (fun f => f.hom a) (app_comp_topIso_inv q.left V))
      refine congrArg U.topIso.inv.hom ?_
      refine (AddMonoidAlgebra.liftNC_single _ _ 0 a).trans ?_
      exact (congrArg (_ * ·) (((Units.coeHom _).comp u).map_one)).trans (_root_.mul_one _))
    (fun χ => by
      rw [hτ₀]
      simp [AddMonoidAlgebra.liftNCRingHom])
  refine ⟨h₁, ?_⟩
  exact (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso U.topIso.inv) _).mp h₂

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorusLocal

theorem pullback_map_eq_one {S S' : Scheme.{0}} (p : S' ⟶ S) (X : Type) [AddCommGroup X]
    (B : Over S) [GrpObj B] (f : splitTorus S X ⟶ B) (hf : IsMonHom f)
    (h : ∀ g : splitTorus S' X ⟶ (Over.pullback p).obj B, IsMonHom g →
      g = toUnit _ ≫ η[(Over.pullback p).obj B]) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S S' p X
  have h1 : e.hom ≫ (Over.pullback p).map f = 1 := h _ inferInstance
  have h2 : (Over.pullback p).map (1 : splitTorus S X ⟶ B) = 1 := Functor.map_one _
  rw [← cancel_epi e.hom, h1, ← Hom.one_def, h2, MonObj.comp_one]

theorem eq_one_of_isNilpotent_maximalIdeal (A : Type) [CommRing A] [IsLocalRing A]
    (hA : IsNilpotent (IsLocalRing.maximalIdeal A)) (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of A))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  refine splitTorus_hom_eq_one_of_nilpotent A _ hA X B f hf (pullback_map_eq_one _ X B f hf ?_)
  intro g hg
  let : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_field (A ⧸ IsLocalRing.maximalIdeal A) X _ g hg

theorem eq_zero_of_forall_mem_map_pow {A C : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Free A C] (x : C)
    (hx : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A C)) : x = 0 := by
  let b := Module.Free.chooseBasis A C
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top, Ideal.mem_iInf]
  intro n
  have := TorusNil.map_mem_map _ (b.coord i) (hx n)
  rw [Algebra.algebraMap_self, Ideal.map_id] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) this


open TorusNil in
theorem pt_ext_of_quotients {A C : Type} [CommRing A] [CommRing C] [Algebra A C] {N : Type}
    (I : N → Ideal C) (hI : ∀ x, (∀ i, x ∈ I i) → x = 0)
    {B : Over (Spec (CommRingCat.of A))} [IsSeparated B.hom] {a b : sp A C ⟶ B}
    (h : ∀ i, spm (Ideal.Quotient.mkₐ A (I i)) ≫ a = spm (Ideal.Quotient.mkₐ A (I i)) ≫ b) :
    a = b := by
  have : IsAffine (sp A C).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of C)))
  have hinj : Function.Injective (equalizer.ι a b).left.appTop := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hb := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).hom
    apply hb.1
    refine Eq.trans (hI _ fun i => ?_) (map_zero _).symm
    have h1 : (spm (Ideal.Quotient.mkₐ A (I i))).left.appTop x = 0 := by
      rw [← equalizer.lift_ι _ (h i), Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        hx, map_zero]
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I i)))) x
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine h2.symm.trans ?_
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ I i))).hom h1).trans (map_zero _)
  have := IsClosedImmersion.isIso_of_injective_of_isAffine hinj
  apply Over.OverMorphism.ext
  rw [← cancel_epi (equalizer.ι a b).left, ← Over.comp_left, equalizer.condition, Over.comp_left]

end TorusLocal


open TorusNil TorusLocal in
theorem splitTorus_hom_proper_trivial_local (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsProper B.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ B) (hf : IsMonHom f) :
    f = toUnit _ ≫ η[B] := by
  have hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (n + 1)))))).map (toUnit _ ≫ η[B]) := by
    intro n
    set J := IsLocalRing.maximalIdeal A ^ (n + 1) with hJ
    refine pullback_map_eq_one _ X B f hf fun g hg => ?_
    have hJt : J ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
    have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJt
    have : IsLocalRing (A ⧸ J) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    have : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk J)))).obj B).hom :=
      inferInstanceAs (IsProper (pullback.snd _ _))
    refine eq_one_of_isNilpotent_maximalIdeal (A ⧸ J) ⟨n + 1, ?_⟩ X _ g hg
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, ← Ideal.map_pow, ← hJ, Ideal.map_quotient_self]
    rfl
  set t := torusPt A X (AddMonoidAlgebra.of A X) with ht
  have h1 : t ≫ f = t ≫ toUnit _ ≫ η[B] := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A (AddMonoidAlgebra A X)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap A (AddMonoidAlgebra A X ⧸ (IsLocalRing.maximalIdeal A ^ (n + 1)).map
          (algebraMap A (AddMonoidAlgebra A X)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of A X
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory
end

