module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantFunctionsFlatBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.InvFun


open TensorProduct in
theorem alg_inv {R A R' B : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing B] [Algebra R A] [Algebra R R']
    [Algebra R B] [Algebra A B] [Algebra R' B] [IsScalarTower R A B] [IsScalarTower R R' B]
    [Algebra.IsPushout R A R' B] [Module.Flat R A] (hinj : Function.Injective (algebraMap R R'))
    {J : Type} [Finite J] (s : J → (R' →ₐ[R] R')) (hs : ∀ x : R', (∀ i, s i x = x) → x ∈ (algebraMap R R').range)
    (t : J → (B →+* B)) (htA : ∀ i a, t i (algebraMap A B a) = algebraMap A B a)
    (htR : ∀ i r, t i (algebraMap R' B r) = algebraMap R' B (s i r)) :
    Function.Injective (algebraMap A B) ∧ ∀ u : B, (∀ i, t i u = u) → u ∈ Set.range (algebraMap A B) := by
  classical
  cases nonempty_fintype J
  let e := Algebra.IsPushout.equiv R A R' B
  have he : ∀ (a : A) (r : R'), e (a ⊗ₜ r) = algebraMap A B a * algebraMap R' B r := fun a r =>
    Algebra.IsPushout.equiv_tmul R A R' B a r
  have hA : ∀ a : A, algebraMap A B a = e ((Algebra.linearMap R R').lTensor A (a ⊗ₜ 1)) := fun a => by
    simp [he]
  refine ⟨fun a b hab => ?_, fun u hu => ?_⟩
  · rw [hA, hA] at hab
    have h₁ := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R R') hinj (e.injective hab)
    simpa using congrArg (TensorProduct.rid R A) h₁
  · let d : R' →ₗ[R] (J → R') := LinearMap.pi fun i => (s i).toLinearMap - LinearMap.id
    have hex : Function.Exact (Algebra.linearMap R R') d := by
      intro x
      constructor
      · intro hx
        exact hs x fun i => sub_eq_zero.1 (congrFun hx i)
      · rintro ⟨r, rfl⟩
        ext i
        simp [d]
    have hexA := Module.Flat.lTensor_exact A hex
    obtain ⟨w, rfl⟩ := e.surjective u
    have key : ∀ (w : A ⊗[R] R') (i : J), e (TensorProduct.piRight R R A (fun _ : J => R') (d.lTensor A w) i) =
        t i (e w) - e w := by
      intro w i
      induction w with
      | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring
      | tmul a r => simp [d, he, htA, htR, mul_sub, tmul_sub]
    have h0 : d.lTensor A w = 0 := by
      apply (TensorProduct.piRight R R A (fun _ : J => R')).injective
      ext i
      apply e.injective
      rw [key, hu]
      simp
    obtain ⟨v, rfl⟩ := (hexA w).1 h0
    refine ⟨TensorProduct.rid R A v, ?_⟩
    rw [hA]
    congr 2
    exact (TensorProduct.rid R A).symm_apply_apply v

theorem app_comp_appLE {Y Y' : Scheme.{0}} {β : Y' ⟶ Y} {f : Y' ⟶ Y'} (hf : f ≫ β = β) (U : Y.Opens)
    (e : β ⁻¹ᵁ U ≤ f ⁻¹ᵁ (β ⁻¹ᵁ U)) : β.app U ≫ f.appLE (β ⁻¹ᵁ U) (β ⁻¹ᵁ U) e = β.app U := by
  refine (Scheme.Hom.comp_appLE f β U (β ⁻¹ᵁ U) e).symm.trans ?_
  rw [← Scheme.Hom.appLE_eq_app]
  simp only [hf]

theorem const_comp_appLE {R : CommRingCat.{0}} {Y : Scheme.{0}} {y : Y ⟶ Spec R} {f : Y ⟶ Y} {s : R ⟶ R}
    (hf : f ≫ y = y ≫ Spec.map s) (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ U) :
    ((Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top) ≫ f.appLE U U e =
      s ≫ (Scheme.ΓSpecIso R).inv ≫ y.appLE ⊤ U le_top := by
  have e₁ : y.appLE ⊤ U le_top ≫ f.appLE U U e = (Spec.map s).appTop ≫ y.appLE ⊤ U le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f y ⊤ U U le_top e).trans ?_
    simp only [hf]
    exact Scheme.Hom.comp_appLE y (Spec.map s) ⊤ U le_top
  rw [Category.assoc, e₁, Scheme.ΓSpecIso_inv_naturality_assoc]

theorem affine_inv {R R' : Type} [CommRing R] [CommRing R'] (ρ : R →+* R') (hρ : Function.Injective ρ) (hG : IsGal ρ)
    {Y Y' : Scheme.{0}} {y : Y ⟶ Sp R} {y' : Y' ⟶ Sp R'} {β : Y' ⟶ Y} [Flat y] (h : IsPullback β y' y (spMap ρ))
    (act : Gal ρ → (Y' ⟶ Y')) (hβ : ∀ σ, act σ ≫ β = β) (hy : ∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Injective (β.app U).hom ∧ ∀ u : Γ(Y', β ⁻¹ᵁ U),
      (∀ σ (h : β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U)), ((act σ).appLE _ _ h).hom u = u) → u ∈ Set.range (β.app U).hom := by
  have hp := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := β ⁻¹ᵁ U)
    le_top le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen h _ _ _
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hp' : IsPushout ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top)
      (CommRingCat.ofHom ρ) (β.app U)
      ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top) := by
    refine hp.of_iso (Scheme.ΓSpecIso _) (.refl _) (Scheme.ΓSpecIso _) (.refl _) (by simp) ?_
      (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    exact Scheme.ΓSpecIso_naturality _
  have hfl : ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
      (y.flat_appLE (isAffineOpen_top _) hU le_top)
  have hle : ∀ σ, β ⁻¹ᵁ U ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ U) := fun σ => by
    rw [← Scheme.Hom.comp_preimage, hβ]
  algebraize [ρ, ((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top).hom,
    (β.app U).hom,
    ((Scheme.ΓSpecIso (.of R')).inv ≫ y'.appLE ⊤ (β ⁻¹ᵁ U) le_top).hom,
    (((Scheme.ΓSpecIso (.of R)).inv ≫ y.appLE ⊤ U le_top) ≫ β.app U).hom]
  have : IsScalarTower R Γ(Y, U) Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R R' Γ(Y', β ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(hp'.w).hom)
  have : Algebra.IsPushout R Γ(Y, U) R' Γ(Y', β ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp hp'
  have := hG.1
  have H := alg_inv (R := R) (A := Γ(Y, U)) (R' := R') (B := Γ(Y', β ⁻¹ᵁ U)) hρ
    (fun σ : Gal ρ => (⟨Gal.hom σ, σ.2⟩ : R' →ₐ[R] R')) (fun x hx => hG.2 x fun σ hσ => hx ⟨σ, hσ⟩)
    (fun σ => ((act σ).appLE _ _ (hle σ)).hom) ?_ ?_
  · exact ⟨H.1, fun u hu => H.2 u fun σ => hu σ _⟩
  · intro σ a
    exact congr($(app_comp_appLE (hβ σ) U (hle σ)).hom a)
  · intro σ r
    exact congr($(const_comp_appLE (hy σ) (β ⁻¹ᵁ U) (hle σ)).hom r)

theorem app_res {Y Y' : Scheme.{0}} (β : Y' ⟶ Y) {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)) :
    (β.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom ((β.app V).hom a) :=
  congr($(β.naturality (homOfLE e).op).hom a)

theorem res_res {Y : Scheme.{0}} {U V W : Y.Opens} (e : U ≤ V) (e' : V ≤ W) (a : Γ(Y, W)) :
    (Y.presheaf.map (homOfLE e).op).hom ((Y.presheaf.map (homOfLE e').op).hom a) =
      (Y.presheaf.map (homOfLE (e.trans e')).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem le_iSup_affine {Y : Scheme.{0}} (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUV⟩, hxU⟩

theorem injective_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, IsAffineOpen U → Function.Injective (β.app U).hom) (V : Y.Opens) :
    Function.Injective (β.app V).hom := by
  intro a b hab
  refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a b fun U => H U.1 U.2.1 ?_
  exact (app_res β U.2.2 a).trans ((congrArg _ hab).trans (app_res β U.2.2 b).symm)

theorem mem_range_of_affine {Y Y' : Scheme.{0}} (β : Y' ⟶ Y)
    (H : ∀ U : Y.Opens, Function.Injective (β.app U).hom) (V : Y.Opens) (u : Γ(Y', β ⁻¹ᵁ V))
    (hu : ∀ (U : Y.Opens) (_ : IsAffineOpen U) (e : U ≤ V),
      (Y'.presheaf.map (homOfLE (β.preimage_mono e)).op).hom u ∈ Set.range (β.app U).hom) :
    u ∈ Set.range (β.app V).hom := by
  choose a ha using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => hu U.1 U.2.1 U.2.2
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => U.1) V
    (fun U => homOfLE U.2.2) (le_iSup_affine V) a (fun i j => H (i.1 ⊓ j.1) (by
      refine (app_res β inf_le_left (a i)).trans (Eq.trans ?_ (app_res β inf_le_right (a j)).symm)
      rw [ha, ha, res_res, res_res]))
  refine ⟨s, Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ V} => β ⁻¹ᵁ U.1) (β ⁻¹ᵁ V)
    (fun U => homOfLE (β.preimage_mono U.2.2)) ?_ _ _ fun U => ?_⟩
  · rw [← β.preimage_iSup]
    exact β.preimage_mono (le_iSup_affine V)
  · exact (app_res β U.2.2 s).symm.trans ((congrArg _ (hs U)).trans (ha U))

theorem invariant_functions : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R']
    (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (Y Y' : Scheme.{0}) (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (β : Y' ⟶ Y), Flat y →
    IsPullback β y' y (spMap ρ) → ∀ (act : Gal ρ → (Y' ⟶ Y')), (∀ σ, act σ ≫ β = β) →
    (∀ σ, act σ ≫ y' = y' ≫ spMap (Gal.hom σ)) → ∀ V : Y.Opens, Function.Injective (β.app V).hom ∧
    ∀ u : Γ(Y', β ⁻¹ᵁ V), (∀ σ (h : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V)), ((act σ).appLE _ _ h).hom u = u) →
      u ∈ Set.range (β.app V).hom := by
  intro R _ _ R' _ _ _ ρ hF hG Y Y' y y' β _ h act hβ hy V
  have H := fun (U : Y.Opens) (hU : IsAffineOpen U) => affine_inv ρ hF.2.1 hG h act hβ hy hU
  have hinj := injective_of_affine β fun U hU => (H U hU).1
  refine ⟨hinj V, fun u hu => mem_range_of_affine β hinj V u fun U hU e => (H U hU).2 _ fun σ hσ => ?_⟩
  have hle : β ⁻¹ᵁ V ≤ act σ ⁻¹ᵁ (β ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, hβ]
  have e₁ : Y'.presheaf.map (homOfLE (β.preimage_mono e)).op ≫ (act σ).appLE _ _ hσ =
      (act σ).appLE _ _ hle ≫ Y'.presheaf.map (homOfLE (β.preimage_mono e)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  exact (congr($(e₁).hom u)).trans (congrArg _ (hu σ hle))

end GlobalTheory.Mum.InvFun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisQuotientAffineOpenSpecInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem quot_affine_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  intro R _ _ _ R' _ _ _ _ _ _ _ G' act hact h1 hmul H hH X π hπ hAff hinv _ hsec V hV
  haveI := hAff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  let r : Gal (algebraMap R R') → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hrπ : ∀ σ, r σ ≫ π = π := hinv
  have hr : ∀ σ, π ⁻¹ᵁ V ≤ (r σ) ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ x hx => by
    show x ∈ (r σ ≫ π) ⁻¹ᵁ V
    rw [hrπ σ]; exact hx
  have hrι : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  let a : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ⟶ Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => (r σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hr σ)
  have key0 : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec = hU.fromSpec ≫ r σ := fun σ =>
    IsAffineOpen.SpecMap_appLE_fromSpec (r σ) hU hU (hr σ)
  have key : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι = hU.fromSpec ≫ H.ι ≫ act σ := fun σ => by
    rw [← Category.assoc, key0, Category.assoc, hrι]
  have key_assoc : ∀ σ {Z : Scheme.{0}} (g : G'.left ⟶ Z),
      Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι ≫ g = hU.fromSpec ≫ H.ι ≫ act σ ≫ g := fun σ Z g => by
    simpa only [Category.assoc] using congrArg (· ≫ g) (key σ)
  have a_one : a 1 = 𝟙 _ := by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, h1, Spec.map_id]
    simp
  have a_mul : ∀ σ τ, a (σ * τ) = a τ ≫ a σ := fun σ τ => by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, hmul, Spec.map_comp]
    simp only [Category.assoc, key, key_assoc]
  have a_one' : ∀ x, (a 1).hom x = x := fun x => by rw [a_one]; rfl
  have a_mul' : ∀ σ τ x, (a (σ * τ)).hom x = (a σ).hom ((a τ).hom x) := fun σ τ x => by
    rw [a_mul]; rfl
  obtain ⟨φ', hφ'⟩ : ∃ φ' : CommRingCat.of R' ⟶ Γ(H.toScheme, π ⁻¹ᵁ V),
      Spec.map φ' = hU.fromSpec ≫ H.ι ≫ G'.hom := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have semi : ∀ σ, φ' ≫ a σ = CommRingCat.ofHom (Gal.hom σ) ≫ φ' := fun σ => by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hφ', key_assoc, hact]
    simp only [Category.assoc]
  have semi' : ∀ σ y, (a σ).hom (φ'.hom y) = φ'.hom (σ.1 y) := fun σ y =>
    congrArg (fun f => f.hom y) (semi σ)
  letI alg' : Algebra R' Γ(H.toScheme, π ⁻¹ᵁ V) := φ'.hom.toAlgebra
  letI algR : Algebra R Γ(H.toScheme, π ⁻¹ᵁ V) := (φ'.hom.comp (algebraMap R R')).toAlgebra
  haveI tow : IsScalarTower R R' Γ(H.toScheme, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fixR : ∀ σ r, (a σ).hom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r) = algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r :=
    fun σ r => by
      show (a σ).hom (φ'.hom (algebraMap R R' r)) = φ'.hom (algebraMap R R' r)
      rw [semi' σ]
      exact congrArg φ'.hom ((show ∀ r, σ.1 (algebraMap R R' r) = algebraMap R R' r from σ.2) r)
  let ah : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => { (a σ).hom with commutes' := fixR σ }
  have inv1 : ∀ σ x, (a σ).hom ((a σ⁻¹).hom x) = x := fun σ x => by
    rw [← a_mul', mul_inv_cancel, a_one']
  have inv2 : ∀ σ x, (a σ⁻¹).hom ((a σ).hom x) = x := fun σ x => by
    rw [← a_mul', inv_mul_cancel, a_one']
  let actE : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) := fun σ =>
    AlgEquiv.ofAlgHom (ah σ) (ah σ⁻¹) (AlgHom.ext fun x => inv1 σ x) (AlgHom.ext fun x => inv2 σ x)
  let actC : Gal (algebraMap R R') →* (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    { toFun := actE
      map_one' := AlgEquiv.ext fun x => a_one' x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => a_mul' σ τ x }
  have actC_apply : ∀ σ x, actC σ x = (a σ).hom x := fun _ _ => rfl
  let C : Subalgebra R Γ(H.toScheme, π ⁻¹ᵁ V) :=
    ⨅ σ, AlgHom.equalizer (actC σ : Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) (AlgHom.id R _)
  have memC : ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := fun x =>
    Algebra.mem_iInf.trans (forall_congr' fun σ => Iff.rfl)
  have happ : Spec.map (π.app V) ≫ hV.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE]; exact IsAffineOpen.SpecMap_appLE_fromSpec π hV hU le_rfl
  have hmem : ∀ g, (π.app V).hom g ∈ C := by
    intro g; rw [memC]; intro σ
    have e : π.app V ≫ a σ = π.app V := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp]
      simp only [Category.assoc]
      rw [happ, ← Category.assoc, key0, Category.assoc, hrπ]
    exact congrArg (fun f => f.hom g) e
  let ψ : Γ(X.left, V) →+* C := (π.app V).hom.codRestrict C hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => (hsec V).1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx⟩ := (hsec V).2 y (fun σ _ => (memC y).1 hy σ)
    exact ⟨x, Subtype.ext hx⟩
  let eψ := RingEquiv.ofBijective ψ hbij
  let l : Sp C ⟶ X.left := Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
  have hlr : l.opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]
  have sq : hU.fromSpec ≫ π = spMap (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) ≫ l := by
    rw [← happ]
    show _ = _ ≫ Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hj : hU.fromSpec ≫ H.ι ≫ G'.hom = spMap (algebraMap R' Γ(H.toScheme, π ⁻¹ᵁ V)) := by
    rw [← hφ']; rfl
  have hl : l ≫ X.hom = spMap (algebraMap R C) := by
    obtain ⟨m, hm⟩ : ∃ m : CommRingCat.of R ⟶ CommRingCat.of C, Spec.map m = l ≫ X.hom :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    rw [← hm]
    have e : m ≫ CommRingCat.ofHom (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) =
        CommRingCat.ofHom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V)) := by
      rw [← Spec.map_inj, Spec.map_comp, hm, ← Category.assoc, ← sq, Category.assoc, hπ]
      have h2 := congrArg (· ≫ spMap (algebraMap R R')) hj
      simp only [Category.assoc] at h2
      rw [h2, ← Spec.map_comp]
      rfl
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) e
  refine ⟨Γ(H.toScheme, π ⁻¹ᵁ V), inferInstance, algR, alg', tow, actC, C, hU.fromSpec, l, inferInstance,
    inferInstance, ?_, ?_, hj, hl, ?_, ?_, memC⟩
  · exact congrArg (fun U : X.left.Opens => (U : Set X.left)) hlr
  · refine (IsOpenImmersion.isPullback _ _ _ _ sq ?_).flip
    rw [hlr, IsAffineOpen.opensRange_fromSpec]
  · intro σ
    exact key σ
  · intro σ y
    exact semi' σ y

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointLogKodairaSpencerFrameChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed (Xo := Xo) (c := c) → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) →
    ∃ (n n' : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
      (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) (X₀ TF.Y Z).functionField),
      (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
        ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := (X₀ TF.Y Z).functionField) e' (ε' k)) ∧
      (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j, D j = ∑ k, L k j • D' k) := by
  first | exact @GlobalTheory.LogKSDiv.GenChange.genKS_change | exact GlobalTheory.LogKSDiv.GenChange.genKS_change | (intros; apply GlobalTheory.LogKSDiv.GenChange.genKS_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatching
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem genLam_pull_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (βW₂ : (G2 GW).left ⟶ (G2 G).left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → Geo.Tor.IsSquare βW βW₂ → LBIso (abelian₂ GW UW.LG.L) (PP.pull βW₂) → ∃ (ga : FractionRing R →+* FractionRing W) (α : AW.A.left ⟶ A.A.left) (α₂ : (G2 AW.A).left ⟶ (G2 A.A).left), (∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r)) ∧ IsGrpPullback AW.A A.A (spMap ga) α ∧ Geo.Tor.IsSquare α α₂ ∧ LBIso (abelian₂ AW.A AW.L) ((abelian₂ A.A A.L).pull α₂) ∧ UW.gen.inv.left ≫ pullback.fst GW.hom (jK W) ≫ βW = α ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hExt W _ _ _ φ GW _ _ βW βW₂ DW AW UW hW hφ hφl hβ hsqW hPP
  let ga : FractionRing R →+* FractionRing W := IsFractionRing.map (K := FractionRing R) (L := FractionRing W) hφ
  have hga : ∀ r, ga (algebraMap R _ r) = algebraMap W _ (φ r) := fun r => by
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [ga, IsFractionRing.map, IsLocalization.map_eq]
  let κW : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R) :=
    pullback.lift (pullback.fst _ _ ≫ βW) (pullback.snd _ _ ≫ spMap ga) (by
      rw [Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition, Category.assoc, hsq, Category.assoc])
  have hκf : κW ≫ pullback.fst G.hom (jK R) = pullback.fst GW.hom (jK W) ≫ βW := pullback.lift_fst _ _ _
  have w : κW ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK W)).obj GW).hom ≫ spMap ga :=
    pullback.lift_snd _ _ _
  have hκ : IsGrpPullback ((Over.pullback (jK W)).obj GW) ((Over.pullback (jK R)).obj G) (spMap ga) κW :=
    (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback GW (jK W)).comp hβ).congr hsq hκf.symm) w
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK W)).obj GW) := Functor.isCommMonObj_obj
  have : IsMonHom UW.gen.hom := UW.gen_hom
  have : IsMonHom gen.hom := hgen
  have : IsMonHom UW.gen.symm.hom := show IsMonHom UW.gen.inv by infer_instance
  have hu : IsGrpPullback AW.A ((Over.pullback (jK W)).obj GW) (𝟙 _) UW.gen.inv.left :=
    isGrpPullback_of_iso UW.gen.symm
  have hg : IsGrpPullback ((Over.pullback (jK R)).obj G) A.A (𝟙 _) gen.hom.left := isGrpPullback_of_iso gen
  have hα : IsGrpPullback AW.A A.A (spMap ga) (UW.gen.inv.left ≫ κW ≫ gen.hom.left) :=
    (hu.comp (hκ.comp hg)).congr (by simp) rfl
  obtain ⟨u₂, squ, Hu⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hu
  obtain ⟨κ₂, sqκ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hκ
  obtain ⟨g₂, sqg, Hg⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ hg
  obtain ⟨fW₂, sqfW, HfW⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback GW (jK W))
  obtain ⟨fR₂, sqfR, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ _ _ _ (isGrpPullback_pullback G (jK R))
  have hLA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  have hLG : (UW.LG.L.pull (pullback.fst GW.hom (jK W))).IsLB := pull_isLB UW.LG.isLB _
  have hAg : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _

  have Z : LBIso (abelian₂ ((Over.pullback (jK R)).obj G) (A.L.pull gen.hom.left)) ((abelian₂ A.A A.L).pull g₂) := by
    have h := Hg A.L (A.L.pull gen.hom.left) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hAg hLA
      (PolBaseChange.lbIso_refl hAg)
      (LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl hLA))
    rwa [Category.comp_id] at h
  have Y : LBIso (PP.pull fR₂) ((abelian₂ A.A A.L).pull g₂) :=
    LBIso.trans (pull_isLB hExt.1 _) (DVR.linComb_isLB _ hAg _ _) (pull_isLB hLA _) (hExt.2 fR₂ sqfR).symm Z
  have e : fW₂ ≫ βW₂ = κ₂ ≫ fR₂ := by
    apply pullback.hom_ext
    · show (fW₂ ≫ βW₂) ≫ (fst G G).left = (κ₂ ≫ fR₂) ≫ (fst G G).left
      simp only [Category.assoc, hsqW.1, sqfR.1]
      rw [← Category.assoc fW₂, sqfW.1, reassoc_of% sqκ.1, hκf, Category.assoc]
    · show (fW₂ ≫ βW₂) ≫ (snd G G).left = (κ₂ ≫ fR₂) ≫ (snd G G).left
      simp only [Category.assoc, hsqW.2, sqfR.2]
      rw [← Category.assoc fW₂, sqfW.2, reassoc_of% sqκ.2, hκf, Category.assoc]
  have B1 : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      (PP.pull (κ₂ ≫ fR₂)) := by
    have h := HfW UW.LG.L (UW.LG.L.pull (pullback.fst GW.hom (jK W))) _ PP βW₂ UW.LG.isLB hLG hExt.1
      (PolBaseChange.lbIso_refl hLG) hPP
    rwa [e] at h
  have B3 : LBIso (PP.pull (κ₂ ≫ fR₂)) ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.chartPull (chartPullSame PP _ (fun _ => fR₂) _ κ₂ fun _ => rfl)
      (chartPullSame (abelian₂ A.A A.L) _ (fun _ => g₂) _ κ₂ fun _ => rfl) Y
  have hLamW : LBIso (abelian₂ ((Over.pullback (jK W)).obj GW) (UW.LG.L.pull (pullback.fst GW.hom (jK W))))
      ((abelian₂ A.A A.L).pull (κ₂ ≫ g₂)) :=
    LBIso.trans (DVR.linComb_isLB _ hLG _ _) (pull_isLB hExt.1 _) (pull_isLB hLA _) B1 B3

  have hN : LBIso AW.L ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) := by
    have hext : LBIso (AW.L.pull UW.gen.hom.left) (UW.LG.L.pull (pullback.fst GW.hom (jK W))) := UW.ext
    have h1 : LBIso (AW.L.pull (𝟙 _)) ((UW.LG.L.pull (pullback.fst GW.hom (jK W))).pull UW.gen.inv.left) :=
      LBIso.chartPull (chartPullSame AW.L _ (fun _ => UW.gen.hom.left) _ UW.gen.inv.left fun _ => by
          rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left])
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) hext
    have h0 : LBIso AW.L (AW.L.pull (𝟙 _)) :=
      LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) (PolBaseChange.lbIso_refl AW.isLB)
    exact LBIso.trans AW.isLB (pull_isLB AW.isLB _) (pull_isLB hLG _) h0 h1
  refine ⟨ga, UW.gen.inv.left ≫ κW ≫ gen.hom.left, u₂ ≫ κ₂ ≫ g₂, hga, hα, ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Category.assoc, sqg.1, reassoc_of% sqκ.1, reassoc_of% squ.1]
  · simp only [Category.assoc, sqg.2, reassoc_of% sqκ.2, reassoc_of% squ.2]
  · exact Hu _ AW.L _ (abelian₂ A.A A.L) (κ₂ ≫ g₂) hLG AW.isLB hLA hN hLamW
  · rw [Category.assoc, Category.assoc, ← Category.assoc gen.hom.left, ← Over.comp_left, Iso.hom_inv_id,
      Over.id_left, Category.id_comp, hκf]

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedOfIsPullbackSurjectiveLft
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geometricallyConnected_of_isPullback_of_surjective :
    ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π →
    ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π →
    GeometricallyConnected G'.hom → GeometricallyConnected G.hom := by
  intro R _ S π hlft hsurj G' G β hpb hG'
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  let jK : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨t, ht⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (Ω := AlgebraicClosure K) π (jK ≫ y)
  have hct : ConnectedSpace ↥(pullback G'.hom t) :=
    pullback_of_geometrically hG'.geometrically_connectedSpace _ t
  have hP : IsPullback (pullback.fst G'.hom t ≫ β) (pullback.snd G'.hom t) G.hom (t ≫ π) :=
    (IsPullback.of_hasPullback G'.hom t).paste_horiz hpb
  rw [← ht] at hP
  have hc' : ConnectedSpace ↥(pullback G.hom (jK ≫ y)) :=
    hP.isoPullback.hom.homeomorph.connectedSpace_iff.mp hct
  have hjK : Surjective jK := ⟨fun z ↦ by
    obtain ⟨w⟩ : Nonempty ↥(Spec (.of (AlgebraicClosure K))) := inferInstance
    exact ⟨w, Subsingleton.elim _ _⟩⟩
  have hc'' : ConnectedSpace ↥(pullback (pullback.snd G.hom y) jK) :=
    (pullbackLeftPullbackSndIso G.hom y jK).hom.homeomorph.connectedSpace_iff.mpr hc'
  exact (pullback.fst (pullback.snd G.hom y) jK).surjective.connectedSpace
    (pullback.fst (pullback.snd G.hom y) jK).continuous

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentityStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (exact GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (intros; apply GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull  <;> assumption)
end

