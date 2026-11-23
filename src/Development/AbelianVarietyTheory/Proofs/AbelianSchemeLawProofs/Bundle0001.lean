module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pullback_comp_iso_monHom {T S' S : Scheme.{0}} (f : S' ⟶ S) (g : S ⟶ T) (h : S' ⟶ T)
    (hh : h = f ≫ g) (G : Over T) [GrpObj G] :
    ∃ e : (Over.pullback h).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G),
      IsMonHom e.hom ∧
        e.hom.left ≫ pullback.fst ((Over.pullback g).obj G).hom f ≫ pullback.fst G.hom g =
          pullback.fst G.hom h := by
  subst hh
  let m : (Over.pullback (f ≫ g)).mapMon.obj (Mon.mk G) ≅
      (Over.pullback f).mapMon.obj ((Over.pullback g).mapMon.obj (Mon.mk G)) :=
    (Functor.mapMonNatIso (Over.pullbackComp f g) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
  refine ⟨(Mon.forget _).mapIso m, ?_, ?_⟩
  · show IsMonHom m.hom.hom
    infer_instance
  · change (((Over.pullbackComp f g).hom.app G).left ≫ 𝟙 _) ≫ pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem charUnit_val_eq_appTop (S : Scheme.{0}) (X : Type) [AddCommGroup X] (χ : X) :
    (charUnit S X χ).val = (pullback.fst (splitTorusAff ZU X).hom (toZ S)).appTop.hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (AddMonoidAlgebra.single χ 1)) := by
  have h : ∀ (Y : Scheme.{0}) (i : (⊤ : Y.Opens) ⟶ ⊤) (a : Γ(Y, ⊤)),
      (Y.presheaf.map i.op).hom a = a := fun Y i a => by
    rw [Subsingleton.elim i (𝟙 _), op_id, Y.presheaf.map_id]
    rfl
  exact h _ _ _

theorem splitTorus_baseChange (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    ∃ e : splitTorus S' X ≅ (Over.pullback f).obj (splitTorus S X), IsMonHom e.hom ∧
      ∀ χ : X, (e.hom.left ≫ pullback.fst (splitTorus S X).hom f).appTop.hom (charUnit S X χ).val =
        (charUnit S' X χ).val := by
  obtain ⟨e, he, hf⟩ := exists_pullback_comp_iso_monHom f (toZ S) (toZ S')
    (specULiftZIsTerminal.hom_ext _ _) (splitTorusAff ZU X)
  refine ⟨e, he, fun χ => ?_⟩
  rw [charUnit_val_eq_appTop, charUnit_val_eq_appTop, ← hf, ← Category.assoc]
  simp only [Scheme.Hom.comp_appTop]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SplitTorusPoints

open Rosenlicht

theorem ΓSpecIso_inv_comp_specMap {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}

theorem map_left_fst {T : Scheme.{0}} (f : S ⟶ T) {A B : Over T} (g : A ⟶ B) :
    ((Over.pullback f).map g).left ≫ pullback.fst B.hom f = pullback.fst A.hom f ≫ g.left :=
  pullback.lift_fst _ _ _

theorem exists_mul_factor (a b : Z ⟶ splitTorus S X) :
    ∃ q : Z.left ⟶ (splitTorusAff ZU X ⊗ splitTorusAff ZU X).left,
      q ≫ (fst _ _ : _ ⟶ splitTorusAff ZU X).left = a.left ≫ torusFst S X ∧
      q ≫ (snd _ _ : _ ⟶ splitTorusAff ZU X).left = b.left ≫ torusFst S X ∧
      q ≫ μ[splitTorusAff ZU X].left = (a * b).left ≫ torusFst S X := by
  let F := Over.pullback (toZ S)
  let G := splitTorusAff ZU X
  let m : Z ⟶ F.obj (G ⊗ G) := lift (a : Z ⟶ F.obj G) (b : Z ⟶ F.obj G) ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom (toZ S)) ≫ g.left =
      (m ≫ F.map g).left ≫ torusFst S X := by
    intro g
    rw [Category.assoc, ← map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  refine ⟨m.left ≫ pullback.fst (G ⊗ G).hom (toZ S), ?_, ?_, ?_⟩
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  · rw [key]
    congr 2
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  · rw [key]
    congr 2

theorem coord_mul_single (a b : Z ⟶ splitTorus S X) (x : X) :
    (coord (a * b)).hom (AddMonoidAlgebra.single x 1) =
      (coord a).hom (AddMonoidAlgebra.single x 1) * (coord b).hom (AddMonoidAlgebra.single x 1) := by
  obtain ⟨q, h1, h2, h3⟩ := exists_mul_factor a b
  let A := torusRing ZU X
  let p : Z.left ⟶ Spec (.of (A ⊗[ZU.{0}] A)) := q ≫ (pullbackSpecIso ZU.{0} A A).hom
  let φ := (Scheme.ΓSpecIso (.of (A ⊗[ZU.{0}] A))).inv ≫ p.appTop
  have e1 : coord a = CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h1]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e2 : coord b = CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[ZU.{0}] A ⊗[ZU.{0}] A).toRingHom ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h2]
    congr 2
    exact (congrArg (q ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A).symm).trans
      (Category.assoc _ _ _).symm
  have e3 : coord (a * b) = CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A) ≫ φ := by
    rw [← ΓSpecIso_inv_comp_specMap, coord, ← h3]
    congr 2
  rw [e1, e2, e3]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← map_mul]
  congr 1
  change Coalgebra.comul (R := ULift.{0} ℤ) (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ)) =
    (AddMonoidAlgebra.single x (1 : ULift.{0} ℤ) ⊗ₜ[ULift.{0} ℤ] (1 : AddMonoidAlgebra (ULift.{0} ℤ) X)) *
    ((1 : AddMonoidAlgebra (ULift.{0} ℤ) X) ⊗ₜ[ULift.{0} ℤ] AddMonoidAlgebra.single x (1 : ULift.{0} ℤ))
  simp

theorem coord_single (t : Z ⟶ splitTorus S X) (x : X) :
    (coord t).hom (AddMonoidAlgebra.single x 1) = t.left.appTop.hom (charUnit S X x).val := by
  rw [TorusInj.charUnit_val, coord, Scheme.Hom.comp_appTop]
  have : (TorusInj.tFst (S := S) X).appLE ⊤ ⊤ (TorusInj.tle _) = (torusFst S X).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [this]
  rfl

noncomputable def toHom (t : Z ⟶ splitTorus S X) : Multiplicative X →* Γ(Z.left, ⊤)ˣ :=
  ((coord t).hom.toMonoidHom.comp (AddMonoidAlgebra.of (ULift.{0} ℤ) X)).toHomUnits

theorem toHom_val (t : Z ⟶ splitTorus S X) (x : X) :
    (toHom t (Multiplicative.ofAdd x)).val = (coord t).hom (AddMonoidAlgebra.single x 1) := rfl

theorem exists_coord_eq (φ : torusRing ZU X ⟶ Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, coord t = φ := by
  refine ⟨Over.homMk (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), ?_⟩
  have : (pullback.lift (Z.left.toSpecΓ ≫ Spec.map φ) Z.hom
    (specULiftZIsTerminal.hom_ext _ _) : Z.left ⟶ (splitTorus S X).left) ≫ torusFst S X =
      Z.left.toSpecΓ ≫ Spec.map φ := pullback.lift_fst _ _ _
  refine (congrArg (fun g => (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ Scheme.Hom.appTop g)
    this).trans ?_
  rw [ΓSpecIso_inv_comp_specMap, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id, Category.comp_id]

theorem toHom_bijective : Function.Bijective (toHom : (Z ⟶ splitTorus S X) → _) := by
  constructor
  · intro a b h
    apply coord_injective
    ext1
    refine ringHom_ext_ZU fun y => ?_
    rw [← toHom_val, ← toHom_val, h]
  · intro u
    letI : Algebra (ULift.{0} ℤ) Γ(Z.left, ⊤) := ULift.algebra' ℤ _
    obtain ⟨t, ht⟩ := exists_coord_eq (Z := Z) (X := X) (CommRingCat.ofHom
      (AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)).toRingHom)
    refine ⟨t, ?_⟩
    ext x
    change (toHom t (Multiplicative.ofAdd x)).val = _
    rw [toHom_val, ht]
    change AddMonoidAlgebra.lift (ULift.{0} ℤ) Γ(Z.left, ⊤) X ((Units.coeHom _).comp u)
      (AddMonoidAlgebra.single _ 1) = _
    simp

theorem toHom_mul (a b : Z ⟶ splitTorus S X) : toHom (a * b) = toHom a * toHom b := by
  ext x
  exact coord_mul_single a b x

end SplitTorusPoints

noncomputable def splitTorusPointsEquiv (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S) :
    (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ) :=
  { Equiv.ofBijective _ SplitTorusPoints.toHom_bijective with
    map_mul' := SplitTorusPoints.toHom_mul }

theorem splitTorusPointsEquiv_val (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S)
    (t : Z ⟶ splitTorus S X) (χ : X) :
    (splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ)).val =
      t.left.appTop.hom (charUnit S X χ).val :=
  SplitTorusPoints.coord_single t χ

theorem exists_splitTorus_points_mulEquiv :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val :=
  fun S X _ Z => ⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FlatQuotient

variable {S : Scheme.{0}}


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
lemma _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective {X Y : Over S} (f : X ⟶ Y) [Flat f.left] [Surjective f.left] :
    Epi f := by
  have hepi : Epi f.left := Flat.epi_of_flat_of_surjective f.left
  exact (Over.forget S).epi_of_epi_map hepi

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerRight_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (f : X ⟶ Y) (Z : Over S) (hf : P f.left) :
    P (f ▷ Z).left := by
  have e1 : (f ▷ Z).left ≫ pullback.snd Y.hom Z.hom = pullback.snd X.hom Z.hom := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have e2 : (f ▷ Z).left ≫ pullback.fst Y.hom Z.hom = pullback.fst X.hom Z.hom ≫ f.left := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have houter : IsPullback ((f ▷ Z).left ≫ pullback.snd Y.hom Z.hom) (pullback.fst X.hom Z.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact (IsPullback.of_hasPullback X.hom Z.hom).flip
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Y.hom Z.hom).flip).flip hf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerLeft_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (Z : Over S) (f : X ⟶ Y) (hf : P f.left) :
    P (Z ◁ f).left := by
  have e1 : (Z ◁ f).left ≫ pullback.fst Z.hom Y.hom = pullback.fst Z.hom X.hom := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have e2 : (Z ◁ f).left ≫ pullback.snd Z.hom Y.hom = pullback.snd Z.hom X.hom ≫ f.left := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have houter : IsPullback ((Z ◁ f).left ≫ pullback.fst Z.hom Y.hom) (pullback.snd Z.hom X.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact IsPullback.of_hasPullback Z.hom X.hom
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Z.hom Y.hom)).flip hf


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
lemma _root_.GlobalTheory.FlatQuotient.epi_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hf' : Surjective f.left] [hg : Flat g.left] [hg' : Surjective g.left] :
    Epi (f ⊗ₘ g) := by
  have h₁ : Flat (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Flat f X' hf
  have h₂ : Surjective (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Surjective f X' hf'
  have h₃ : Flat (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Flat Y g hg
  have h₄ : Surjective (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Surjective Y g hg'
  have e₁ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (f ▷ X')
  have e₂ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (Y ◁ g)
  rw [MonoidalCategory.tensorHom_def]
  exact epi_comp _ _


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
lemma _root_.GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel {G B B' T : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B'])
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by
  have hk : (g * g'⁻¹) ≫ q = toUnit Z ≫ η[B] := by
    rw [mul_comp, GrpObj.inv_comp, h, mul_inv_cancel, Hom.one_def]
  have hl : hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ i = g * g'⁻¹ := hker.lift_fst _ _ _
  have hone : (g * g'⁻¹) ≫ f = 1 := by
    rw [← hl, Category.assoc, hf, Hom.one_def, ← Category.assoc, toUnit_unique
      (hker.lift (g * g'⁻¹) (toUnit Z) hk ≫ toUnit T) (toUnit Z)]
  rw [mul_comp, GrpObj.inv_comp, mul_inv_eq_one] at hone
  exact hone


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.FlatQuotient.exists_desc {G B B' T : Over S} [GrpObj G]
    [GrpObj B] [GrpObj B'] (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B']) :
    ∃ β : B ⟶ B', IsMonHom β ∧ q ≫ β = f := by
  have hcomp : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ G.left), g₁ ≫ q.left = g₂ ≫ q.left →
      g₁ ≫ f.left = g₂ ≫ f.left := by
    intro Z g₁ g₂ h
    have hw : g₂ ≫ G.hom = g₁ ≫ G.hom := by
      rw [← Over.w q, ← Category.assoc, ← h, Category.assoc]
    have key := _root_.GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel q i f hker hf (Z := Over.mk (g₁ ≫ G.hom))
      (Over.homMk g₁) (Over.homMk g₂ hw) (by ext; simpa using h)
    simpa using congrArg (fun φ => φ.left) key
  let β₀ : B.left ⟶ B'.left := EffectiveEpi.desc q.left f.left hcomp
  have hβ₀ : q.left ≫ β₀ = f.left := EffectiveEpi.fac _ _ _
  have hw : β₀ ≫ B'.hom = B.hom := by
    rw [← cancel_epi q.left, reassoc_of% hβ₀, Over.w f, Over.w q]
  let β : B ⟶ B' := Over.homMk β₀ hw
  have hqβ : q ≫ β = f := by
    ext
    simp [β, hβ₀]
  have hqq : Epi (q ⊗ₘ q) := _root_.GlobalTheory.FlatQuotient.epi_tensorHom q q
  refine ⟨β, ⟨?_, ?_⟩, hqβ⟩
  · rw [← IsMonHom.one_hom (f := q), Category.assoc, hqβ, IsMonHom.one_hom]
  · rw [← cancel_epi (q ⊗ₘ q)]
    calc (q ⊗ₘ q) ≫ μ ≫ β = μ ≫ q ≫ β := by
          rw [← Category.assoc, ← IsMonHom.mul_hom, Category.assoc]
      _ = μ ≫ f := by rw [hqβ]
      _ = (f ⊗ₘ f) ≫ μ := IsMonHom.mul_hom f
      _ = (q ⊗ₘ q) ≫ (β ⊗ₘ β) ≫ μ := by
          rw [← hqβ]
          simp

end FlatQuotient


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.flatQuotient_iso_of_same_kernel :
    ∀ (S : Scheme.{0}) (G B B' T T' : Over S) [GrpObj G] [GrpObj B] [GrpObj B'] [GrpObj T]
      [GrpObj T'] (q : G ⟶ B) (i : T ⟶ G) (q' : G ⟶ B') (i' : T' ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsMonHom q' → IsMonHom i' → Flat q'.left →
      Surjective q'.left → QuasiCompact q'.left → IsPullback i' (toUnit _) q' (η[B']) →
      i' ≫ q = toUnit _ ≫ η[B] → i ≫ q' = toUnit _ ≫ η[B'] →
      ∃ β : B' ≅ B, IsMonHom β.hom ∧ q' ≫ β.hom = q := by
  intro S G B B' T T' _ _ _ _ _ q i q' i' hq _ hqf hqs hqc hk hq' _ hq'f hq's hq'c hk' h₁ h₂
  obtain ⟨β, -, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i q' hk h₂
  obtain ⟨β', hβ', hq'β'⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q' i' q hk' h₁
  have eq : Epi q := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q
  have eq' : Epi q' := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective q'
  have e₁ : β ≫ β' = 𝟙 B := by
    rw [← cancel_epi q, reassoc_of% hqβ, hq'β', Category.comp_id]
  have e₂ : β' ≫ β = 𝟙 B' := by
    rw [← cancel_epi q', reassoc_of% hq'β', hqβ, Category.comp_id]
  exact ⟨⟨β', β, e₂, e₁⟩, hβ', hq'β'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

universe u

theorem isIntegral_of_smooth_field_of_connectedSpace {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] [ConnectedSpace Z] : IsIntegral Z := by
  have hK : IsNormalScheme (Spec (.of K)) := inferInstance
  have : IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsNormalScheme.isIntegral_of_connectedSpace Z

theorem geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field_of_connectedSpace snd

theorem grpObj_geometricallyIntegral_of_smooth (S : Scheme.{0}) (H : Over S) [GrpObj H]
    [Smooth H.hom] [GeometricallyConnected H.hom] : GeometricallyIntegral H.hom :=
  geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom

end GlobalTheory
end

