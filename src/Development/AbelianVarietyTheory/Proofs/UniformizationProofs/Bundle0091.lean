module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageEqOneIffTorusPoint
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section Kernel

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' : Over S'} [GrpObj B] [GrpObj G']
  {X : Type} [AddCommGroup X]

theorem TQ.mono_i_left (Q : TQ G' X) : Mono Q.i.left := by
  have : Mono Q.i := ⟨fun _ _ h => Q.isKernel.hom_ext h (toUnit_unique _ _)⟩
  infer_instance

theorem TQ.image_eq_one_iff (Q : TQ G' X) {β : Q.B.left ⟶ B.left} (hB : IsGrpPullback Q.B B f β)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f) :
    xe ≫ Q.q.left ≫ β = r ≫ (1 : T ⟶ B).left ↔ ∃ τ : Z ⟶ (splitTorus S' X).left, τ ≫ Q.i.left = xe := by
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
  have e₁ : (eB (xe' ≫ Q.q)).left = xe ≫ Q.q.left ≫ β := (heB _).trans (Category.assoc _ _ _)
  have e₂ : (eB 1).left = r ≫ (1 : T ⟶ B).left := by
    rw [map_one, ← MonObj.comp_one R]; rfl
  rw [← e₁, ← e₂]
  constructor
  · intro h
    have h₁ : xe' ≫ Q.q = toUnit _ ≫ η[Q.B] := eB.injective (Over.OverMorphism.ext h)
    exact ⟨(Q.isKernel.lift _ _ h₁).left, congrArg (fun z => z.left) (Q.isKernel.lift_fst _ _ h₁)⟩
  · rintro ⟨τ, hτ⟩
    let τ' : Over.mk (xe ≫ G'.hom) ⟶ splitTorus S' X := Over.homMk τ (by
      rw [← hτ, ← Over.w Q.i]; exact (Category.assoc _ _ _).symm)
    have h₁ : τ' ≫ Q.i = xe' := Over.OverMorphism.ext hτ
    have h₂ : xe' ≫ Q.q = 1 := by
      rw [← h₁, Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (τ' ≫ toUnit _)]
    rw [h₂]

end Kernel

section Scal

variable {A C : Type} [CommRing A] [CommRing C] {Y Y' : Scheme.{0}}

noncomputable def scalRingHom (p : Y ⟶ Spec (CommRingCat.of A)) : A →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

theorem scalRingHom_specMap (p : Y ⟶ Spec (CommRingCat.of C)) (φ : A →+* C) :
    scalRingHom (p ≫ Spec.map (CommRingCat.ofHom φ)) = (scalRingHom p).comp φ :=
  congrArg CommRingCat.Hom.hom (SplitTorusPoints.ΓSpecIso_inv_comp_specMap p (CommRingCat.ofHom φ))

theorem exists_factor_quotient (r : Y ⟶ Spec (CommRingCat.of C)) (J : Ideal C)
    (h : J ≤ RingHom.ker (scalRingHom r)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ J)), r' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = r := by
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J (scalRingHom r) fun _ ha => RingHom.mem_ker.1 (h ha))), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]
  apply ext_to_Spec
  refine (SplitTorusPoints.ΓSpecIso_inv_comp_specMap _ _).trans ?_
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem exists_factor_thick (φ : A →+* C) (I : Ideal A) (e : ℕ) (r : Y ⟶ Spec (CommRingCat.of C))
    (p : Y ⟶ Spec (CommRingCat.of (A ⧸ I ^ (e + 1))))
    (h : p ≫ thick A I e = r ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃ r' : Y ⟶ Spec (CommRingCat.of (C ⧸ I.map φ ^ (e + 1))), r' ≫ thick C (I.map φ) e = r := by
  refine exists_factor_quotient r _ ?_
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  have := congrArg (fun q => scalRingHom q a) h
  simp only [scalRingHom_specMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero] at this
  exact this.symm

theorem exists_torus_point {S : Scheme.{0}} {X : Type} [AddCommGroup X] (c : Multiplicative X →* Cˣ)
    (r : Y ⟶ Spec (CommRingCat.of C)) (p : Y ⟶ S) : ∃ τ : Y ⟶ (splitTorus S X).left, τ ≫ (splitTorus S X).hom = p ∧
      ∀ χ, τ.appTop.hom (charUnit S X χ).val = scal r (c (Multiplicative.ofAdd χ)).val := by
  obtain ⟨τ, hτ⟩ := (splitTorusPointsEquiv S X (Over.mk p)).surjective
    ((Units.map (scalRingHom r).toMonoidHom).comp c)
  refine ⟨τ.left, Over.w τ, fun χ => ?_⟩
  refine (splitTorusPointsEquiv_val S X _ τ χ).symm.trans ?_
  rw [hτ]; rfl

theorem exists_hom_of_thick {X : Type} [AddCommGroup X] (J : Ideal C) [IsAdicComplete J C] {S : ℕ → Scheme.{0}}
    (τ : ∀ e, Spec (CommRingCat.of (C ⧸ J ^ (e + 1))) ⟶ (splitTorus (S e) X).left)
    (h : ∀ e χ, (thickTrans C J e ≫ τ (e + 1)).appTop.hom (charUnit _ X χ).val =
      (τ e).appTop.hom (charUnit _ X χ).val) :
    ∃ c : Multiplicative X →* Cˣ, ∀ e χ,
      (τ e).appTop.hom (charUnit _ X χ).val = scal (thick C J e) (c (Multiplicative.ofAdd χ)).val := by
  let u := fun e => splitTorusPointsEquiv (S e) X (Over.mk (τ e ≫ (splitTorus (S e) X).hom)) (Over.homMk (τ e) rfl)
  have hu : ∀ e χ, (u e (Multiplicative.ofAdd χ)).val = (τ e).appTop.hom (charUnit _ X χ).val := fun e χ =>
    splitTorusPointsEquiv_val _ _ _ _ χ
  choose b hb using fun χ : X => CompletePoint.exists_fn_of_thick J (fun e => (τ e).appTop.hom (charUnit _ X χ).val)
    fun e => by rw [← h e χ, Scheme.Hom.comp_appTop]; rfl
  let b' : Multiplicative X →* Γ(Spec (CommRingCat.of C), ⊤) :=
    { toFun := fun χ => b χ.toAdd
      map_one' := CompletePoint.fn_eq_of_thick J fun e => by
        rw [hb, ← hu]; exact (congrArg Units.val (map_one (u e))).trans (map_one _).symm
      map_mul' := fun χ χ' => CompletePoint.fn_eq_of_thick J fun e => by
        rw [(thick C J e).appTop.hom.map_mul, hb, hb, hb, ← hu, ← hu, ← hu]
        exact congrArg Units.val (map_mul (u e) χ χ') }
  refine ⟨((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom.toMonoidHom.comp b').toHomUnits, fun e χ => ?_⟩
  rw [← hb]
  exact congrArg (thick C J e).appTop.hom (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of C)) (b χ)).symm

end Scal

theorem image_eq_one_iff_torus_point : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ↔ ∃ c : Multiplicative s.X →* Wˣ, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (τ : Z ⟶ (splitTorus _ s.X).left), τ ≫ (splitTorus (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))) s.X).hom ≫ thick V _ e = r ≫ (Spec.map (CommRingCat.ofHom (algebraMap V W))) → (∀ χ, τ.appTop.hom (charUnit _ s.X χ).val = scal r (c (Multiplicative.ofAdd χ)).val) → τ ≫ (t.l e).Q.i.left ≫ (fstG _ e G).left = r ≫ (x).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ x
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  have hx : x.left ≫ G.hom = Spec.map (CommRingCat.ofHom φ) := Over.w x
  have hF : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  have mF : ∀ e, Mono (fstG I e G).left := fun e => pullback.fst_of_mono (f := G.hom) (g := thick V I e)
  have base : ∀ (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x.left →
      r ≫ Spec.map (CommRingCat.ofHom φ) = (xe ≫ (thickObj V I e G).hom) ≫ thick V I e := fun e Z r xe h => by
    rw [Category.assoc, ← hF, ← hx, ← Category.assoc, ← h]
    exact Category.assoc _ _ _
  have ker := fun (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V I e G).left)
    (h : xe ≫ (fstG I e G).left = r ≫ x.left) =>
    (t.l e).Q.image_eq_one_iff (T := Over.mk (Spec.map (CommRingCat.ofHom φ))) (a.b_pb e).1 r xe (base e r xe h)
  constructor
  · intro H
    let J := I.map φ
    have hle : ∀ e : ℕ, I ^ (e + 1) ≤ (J ^ (e + 1)).comap φ := fun e => by
      rw [← Ideal.map_pow]; exact Ideal.le_comap_map
    have hp : ∀ e, (thick W J e ≫ x.left) ≫ G.hom =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ φ (hle e))) ≫ thick V I e := fun e => by
      rw [Category.assoc, hx, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨y, hy⟩ : ∃ y : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left,
        ∀ e, y e ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      ⟨fun e => pullback.lift _ _ (hp e), fun e => pullback.lift_fst _ _ _⟩
    choose τ hτ using fun e => (ker e _ _ (hy e)).1 (H e _ _ _ (hy e))
    obtain ⟨c, hc⟩ := exists_hom_of_thick J τ fun e χ => by
      obtain ⟨σ, -, h₁, h₂⟩ := t.tor e
      have := (t.l (e + 1)).Q.mono_i_left
      have := mF (e + 1)
      have h₃ : thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
        (pullback.lift_fst _ _ _).trans (Category.comp_id _)
      have h₄ : thickTrans W J e ≫ y (e + 1) = y e ≫ thickMap V I e G := by
        refine (cancel_mono (fstG I (e + 1) G).left).1 ?_
        refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hy (e + 1))).trans ?_)
        refine Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₃)).symm
        rw [← Category.assoc, thickTrans_comp]
        exact (hy e).symm
      have h₅ : thickTrans W J e ≫ τ (e + 1) = τ e ≫ σ := by
        rw [← cancel_mono (t.l (e + 1)).Q.i.left, Category.assoc, hτ, h₄, Category.assoc, h₂, ← Category.assoc, hτ]
      rw [h₅, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h₁]
    refine ⟨c, fun e Z r τ' h₁ h₂ => ?_⟩
    obtain ⟨r', rfl⟩ := exists_factor_thick φ I e r _ ((Category.assoc _ _ _).trans h₁)
    have h₃ : τ' = r' ≫ τ e := by
      refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
      · rw [← cancel_mono (thick V I e), Category.assoc]
        refine h₁.trans ?_
        rw [Category.assoc, base e _ _ (hy e), ← hτ e, Category.assoc (τ e), Over.w]
        simp only [Category.assoc]
      · rw [h₂, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hc, scal, scal,
          Scheme.Hom.comp_appTop]
        rfl
    have h₄ : τ e ≫ (t.l e).Q.i.left ≫ (fstG I e G).left = thick W J e ≫ x.left :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e G).left) (hτ e)).trans (hy e))
    rw [h₃]
    exact (Category.assoc _ _ _).trans ((congrArg (r' ≫ ·) h₄).trans (Category.assoc _ _ _).symm)
  · rintro ⟨c, hc⟩ e Z r xe h
    obtain ⟨τ, h₁, h₂⟩ := exists_torus_point c r (xe ≫ (thickObj V I e G).hom)
    have := mF e
    refine (ker e r xe h).2 ⟨τ, (cancel_mono (fstG I e G).left).1 ?_⟩
    refine (Category.assoc _ _ _).trans ((hc e Z r τ ?_ h₂).trans h.symm)
    rw [← Category.assoc, h₁]
    exact (base e r xe h).symm

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartImageOneMulInv
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B] [GrpObj G']
  [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}

theorem exists_imageHom (hG : IsGrpPullback G' G f φ) (hB : IsGrpPullback B' B f β) (q : G' ⟶ B') [IsMonHom q]
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (x₀ : T ⟶ G) (h₀ : xe ≫ φ = r ≫ x₀.left) :
    ∃ (Y : Over S) (R : Y ⟶ T) (Φ : (T ⟶ G) → (Y ⟶ B)), Φ 1 = 1 ∧ (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      (∀ x, Φ x⁻¹ = (Φ x)⁻¹) ∧
      (∀ x b, (∀ ye : Z ⟶ G'.left, ye ≫ φ = r ≫ x.left → ye ≫ q.left ≫ β = r ≫ b.left) → Φ x = R ≫ b) ∧
      ∀ b, Φ x₀ = R ≫ b → xe ≫ q.left ≫ β = r ≫ b.left := by
  have hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f := by
    rw [Category.assoc, ← hG.1.w, reassoc_of% h₀, Over.w]
  obtain ⟨eG, heG⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hG _ _ hc
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  refine ⟨_, R, fun x => eB (eG.symm (R ≫ x) ≫ q), ?_, fun x y => ?_, fun x => ?_, fun x b h => ?_,
    fun b h => ?_⟩
  · simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  · simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]
  · simp only [GrpObj.comp_inv, map_inv, GrpObj.inv_comp]
  · apply Over.OverMorphism.ext
    refine (heB _).trans ((Category.assoc _ _ _).trans (h _ ?_))
    refine (heG _).symm.trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl
  · let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
    have h₁ : eG xe' = R ≫ x₀ := Over.OverMorphism.ext ((heG _).trans h₀)
    have h₂ : eB (xe' ≫ q) = R ≫ b := by
      rw [← h]
      beta_reduce
      rw [← h₁, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans ((heB (xe' ≫ q)).symm.trans (congrArg (fun z => z.left) h₂))

end

theorem image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  intro V _ _ _ A G _ _ s t a W _ _ x x' b b'
  have hG := fun e => isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) e)
  have hB := fun e => (a.b_pb e).1
  have hq := fun e => (t.l e).Q.q_hom
  refine ⟨fun e Z r xe h => ?_, fun h₁ h₂ => ⟨fun e Z r xe h => ?_, fun e Z r xe h => ?_⟩⟩
  · obtain ⟨Y, R, Φ, e₁, -, -, -, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k 1 (by rw [e₁, MonObj.comp_one])
  · obtain ⟨Y, R, Φ, -, e₂, -, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₂, l x b (h₁ e Z r), l x' b' (h₂ e Z r), MonObj.comp_mul])
  · obtain ⟨Y, R, Φ, -, -, e₃, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₃, l x b (h₁ e Z r), GrpObj.comp_inv])

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionGeometricPointOfField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

theorem card_torsion_geometricPoint_of_field :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (n : ℕ), (n : k) ≠ 0 → Nat.card {x : Over.mk t ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
  intro H S B _ hB g hg k _ _ t n hn
  have hB' : IsAbelianScheme ((Over.pullback t).obj B) :=
    { comm := by have := hB.comm; infer_instance
      smooth := by have := hB.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hB.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by have := hB.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := H k ((Over.pullback t).obj B) g n hB' hg' hn
  have hp := isGrpPullback_pullback B t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst B.hom t = y.left ≫ pullback.fst B.hom t := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ B // x ^ n = 1} = n ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTransfer
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GoodReductionUnif

theorem exists_baseChange (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : PolAV S) :
    ∃ (A : PolAV S') (eA : (Over.pullback f).obj P.A ≅ A.A), IsMonHom eA.hom ∧
      ∃ w : LB.Iso (A.L.pull eA.hom.left) (P.L.pull (pullback.fst P.A.hom f)), w.IsGen := by
  obtain ⟨A, g, hg, -, mul, t, ht⟩ := hB S S' f P
  let eA : (Over.pullback f).obj P.A ≅ A.A := Over.isoMk hg.isoPullback.symm hg.isoPullback_inv_snd
  have he : eA.hom.left ≫ g = pullback.fst P.A.hom f := hg.isoPullback_inv_fst
  refine ⟨A, eA, isMonHom_of_mul _ fun T x y => Over.OverMorphism.ext (hg.hom_ext ?_ ?_), ?_⟩
  · have tb : ∀ a : T ⟶ (Over.pullback f).obj P.A, toBase hg.w (a ≫ eA.hom) =
        toBase (A := P.A) (A' := (Over.pullback f).obj P.A) (g := pullback.fst P.A.hom f) pullback.condition a :=
      fun a => Over.OverMorphism.ext ((Category.assoc _ _ _).trans (congrArg (a.left ≫ ·) he))
    have e : toBase hg.w ((x * y) ≫ eA.hom) = toBase hg.w ((x ≫ eA.hom) * (y ≫ eA.hom)) := by
      rw [mul, tb, tb, tb, toBase_mul_pullback]
    exact congrArg CommaMorphism.left e
  · exact (Over.w _).trans (Over.w _).symm
  · obtain ⟨t', ht', -⟩ := GenericSectionBasis.exists_inv_iso t ht
    have h₁ := (isGen_iff t').1 ht'
    have h₂ := (isGen_iff _).1 (pullIso_isGen A.isLB eA.hom.left)
    obtain ⟨w, Tw⟩ := Geo.Tor.exists_comp A.isLB t' (pullIso A.L eA.hom.left) h₁ h₂ P.isLB
      (pull_isLB A.isLB _)
    rw [← he]
    exact ⟨w, (isGen_iff w).2 (Tw.pgen_comp A.isLB h₁ h₂)⟩


end GlobalTheory.GoodReductionUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImage
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.ImagePairing

theorem eq_map_of_isCPMap {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {F : G'.left ⟶ G.left} {hw} {w}
    (h : IsCPMap P' P f F hw w) {N : ℕ} {T' : Over S'} {T : Over S} (r : T'.left ⟶ T.left)
    (hr : r ≫ T.hom = T'.hom ≫ f) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : x'.left ≫ F = r ≫ x.left)
    (hy : y'.left ≫ F = r ≫ y.left) {ζ' ζ} (h' : CubWeil P'.c N x' y' ζ') (h₀ : CubWeil P.c N x y ζ) :
    ζ' = Units.map r.appTop.hom.toMonoidHom ζ := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  have a := cubWeil_map S S' f G G' P P' F hw w h N T' x' y' ζ' h'
  have ex : toBase hw x' = ρ ≫ x := Over.OverMorphism.ext hx
  have ey : toBase hw y' = ρ ≫ y := Over.OverMorphism.ext hy
  rw [ex, ey] at a
  exact a.unique (h₀.comp ρ)

theorem pow_eq_one_of_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G] {N : ℕ} {T' : Over S'}
    {T : Over S} (r : T'.left ⟶ T.left) (hr : r ≫ T.hom = T'.hom ≫ f) {x' : T' ⟶ (Over.pullback f).obj G}
    {x : T ⟶ G} (hx : x'.left ≫ pullback.fst G.hom f = r ≫ x.left) (h : x ^ N = 1) : x' ^ N = 1 := by
  let ρ : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk r hr
  let β : (T' ⟶ (Over.pullback f).obj G) →* (Over.mk (T'.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition)
      (toBase_mul_pullback G f T')
  have ex : β x' = ρ ≫ x := Over.OverMorphism.ext hx
  have e : β (x' ^ N) = β 1 := by rw [map_pow, map_one, ex, ← MonObj.comp_pow, h, MonObj.comp_one]
  refine Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ?_)
  exact (Over.w (x' ^ N)).trans (Over.w (1 : T' ⟶ (Over.pullback f).obj G)).symm

theorem fn_eq_of_thick {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (a b : Γ(Spec (CommRingCat.of R), ⊤))
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom ((thick R I e).appTop.hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem exists_thick_hom {V W : Type} [CommRing V] [CommRing W] [Algebra V W] (I : Ideal V) (e : ℕ) :
    ∃ φ : Spec (CommRingCat.of (W ⧸ (I.map (algebraMap V W)) ^ (e + 1))) ⟶ Spec (CommRingCat.of (V ⧸ I ^ (e + 1))),
      thick W (I.map (algebraMap V W)) e ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) = φ ≫ thick V I e := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap V W) ?_)), ?_⟩
  · rw [← Ideal.map_pow]; exact Ideal.le_comap_map
  · simp only [thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem cubWeil_image : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ (N : ℕ) (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B) (ζ), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → b ^ N = 1 → b' ^ N = 1 → CubWeil s.P.c N x x' ζ → CubWeil a.M.c N b b' ζ := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ N x x' b b' ζ hx hx' hb hb' h
  obtain ⟨ξ, hξ, -⟩ := existsUnique_cubWeil a.M.c hb hb'
  suffices e : ζ = ξ from e ▸ hξ
  refine Units.ext (fn_eq_of_thick ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) _ _ fun e => ?_)
  obtain ⟨φ, hφ⟩ := exists_thick_hom (W := W) (IsLocalRing.maximalIdeal V) e
  let r := thick W ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) e
  have lifts : ∀ y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G,
      ∃ ye : Over.mk φ ⟶ thickObj V (IsLocalRing.maximalIdeal V) e G,
        ye.left ≫ pullback.fst G.hom (thick V _ e) = r ≫ y.left := fun y =>
    ⟨Over.homMk (pullback.lift (r ≫ y.left) φ ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (Over.w y)).trans hφ)))
      (pullback.lift_snd _ _ _), pullback.lift_fst _ _ _⟩
  obtain ⟨y, hy⟩ := lifts x
  obtain ⟨y', hy'⟩ := lifts x'
  obtain ⟨θ, hθ, -⟩ := existsUnique_cubWeil (t.l e).Pe.c
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy h.1)
    (pow_eq_one_of_pullback (T' := Over.mk φ) (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))))
      _ r hφ hy' h.2.1)
  obtain ⟨w, hw⟩ := (t.l e).lev
  obtain ⟨hp, v, hv⟩ := a.b_pb e
  have e₁ := eq_map_of_isCPMap hw (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r hφ hy hy' hθ h
  obtain ⟨u, -, hu⟩ := hv.exists_comp (t.l e).D.map (by
    rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w, Category.id_comp])
  have e₂ := eq_map_of_isCPMap hu (T' := Over.mk φ)
    (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) r
    (hφ.trans (congrArg (φ ≫ ·) (Category.id_comp _).symm)) (hx e _ r y.left hy) (hx' e _ r y'.left hy') hθ hξ
  exact congrArg Units.val (e₁.symm.trans e₂)

end GlobalTheory.UU.ImagePairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtCancelNonzeroScalarStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.expandsAt_cancel_nonzero_scalar : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) [QuasiCompact G.hom] (r : R), r ≠ 0 → ∀ (σ₀ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∀ e, U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.expandsAt_cancel_scalar | exact GlobalTheory.expandsAt_cancel_scalar | (intros; apply GlobalTheory.expandsAt_cancel_scalar <;> assumption)
end

