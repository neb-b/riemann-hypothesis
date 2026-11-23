module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNormalisedGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftExtending
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPartLift

section General
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_torus_lift [Module.Free ℤ X] {Z' Z : Over S} (ρ : Z' ⟶ Z)
    (h : ∀ a : Γ(Z'.left, ⊤)ˣ, ∃ r : Γ(Z.left, ⊤)ˣ, ρ.left.appTop.hom r.val = a.val)
    (t : Z' ⟶ splitTorus S X) : ∃ t' : Z ⟶ splitTorus S X, ρ ≫ t' = t := by
  let e := Module.Free.chooseBasis ℤ X
  choose r hr using h
  let l : X →ₗ[ℤ] Additive Γ(Z.left, ⊤)ˣ := e.constr ℤ fun k => Additive.ofMul (r (chV t (e k)))
  let m : X →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditiveRight (splitTorusPointsEquiv S X Z' t)).toIntLinearMap
  let n : Additive Γ(Z.left, ⊤)ˣ →ₗ[ℤ] Additive Γ(Z'.left, ⊤)ˣ :=
    (MonoidHom.toAdditive (Units.map ρ.left.appTop.hom.toMonoidHom)).toIntLinearMap
  have hl : n ∘ₗ l = m := e.ext fun k => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact congrArg Additive.ofMul (Units.ext (hr _))
  let t' := (splitTorusPointsEquiv S X Z).symm (AddMonoidHom.toMultiplicativeLeft l.toAddMonoidHom)
  have ht' : ∀ χ, chV t' χ = Additive.toMul (l χ) := fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; rfl
  refine ⟨t', (splitTorusPointsEquiv S X Z').injective (MonoidHom.ext fun χ => Units.ext ?_)⟩
  have e₁ : (chV (ρ ≫ t') (Multiplicative.toAdd χ)).val = ρ.left.appTop.hom (chV t' (Multiplicative.toAdd χ)).val := by
    rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]
  refine e₁.trans ?_
  rw [ht']
  exact congrArg (fun a => (Additive.toMul a).val) (LinearMap.congr_fun hl (Multiplicative.toAdd χ))

theorem units_lift {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (a : Γ(Spec (CommRingCat.of A'), ⊤)ˣ) :
    ∃ r : Γ(Spec (CommRingCat.of A), ⊤)ˣ, (Spec.map (CommRingCat.ofHom f)).appTop.hom r.val = a.val := by
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨c, hc⟩ := hf ((Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom a.val)
  have hu : IsUnit c := IsUnit.of_map f c (hc ▸ a.isUnit.map _)
  refine ⟨(hu.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).unit, ?_⟩
  rw [IsUnit.unit_spec]
  have e := congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [← e, hc]
  exact congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso (CommRingCat.of A')).hom_inv_id

theorem exists_lift_extending [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {A A' : Type} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (b : Spec (CommRingCat.of A) ⟶ Q.B.left) (y : Spec (CommRingCat.of A') ⟶ G.left)
    (hy : y ≫ Q.q.left = Spec.map (CommRingCat.ofHom f) ≫ b) :
    ∃ g : Spec (CommRingCat.of A) ⟶ G.left, g ≫ Q.q.left = b ∧ Spec.map (CommRingCat.ofHom f) ≫ g = y := by
  have := Q.q_hom
  have := Q.i_hom
  let b' : Over.mk (b ≫ Q.B.hom) ⟶ Q.B := Over.homMk b rfl
  let y' : Over.mk (y ≫ G.hom) ⟶ G := Over.homMk y rfl
  let ρ : Over.mk (y ≫ G.hom) ⟶ Over.mk (b ≫ Q.B.hom) := Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    change Spec.map (CommRingCat.ofHom f) ≫ b ≫ Q.B.hom = y ≫ G.hom
    rw [← Category.assoc, ← hy, Category.assoc, Over.w])
  have hy' : y' ≫ Q.q = ρ ≫ b' := Over.OverMorphism.ext hy
  obtain ⟨g, hg⟩ := Q.exists_lift b'
  have h₁ : (y' * (ρ ≫ g)⁻¹) ≫ Q.q = toUnit _ ≫ η[Q.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hg, hy', mul_inv_cancel, Hom.one_def]
  obtain ⟨t, ht⟩ := exists_torus_lift ρ (units_lift f hf) (Q.isKernel.lift _ _ h₁)
  have h₃ : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  have a₁ : ((t ≫ Q.i) * g) ≫ Q.q = b' := by rw [MonObj.mul_comp, h₃, _root_.one_mul, hg]
  have a₂ : ρ ≫ ((t ≫ Q.i) * g) = y' := by
    rw [MonObj.comp_mul, ← Category.assoc, ht, IsPullback.lift_fst, inv_mul_cancel_right]
  exact ⟨((t ≫ Q.i) * g).left, congrArg (fun q => q.left) a₁, congrArg (fun q => q.left) a₂⟩

end General

open GlobalTheory.FormalPoint

theorem main : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W → IsLocalHom (algebraMap V W) → ∀ b : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B, ∃ x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) := by
  intro V _ _ _ A G _ _ s t a W _ _ _ hW _ b
  let I := IsLocalRing.maximalIdeal V
  let φ := algebraMap V W
  let J := I.map φ
  have hJ : J ≠ ⊤ := ne_top_of_isHausdorff J
  have hloc := isLocalRing_quotient_pow hJ
  have hbw : b.left ≫ a.B.hom = Spec.map (CommRingCat.ofHom φ) := Over.w b
  have pb : ∀ e, IsPullback (a.b e) (t.l e).Q.B.hom a.B.hom (thick V I e) := fun e => (a.b_pb e).1.1
  have w : ∀ e, (adicLevelι J (e + 1) ≫ b.left) ≫ a.B.hom = levelMap I φ e ≫ thick V I e := fun e =>
    (Category.assoc _ _ _).trans ((congrArg _ hbw).trans (levelMap_thick I φ e).symm)
  let c : ∀ e, Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (t.l e).Q.B.left := fun e => (pb e).lift _ _ (w e)
  have c₁ : ∀ e, c e ≫ a.b e = adicLevelι J (e + 1) ≫ b.left := fun e => (pb e).lift_fst _ _ _
  have c₂ : ∀ e, c e ≫ (t.l e).Q.B.hom = levelMap I φ e := fun e => (pb e).lift_snd _ _ _
  have mth : ∀ e, Mono (thick V I e) := fun e => have := isClosedImmersion_red (I ^ (e + 1)); inferInstance
  have mono : ∀ e, Mono (a.b e) := fun e =>
    (MorphismProperty.monomorphisms _).of_isPullback (pb e).flip (mth e)
  have cc : ∀ e, c e ≫ t.β e = adicLevelMap J (Nat.le_succ (e + 1)) ≫ c (e + 1) := fun e => by
    have := mono (e + 1)
    rw [← cancel_mono (a.b (e + 1)), Category.assoc, Category.assoc, a.b_β, c₁, c₁, adicLevelMap_ι_assoc]
  let P := fun e => {x : Spec (CommRingCat.of (W ⧸ J ^ (e + 1))) ⟶ (thickObj V I e G).left //
    x ≫ (t.l e).Q.q.left = c e}
  have base : Nonempty (P 0) := by
    obtain ⟨g, hg⟩ := (t.l 0).Q.exists_lift (Over.homMk (c 0) rfl : Over.mk (c 0 ≫ (t.l 0).Q.B.hom) ⟶ (t.l 0).Q.B)
    exact ⟨⟨g.left, congrArg (fun q => q.left) hg⟩⟩
  have step : ∀ e (x : P e), ∃ x' : P (e + 1),
      adicLevelMap J (Nat.le_succ (e + 1)) ≫ x'.1 = x.1 ≫ thickMap V I e G := fun e x => by
    obtain ⟨g, h₁, h₂⟩ := exists_lift_extending (t.l (e + 1)).Q (Ideal.Quotient.factorPow J (Nat.le_succ (e + 1)))
      (Ideal.Quotient.factor_surjective _) (c (e + 1)) (x.1 ≫ thickMap V I e G)
      (by rw [Category.assoc, ← t.β_q, ← Category.assoc, x.2, cc])
    exact ⟨⟨g, h₁⟩, h₂⟩
  choose nx hnx using step
  let x : ∀ e, P e := fun e => Nat.rec base.some nx e
  have hx : ∀ e, adicLevelMap J (Nat.le_succ (e + 1)) ≫ (x (e + 1)).1 = (x e).1 ≫ thickMap V I e G :=
    fun e => hnx e (x e)
  have tm : ∀ e, thickMap V I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := fun e =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fam : IsAdicFamily J fun e => (x e).1 ≫ (fstG I e G).left := fun e => by
    rw [← Category.assoc, hx, Category.assoc, tm]
  have fw : ∀ e, (fstG I e G).left ≫ G.hom = (thickObj V I e G).hom ≫ thick V I e := fun e => pullback.condition
  obtain ⟨g, ⟨g₁, g₂⟩, -⟩ := existsUnique_over_of_isAdicFamily (Spec.map (CommRingCat.ofHom φ)) G.hom fam fun e => by
    rw [Category.assoc, fw, ← Over.w (t.l e).Q.q, Category.assoc, ← Category.assoc, (x e).2, ← Category.assoc, c₂]
    exact levelMap_thick I φ e
  refine ⟨Over.homMk g g₁, fun e Z r xe h => ?_⟩
  replace h : xe ≫ (fstG I e G).left = r ≫ g := h
  obtain ⟨l, rfl⟩ := exists_factor_level I φ r (xe ≫ (thickObj V I e G).hom) (by
    rw [Category.assoc, ← fw, ← Category.assoc, h, Category.assoc, g₁])
  have : Mono (fstG I e G).left := have := mth e; (inferInstance : Mono (pullback.fst G.hom (thick V I e)))
  have hxe : xe = l ≫ (x e).1 := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, g₂]
  rw [hxe, Category.assoc, Category.assoc, ← c₁, ← Category.assoc (x e).1, (x e).2]

end GlobalTheory.AbelianPartLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSq
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SymSec
open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem sec_gs {N : LB X} (s : LB.Sec N) (r : Y ⟶ X) (y : Y) {i j : N.ι} (hi : r y ∈ N.U i) (hj : r y ∈ N.U j) :
    gs r y (N.U i) (s.f i) = (gm r y (N.U i ⊓ N.U j) (N.g i j)).val * gs r y (N.U j) (s.f j) := by
  have hm : r y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  exact (gs_res r y _ hm _).symm.trans ((congrArg (gs r y _) (s.compat i j)).trans ((gs_mul r y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r y _ hm _) (gs_res r y _ hm _))))

theorem glue {N : LB X} (hN : N.IsLB) {I : Type} (W : I → X.Opens) (c : I → N.ι) (hc : ∀ i, W i ≤ N.U (c i))
    (hW : ∀ x : X, ∃ i, x ∈ W i) (a : ∀ i, Γ(X, W i))
    (h : ∀ i i' x, x ∈ W i → x ∈ W i' → gs (𝟙 X) x (W i) (a i) =
      (gm (𝟙 X) x (N.U (c i) ⊓ N.U (c i')) (N.g (c i) (c i'))).val * gs (𝟙 X) x (W i') (a i')) :
    ∃ s : LB.Sec N, ∀ i x, x ∈ W i → gs (𝟙 X) x (N.U (c i)) (s.f (c i)) = gs (𝟙 X) x (W i) (a i) := by
  have gl : ∀ j : N.ι, ∃ b : Γ(X, N.U j), ∀ i x, x ∈ N.U j → x ∈ W i →
      gs (𝟙 X) x (N.U j) b = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) := by
    intro j
    obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(X, N.U j ⊓ W i), ∀ i x, x ∈ N.U j ⊓ W i →
        gs (𝟙 X) x _ (u i) = (gm (𝟙 X) x (N.U j ⊓ N.U (c i)) (N.g j (c i))).val * gs (𝟙 X) x (W i) (a i) :=
      ⟨fun i => (X.presheaf.map (homOfLE (inf_le_inf_left _ (hc i) : N.U j ⊓ W i ≤ N.U j ⊓ N.U (c i))).op).hom
          (N.g j (c i)).val * (X.presheaf.map (homOfLE (inf_le_right : N.U j ⊓ W i ≤ W i)).op).hom (a i),
        fun i x hx => (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_res _ x _ hx _).trans
          (gs_unit (𝟙 X) x (N.U j ⊓ N.U (c i)) ⟨hx.1, hc i hx.2⟩ _)) (gs_res _ x _ hx _))⟩
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i => N.U j ⊓ W i) (N.U j)
      (fun i => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨i, hi⟩ := hW x
        exact Opens.mem_iSup.2 ⟨i, hx, hi⟩) u
      (fun i i' => fn_ext (V := (N.U j ⊓ W i) ⊓ (N.U j ⊓ W i')) fun x hx => by
        refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_ (gs_res (𝟙 X) x inf_le_right hx _).symm)
        rw [hu i x hx.1, hu i' x hx.2, h i i' x hx.1.2 hx.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hN (𝟙 X) x hx.1.1 (hc i hx.1.2) (hc i' hx.2.2)])
    refine ⟨b, fun i x h₁ h₂ => ?_⟩
    have hx : x ∈ N.U j ⊓ W i := ⟨h₁, h₂⟩
    exact (gs_res (𝟙 X) x inf_le_left hx b).symm.trans ((congrArg (gs (𝟙 X) x (N.U j ⊓ W i)) (hb i)).trans
      (hu i x hx))
  choose b hb using gl
  refine ⟨⟨b, fun j j' => fn_ext fun x hx => ?_⟩, fun i x hx => ?_⟩
  · obtain ⟨i, hi⟩ := hW x
    refine (gs_res (𝟙 X) x _ hx _).trans (Eq.trans ?_ ((gs_mul (𝟙 X) x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)
    rw [hb j i x hx.1 hi, hb j' i x hx.2 hi, ← _root_.mul_assoc, ← Units.val_mul,
      gm_cocycle hN (𝟙 X) x hx.1 hx.2 (hc i hi)]
  · show gs (𝟙 X) x _ (b (c i)) = _
    rw [hb (c i) i x (hc i hx) hx, gm_self hN (𝟙 X) x (hc i hx), Units.val_one, _root_.one_mul]

theorem gs_ne [IsIntegral Y] (r : Y ⟶ X) [IsIso r] (y : Y) {U : X.Opens} (hy : r y ∈ U) {a : Γ(X, U)} (ha : a ≠ 0) :
    gs r y U a ≠ 0 := by
  rw [gs_eq r y U hy]
  have h₁ : Function.Injective (r.app U).hom := (ConcreteCategory.bijective_of_isIso (r.app U)).1
  intro h
  apply ha
  apply h₁
  apply germ_injective_of_isIntegral Y y (show y ∈ r ⁻¹ᵁ U from hy)
  rw [map_zero, map_zero]
  exact h

theorem sec_ne [IsIntegral X] {N : LB X} (s : LB.Sec N) (hs : ∃ j, s.f j ≠ 0) {i : N.ι} {x : X} (hx : x ∈ N.U i) :
    s.f i ≠ 0 := by
  obtain ⟨j, hj⟩ := hs
  have hne : (N.U j : Set X).Nonempty := by
    by_contra hn
    exact hj (fn_ext fun y hy => (hn ⟨y, hy⟩).elim)
  obtain ⟨y, hy, hyi, hyj⟩ := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _ (N.U i).isOpen
    (N.U j).isOpen ⟨x, trivial, hx⟩ (by simpa using hne)
  intro h0
  have e := sec_gs s (𝟙 X) y (i := j) (j := i) hyj hyi
  rw [h0, gs_eq (𝟙 X) y (N.U i) hyi, map_zero, map_zero, mul_zero] at e
  exact gs_ne (𝟙 X) y hyj hj e

theorem alg {R : Type} [CommRing R] (k : ℕ) {A B C D E F E' F' : Rˣ} {P Q P' Q' : R}
    (e₁ : P' = (A ^ k * C⁻¹).val * P) (e₂ : Q' = (B ^ k * D⁻¹).val * Q) (e₃ : E' = C * D * E)
    (e₄ : F' = B * A⁻¹ * F) :
    P' * Q' * (E' * (F' ^ k)⁻¹).val = (A ^ (2 * k)).val * (P * Q * (E * (F ^ k)⁻¹).val) := by
  subst e₁ e₂ e₃ e₄
  have : (A ^ k * C⁻¹) * (B ^ k * D⁻¹) * (C * D * E * ((B * A⁻¹ * F) ^ k)⁻¹) = A ^ (2 * k) * (E * (F ^ k)⁻¹) := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module
  have := congrArg Units.val this
  simp only [Units.val_mul] at this ⊢
  linear_combination (P * Q) * this

theorem core [IsIntegral X] {L O : LB X} (hL : L.IsLB) (hO : O.IsLB) (σ z : X ⟶ X) [IsIso σ] (p₀ : O.ι)
    (hz : ∀ x, z x ∈ O.U p₀) (sy : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1])) (hsy : sy.IsGen)
    (t : LB.Gen (LB.LinComb O (K := Fin 3) ![𝟙 X, σ, z] ![1, 1, -2])) (ht : t.IsGen) (k : ℕ)
    (s : LB.Sec (LB.div (pw L k) O)) (hs : ∃ j, s.f j ≠ 0) :
    ∃ s : LB.Sec (pw L (2 * k : ℕ)), ∃ j, s.f j ≠ 0 := by
  let W : (L.ι × L.ι) × (O.ι × O.ι) → X.Opens := fun i =>
    (L.U i.1.1 ⊓ O.U i.2.1) ⊓ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)
  have l₁ : ∀ i, W i ≤ LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.2.1, hx.1.1]
  have l₂ : ∀ i, W i ≤ LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀] := fun i x hx => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [hx.1.2, hx.2.2, hz x]
  obtain ⟨a, ha⟩ : ∃ a : ∀ i, Γ(X, W i), ∀ i x, x ∈ W i → gs (𝟙 X) x (W i) (a i) =
      gs (𝟙 X) x (L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) * gs σ x (L.U i.1.2 ⊓ O.U i.2.2) (s.f (i.1.2, i.2.2)) *
        (gm (𝟙 X) x (LB.wchart O ![𝟙 X, σ, z] ![i.2.1, i.2.2, p₀]) (t.s ![i.2.1, i.2.2, p₀]) *
          ((gm (𝟙 X) x (LB.wchart L ![σ, 𝟙 X] ![i.1.2, i.1.1]) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val := by
    refine ⟨fun i => rs X (inf_le_left : W i ≤ L.U i.1.1 ⊓ O.U i.2.1) (s.f (i.1.1, i.2.1)) *
      rs X (inf_le_right : W i ≤ σ ⁻¹ᵁ (L.U i.1.2 ⊓ O.U i.2.2)) ((σ.app (L.U i.1.2 ⊓ O.U i.2.2)).hom (s.f (i.1.2, i.2.2))) *
      (res (l₂ i) (t.s ![i.2.1, i.2.2, p₀]) * ((res (l₁ i) (sy.s ![i.1.2, i.1.1])) ^ k)⁻¹).val, fun i x hx => ?_⟩
    refine (gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·) ((gs_mul _ x _ hx _ _).trans (congrArg₂ (· * ·)
      (gs_res _ x _ hx _) ((gs_res _ x _ hx _).trans ((gs_pull (𝟙 X) σ x _ hx.2 _).trans (by rw [Category.id_comp])))))
      ((gs_unit _ x _ hx _).trans (congrArg Units.val ?_)))
    rw [map_mul, map_inv, map_pow]
    exact congrArg₂ (· * ·) (gm_res _ x _ hx _) (congrArg (fun q => (q ^ k)⁻¹) (gm_res _ x _ hx _))
  have cov : ∀ x : X, ∃ i, x ∈ W i := fun x => by
    obtain ⟨j, hj⟩ := exists_chart hL x
    obtain ⟨j', hj'⟩ := exists_chart hL (σ x)
    obtain ⟨p, hp⟩ := exists_chart hO x
    obtain ⟨q, hq⟩ := exists_chart hO (σ x)
    exact ⟨((j, j'), (p, q)), ⟨hj, hp⟩, ⟨hj', hq⟩⟩
  obtain ⟨s', hs'⟩ := glue (N := pw L (2 * k : ℕ)) (isLB_pw hL (2 * k : ℕ)) W (fun i => i.1.1) (fun i x hx => hx.1.1) cov a (by
    intro i i' x hx hx'
    have tr : ∀ (r : X ⟶ X) (p q : L.ι × O.ι), r x ∈ L.U p.1 ⊓ O.U p.2 → r x ∈ L.U q.1 ⊓ O.U q.2 →
        gs r x (L.U p.1 ⊓ O.U p.2) (s.f p) = (gm r x (L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) ^ k *
          (gm r x (O.U p.2 ⊓ O.U q.2) (O.g p.2 q.2))⁻¹).val * gs r x (L.U q.1 ⊓ O.U q.2) (s.f q) := by
      intro r p q hp hq
      refine (sec_gs s r x (i := p) (j := q) hp hq).trans (congrArg₂ (· * ·) (congrArg Units.val ?_) rfl)
      refine (gm_div O (pw L k) r x p q ⟨hp, hq⟩).trans (congrArg₂ (· * ·) ?_ rfl)
      exact (map_zpow _ _ _).trans (zpow_natCast _ _)
    have e₁ := tr (𝟙 X) (i.1.1, i.2.1) (i'.1.1, i'.2.1) hx.1 hx'.1
    have e₂ := tr σ (i.1.2, i.2.2) (i'.1.2, i'.2.2) hx.2 hx'.2
    have e₃ := gen_trans ht (𝟙 X) x (l₂ i hx) (l₂ i' hx')
    have e₄ := gen_trans hsy (𝟙 X) x (l₁ i hx) (l₁ i' hx')
    have f₃ : trF (L := O) ![𝟙 X, σ, z] ![1, 1, -2] (𝟙 X) x ![i.2.1, i.2.2, p₀] ![i'.2.1, i'.2.2, p₀] =
        gm (𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) * gm σ x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) := by
      rw [trF, Fin.prod_univ_three]
      show gm (𝟙 X ≫ 𝟙 X) x (O.U i.2.1 ⊓ O.U i'.2.1) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ σ) x (O.U i.2.2 ⊓ O.U i'.2.2) (O.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ z) x (O.U p₀ ⊓ O.U p₀) (O.g _ _) ^ (-2 : ℤ) = _
      rw [gm_self hO (𝟙 X ≫ z) x (hz x), one_zpow, _root_.mul_one, zpow_one, zpow_one, Category.id_comp,
        Category.id_comp]
    have f₄ : trF (L := L) ![σ, 𝟙 X] ![1, -1] (𝟙 X) x ![i.1.2, i.1.1] ![i'.1.2, i'.1.1] =
        gm σ x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) * (gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _))⁻¹ := by
      rw [trF, Fin.prod_univ_two]
      show gm (𝟙 X ≫ σ) x (L.U i.1.2 ⊓ L.U i'.1.2) (L.g _ _) ^ (1 : ℤ) *
        gm (𝟙 X ≫ 𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (-1 : ℤ) = _
      rw [zpow_one, zpow_neg_one, Category.id_comp, Category.id_comp]
    have f₅ : gm (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1 ⊓ (pw L (2 * k : ℕ)).U i'.1.1) ((pw L (2 * k : ℕ)).g i.1.1 i'.1.1) =
        gm (𝟙 X) x (L.U i.1.1 ⊓ L.U i'.1.1) (L.g _ _) ^ (2 * k) :=
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    rw [ha i x hx, ha i' x hx', f₅]
    exact alg k e₁ e₂ (e₃.trans (congrArg₂ (· * ·) f₃ rfl)) (e₄.trans (congrArg₂ (· * ·) f₄ rfl)))
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨i, hi⟩ := cov x
  refine ⟨s', i.1.1, fun h0 => ?_⟩
  have e := (hs' i x hi).trans (ha i x hi)
  rw [h0, gs_eq (𝟙 X) x ((pw L (2 * k : ℕ)).U i.1.1) hi.1.1, map_zero, map_zero] at e
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Units.ne_zero _) e.symm
  · exact gs_ne (𝟙 X) x hi.1 (sec_ne s hs (i := (i.1.1, i.2.1)) hi.1)
  · exact gs_ne σ x hi.2 (sec_ne s hs (i := (i.1.2, i.2.2)) hi.2)

theorem exists_sec_sq : ∀ (A : Type) [CommRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] (M : CP B) (k : ℕ) (O : LB B.left), O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → (∃ s : LB.Sec (LB.div (pw M.L.L k) O), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (pw M.L.L (2 * k : ℕ)), (∃ j, s.f j ≠ 0) := by
  intro A _ _ B _ _ _ M k O hO ⟨u, hu⟩ ⟨s, hs⟩
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, ∀ y : Spec (CommRingCat.of A), eSec B y ∈ O.U p₀ := by
    obtain ⟨i, hi⟩ := exists_chart hO (eSec B (IsLocalRing.closedPoint A))
    exact ⟨i, fun y => ((IsLocalRing.specializes_closedPoint y).map (eSec B).continuous).mem_open (O.U i).isOpen hi⟩
  have hι : (𝟙 B : B ⟶ B)⁻¹ = ι[B] := by rw [Hom.inv_def, Category.id_comp]
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (𝟙 B) ι[B]).left ≫ (psum B (x2 B) I.down).left =
      (psum B ![𝟙 B, ι[B]] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift (𝟙 B) ι[B])) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  obtain ⟨t, ht, -⟩ := exists_gen hO (φ' := ![𝟙 B.left, (ι[B]).left, (1 : B ⟶ B).left]) (ε' := ![1, 1, -2])
    (fun V _ h => by
      have p := GlobalTheory.JetSer.prod_lam (𝟙 B) ι[B] h
      rw [← hι, mul_inv_cancel, hι] at p
      simp only [e, zpow_neg, Finset.prod_inv_distrib, p, Fin.prod_univ_three]
      show _ = h (𝟙 B.left) ^ (1 : ℤ) * h (ι[B]).left ^ (1 : ℤ) * h (1 : B ⟶ B).left ^ (-2 : ℤ)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Over.id_left]
      module)
    (LB.invGen O _ _ (LB.pullGen O (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum B (x2 B) I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) u (lift (𝟙 B) ι[B]).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _))
  haveI : IsIso (ι[B]).left := inferInstanceAs (IsIso ((Over.forget _).map ι[B]))
  exact core M.L.isLB hO (ι[B]).left (1 : B ⟶ B).left p₀ (fun x => hp₀ (B.hom x))
    M.sym M.sym_gen t ht k s hs

end GlobalTheory.UU.SymSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueBiTriv
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.EvenCub

section Alg
variable {A A' B U : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommGroup U]

def diff₃ (k : A → U) (x y u : A) : U :=
  k (x * y * u) * (k (x * y))⁻¹ * (k (x * u))⁻¹ * (k (y * u))⁻¹ * k x * k y * k u * (k 1)⁻¹

def diffS (k : A → U) (x : A) : U := k x⁻¹ * (k x)⁻¹

end Alg

section Rep
variable {S X : Scheme.{0}} {L : LB X} {Y : Over S}

def Rep (L : LB X) (Y : Over S) (F : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J

variable {F F' : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U}
  {v v' : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ}

theorem Rep.mul (h : Rep L Y F v) (h' : Rep L Y F' v') :
    Rep L Y (fun U _ k => F U k * F' U k) (fun T σ z J => v T σ z J * v' T σ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ k => DVR.prod_sum₂ _ (hF U k) (hF' U k), fun T σ z J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T σ z J hJ) (hv' T σ z J hJ))⟩

theorem Rep.inv (h : Rep L Y F v) : Rep L Y (fun U _ k => (F U k)⁻¹) (fun T σ z J => (v T σ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ k => ?_, fun T σ z J hJ =>
    (val_inv _ _).trans (congrArg (·⁻¹) (hv T σ z J hJ))⟩
  show _ = (F U k)⁻¹
  rw [← hF U k, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun a _ => zpow_neg _ _

theorem Rep.pull {K : Type} [Fintype K] {Y' : Over S} {φ : K → (Y'.left ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ Y')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (p.left ≫ φ k) ^ ε k = F U h) :
    Rep L Y F (fun _ σ z J => val t (σ ≫ p).left z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, hF,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem Rep.eq_one (hL : L.IsLB) (hY : Function.Surjective Y.hom.appTop.hom) (h : Rep L Y F v)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = 1) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → v _ e z J = 1) (T : Over S) (σ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    v T σ z J = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, hF', hv⟩ := h
  refine (hv T σ z J hJ).symm.trans ((gen_unique' hL (fun U _ k => ?_) Y.hom e.left (Over.w e) hY ht
    (LB.isGen_oneGen L) (fun y I hI => (hv _ e y I hI).trans ((he y I hI).trans (val_one _).symm)) _ σ.left z J hJ).trans
    (val_one _))
  rw [hF', hF]
  exact Fintype.prod_empty _

end Rep

section Quad
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable {H : Over S} [GrpObj H] [IsCommMonObj H] {P : CP G} {i : H ⟶ G} [IsMonHom i]

end Quad

section DVR
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] [IsSeparated G.hom] [GeometricallyConnected G.hom]

end DVR

end GlobalTheory.EvenCub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem isProper_of_isProjBy :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), IsProjBy f → IsProper f := by
  intro R _ X f h
  obtain ⟨N, φ, hφ, e⟩ := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver (R := R) f).1 h
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  rw [← e]
  infer_instance

end GlobalTheory.AbLaw
end

