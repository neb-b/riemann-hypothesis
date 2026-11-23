module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsNilpotentOfRd
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueCharacterOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvSurjective
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.CubeLift

open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)

section Expand

variable {S S' : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {R : CommRingCat.{0}}

private theorem app_global_comp_apply {U V W' : Scheme.{0}} (f : U ⟶ V) (g : V ⟶ W') (u : Γ(W', ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) := by
  rfl

private theorem splitTorus_pull_comp {B : CommRingCat.{0}} {s : Spec B ⟶ S}
    (g : Over.mk s ⟶ splitTorus S Y) (h : splitTorus S Y ⟶ splitTorus S X) (u : Γ((splitTorus S X).left, ⊤)) :
    pull (g ≫ h) u = pull g (h.left.appTop.hom u) := by
  simp only [SplitTorus.pull, RingHom.comp_apply, Over.comp_left, app_global_comp_apply]

theorem ev_torusMap (t : Spec R ⟶ S) (φ : X →+ Y) (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((SplitTorus.torusMap S φ).left.appTop.hom u) = mv φ (ev t u) := by
  have key : ∀ hs, univPt Y t ≫ SplitTorus.torusMap S φ =
      ptOf (B := CommRingCat.of (AddMonoidAlgebra R Y)) t (mv φ) hs := by
    intro hs
    refine SplitTorus.pull_ext fun a => ?_
    rw [SplitTorus.pull_ptOf, splitTorus_pull_comp, SplitTorus.torusMap_appTop_chi]
    change ev t _ = _
    rw [SplitTorus.ev_chi, SplitTorus.ev_chi, mv_single]
  have hs : Spec.map (CommRingCat.ofHom ((mv φ : AddMonoidAlgebra R X →+* AddMonoidAlgebra R Y).comp
      (algebraMap R (AddMonoidAlgebra R X)))) ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R Y))) ≫ t := by
    congr 3
    ext r
    simp [mv]
  change pull (univPt Y t) _ = _
  rw [← splitTorus_pull_comp, key hs, SplitTorus.pull_ptOf]

theorem ev_bcMap (f : S' ⟶ S) (t : Spec R ⟶ S') (u : Γ((splitTorus S X).left, ⊤)) :
    ev t ((bcMap f X).appTop.hom u) = ev (t ≫ f) u := by
  have e : (univPt X t).left ≫ bcMap f X = (univPt X (t ≫ f)).left := by
    refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · simp [SplitTorus.bcMap_hom]
    · have h0 : (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X t) χ) =
          (Scheme.ΓSpecIso _).hom.hom (SplitTorus.val (univPt X (t ≫ f)) χ) := by
        rw [← SplitTorus.pull_chi, ← SplitTorus.pull_chi]
        exact (SplitTorus.ev_chi t χ).trans (SplitTorus.ev_chi (t ≫ f) χ).symm
      have h1 := congrArg (Scheme.ΓSpecIso _).inv.hom h0
      simp only [Iso.hom_inv_id_apply] at h1
      rw [SplitTorus.val_eq, SplitTorus.val_eq] at h1
      rw [app_global_comp_apply, SplitTorus.charUnit_val, SplitTorus.bcMap_appTop_chi]
      exact h1
  change pull (univPt X t) _ = pull (univPt X (t ≫ f)) u
  simp only [SplitTorus.pull, RingHom.comp_apply, ← e, app_global_comp_apply]

theorem ev_injective : Function.Injective (ev (X := X) (𝟙 (Spec R))) := by
  intro u v h
  refine SplitTorus.eq_of_ev fun B t => ?_
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ ≫ 𝟙 _ = t := ⟨Spec.preimage t, by simp⟩
  rw [SplitTorus.ev_comp, SplitTorus.ev_comp, h]

private theorem ev_base_apply (r : R) :
    ev (X := X) (𝟙 (Spec R)) ((splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) =
      AddMonoidAlgebra.single 0 r := by
  change pull (univPt X _) _ = _
  have hw := Over.w (univPt X (𝟙 (Spec R)))
  simp only [SplitTorus.pull, RingHom.comp_apply]
  rw [← app_global_comp_apply, hw]
  erw [Category.comp_id]
  erw [SplitTorus.specMap_appTop_apply, Iso.inv_hom_id_apply]
  rfl

theorem ev_surjective : Function.Surjective (ev (X := X) (𝟙 (Spec R))) := by
  intro w
  induction w using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    refine ⟨(splitTorus (Spec R) X).hom.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) * chi X x, ?_⟩
    rw [map_mul, SplitTorus.ev_chi, ev_base_apply, AddMonoidAlgebra.single_mul_single, zero_add, _root_.mul_one]

end Expand

section Points

variable {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z Z' V : Over S}

abbrev app {Z V : Scheme.{0}} (r : Z ⟶ V) : Γ(V, ⊤)ˣ →* Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom

theorem app_app {Z Z' V : Scheme.{0}} (r : Z' ⟶ Z) (s : Z ⟶ V) (u : Γ(V, ⊤)ˣ) : app r (app s u) = app (r ≫ s) u := by
  ext
  exact (app_global_comp_apply r s u.val).symm

def pt (x y u : Z ⟶ splitTorus S X) : Z ⟶ splitTorus S (X × X × X) :=
  ofVal ((valHom x).coprod ((valHom y).coprod (valHom u)))

theorem pt_p₁ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₁ = x := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₂ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₂ = y := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_p₃ (x y u : Z ⟶ splitTorus S X) : pt x y u ≫ SplitTorus.torusMap S p₃ = u := by
  refine SplitTorus.hom_ext fun a => ?_
  rw [SplitTorus.val_comp_torusMap, pt, SplitTorus.val_ofVal]
  simp

theorem pt_torusMap (a b c : X →+ Y) : pt (SplitTorus.torusMap S a) (SplitTorus.torusMap S b) (SplitTorus.torusMap S c) = SplitTorus.torusMap S (tri a b c) := by
  refine SplitTorus.hom_ext fun p => ?_
  obtain ⟨x, y, z⟩ := p
  rw [pt, SplitTorus.val_ofVal, SplitTorus.val_torusMap]
  simp only [AddMonoidHom.coprod_apply, toMul_add, Units.val_mul, SplitTorus.valHom_apply,
    SplitTorus.val_torusMap, tri]
  rw [← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id, ← SplitTorus.val_id,
    SplitTorus.val_add, SplitTorus.val_add]

def dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (x y u : Z ⟶ V) : Γ(Z.left, ⊤)ˣ :=
  app (x * y * u).left g * app x.left g * app y.left g * app u.left g / app (x * y).left g / app (x * u).left g /
    app (y * u).left g

theorem app_dif [GrpObj V] (g : Γ(V.left, ⊤)ˣ) (r : Z' ⟶ Z) (x y u : Z ⟶ V) :
    app r.left (dif g x y u) = dif g (r ≫ x) (r ≫ y) (r ≫ u) := by
  simp only [dif, map_mul, map_div, app_app, ← Over.comp_left, Hom.mul_def, comp_lift_assoc]

end Points

section Affine

variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

abbrev ex : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ →* (AddMonoidAlgebra A X)ˣ :=
  Units.map (ev (X := X) (𝟙 (Spec (CommRingCat.of A)))).toMonoidHom

theorem ex_bijective : Function.Bijective (ex (A := A) (X := X)) := by
  have hi := ev_injective (R := CommRingCat.of A) (X := X)
  have hs := ev_surjective (R := CommRingCat.of A) (X := X)
  refine ⟨fun u v h => Units.ext (hi (congrArg Units.val h)), fun w => ?_⟩
  obtain ⟨a, ha⟩ := hs w.val
  obtain ⟨b, hb⟩ := hs w.inv
  have hab : a * b = 1 := hi (by rw [map_mul, ha, hb, w.val_inv, map_one])
  exact ⟨⟨a, b, hab, by rw [_root_.mul_comm, hab]⟩, Units.ext ha⟩

theorem ex_app (φ : X →+ Y) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (app (SplitTorus.torusMap _ φ).left u) = um φ (ex u) := Units.ext (ev_torusMap (𝟙 _) φ u.val)

theorem ex_dif (a b c : X →+ Y) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex (dif g (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b) (SplitTorus.torusMap _ c)) = del (ex g) a b c := by
  simp only [dif, del, map_mul, map_div, ← SplitTorus.torusMap_add, ex_app]

theorem ex_mem_cong (J : Ideal A) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ) :
    ex u ∈ cong J ↔ app (bcMap (red J) X) u = 1 := by
  have key : ev (𝟙 _) ((bcMap (red J) X).appTop.hom u.val) = rd J (ev (𝟙 _) u.val) := by
    rw [ev_bcMap, Category.id_comp,
      show red J = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ 𝟙 _ from (Category.comp_id _).symm,
      SplitTorus.ev_comp]
    rfl
  rw [mem_cong, Units.ext_iff, Units.val_one]
  change rd J (ev (𝟙 _) u.val) = 1 ↔ (bcMap (red J) X).appTop.hom u.val = 1
  constructor
  · intro h
    apply ev_injective
    rw [key, h, map_one]
  · intro h
    rw [← key, h, map_one]

variable {J : Ideal A}

theorem exists_dif (hJ : IsNilpotent J) (D : Γ((splitTorus (Spec (CommRingCat.of A)) (X × X × X)).left, ⊤)ˣ)
    (s₁ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt y x u).left D)
    (s₂ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt x u y).left D)
    (co : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u v : Z ⟶ splitTorus _ X),
      app (pt (x * y) u v).left D * app (pt x y v).left D = app (pt x (y * u) v).left D * app (pt y u v).left D)
    (h : app (bcMap (red J) _) D = 1) :
    ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ, app (bcMap (red J) X) g = 1 ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), app (pt x y u).left D = dif g x y u := by
  have hcub : Cub (ex (A := A) (X := X × X × X) D) := by
    refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
    · have h1 := congrArg ex (s₁ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (s₂ (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c))
      simpa only [pt_torusMap, ex_app] using h1
    · have h1 := congrArg ex (co (splitTorus _ Y) (SplitTorus.torusMap _ a) (SplitTorus.torusMap _ b)
        (SplitTorus.torusMap _ c) (SplitTorus.torusMap _ d))
      simpa only [← SplitTorus.torusMap_add, pt_torusMap, map_mul, ex_app] using h1
  obtain ⟨g', hg', hD⟩ := hcub.exists_del hJ ((ex_mem_cong J D).2 h)
  obtain ⟨g, rfl⟩ := (ex_bijective (A := A) (X := X)).2 g'
  have hD' : D = dif g (SplitTorus.torusMap _ p₁) (SplitTorus.torusMap _ p₂) (SplitTorus.torusMap _ p₃) := by
    apply (ex_bijective (A := A) (X := X × X × X)).1
    rw [hD, ex_dif]
  refine ⟨g, (ex_mem_cong J g).1 hg', fun Z x y u => ?_⟩
  rw [hD', app_dif, pt_p₁, pt_p₂, pt_p₃]

theorem eq_one_of_dif (hJ : IsNilpotent J) (g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ)
    (h : app (bcMap (red J) X) g = 1)
    (hg : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), dif g x y u = 1) : g = 1 := by
  have h1 : ex g ∈ cong J := (ex_mem_cong J g).2 h
  have h2 : del (ex g) p₁ p₂ p₃ = 1 := by
    rw [← ex_dif, hg, map_one]
  apply (ex_bijective (A := A) (X := X)).1
  rw [eq_one_of_del hJ h1 h2, map_one]

end Affine

end GlobalTheory.CubeLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CubicUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def ev {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : Γ(Z.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom.toMonoidHom u

theorem ev_val {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : (ev x u).val = x.left.appTop.hom u.val := rfl

theorem ev_comp {W Z Y : Over S} (p : W ⟶ Z) (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev p (ev x u) = ev (p ≫ x) u := by
  ext
  rw [ev_val, ev_val, ev_val, Over.comp_left, GlobalTheory.FunDescent.comp_appTop_apply]

theorem ev_mul {Z Y : Over S} (x : Z ⟶ Y) (u v : Γ(Y.left, ⊤)ˣ) : ev x (u * v) = ev x u * ev x v := by
  simp only [ev, map_mul]

theorem ev_inv {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev x u⁻¹ = (ev x u)⁻¹ := by
  simp only [ev, map_inv]

theorem exists_char (Y : Over S) [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), ev (lift t y) ρ = chV t χ := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val := by
    intro Z t t' y
    have := congrArg Units.val (hρ Z t t' y)
    simpa [ev_val] using this
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y => ?_⟩
  ext
  rw [ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]

theorem eq_zero_of_chV (Y : Over S) [ConnectedSpace Y.left] (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t χ = 1) : χ = 0 := by
  have key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) →
      ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val := by
    intro ψ hψ
    have := congrArg Units.val (hψ _ (fst (splitTorus S X) Y))
    rw [chV_val] at this
    rw [this, Units.val_one]
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val *
          (lift t' y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val := by
    intro Z t t' y
    simp
  obtain ⟨ψ, -, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y 1 hm
  rw [huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]

private lemma mul_inv_inv_eq_of_mul_mul_mul_eq {M : Type*} [CommGroup M] (A AB a b y AY BY : M)
    (c : A * a * b * y = AB * AY * BY) :
    A * AB⁻¹ * y⁻¹ = AY * a⁻¹ * y⁻¹ * (BY * b⁻¹ * y⁻¹) := by
  apply Additive.ofMul.injective
  have c2 := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at c2 ⊢
  have hA : Additive.ofMul A = Additive.ofMul AB + Additive.ofMul AY + Additive.ofMul BY -
      (Additive.ofMul a + Additive.ofMul b + Additive.ofMul y) := by
    rw [← c2]
    abel
  rw [hA]
  abel

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {M : Type*} [CommGroup M] {p a b : M} (h : p * a⁻¹ * b⁻¹ = 1) : p = a * b := by
  rw [_root_.mul_assoc, ← _root_.mul_inv_rev, _root_.mul_inv_eq_one] at h
  rw [h, _root_.mul_comm]

end GlobalTheory.CubicUnit

namespace GlobalTheory
open CubicUnit

theorem even_cubic_unit_eq_one :
    (GlobalFnsSt → ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ), (∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) → U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) → u = 1) := by
  intro hG S _ X _ _ G _ _ _ Q u hU
  haveI := Q.i_hom
  haveI := Q.q_hom
  haveI := Q.q_flat
  haveI := Q.q_surj
  haveI := Q.q_affine

  have hval : ∀ T : Over S, ∀ x : T ⟶ G, (fun x : T ⟶ G => (ev x u).val) x = x.left.appTop.hom u.val :=
    fun T x => ev_val x u
  have h1 : ∀ T : Over S, ev (1 : T ⟶ G) u = 1 := fun T =>
    Units.ext (by simpa using (hU T _ (hval T)).1)
  have hinv : ∀ (T : Over S) (x : T ⟶ G), ev x⁻¹ u = ev x u := fun T x =>
    Units.ext ((hU T _ (hval T)).2.1 x)
  have hcub : ∀ (T : Over S) (x y v : T ⟶ G),
      ev (x * y * v) u * ev x u * ev y u * ev v u = ev (x * y) u * ev (x * v) u * ev (y * v) u :=
    fun T x y v => Units.ext (by simpa only [Units.val_mul] using (hU T _ (hval T)).2.2 x y v)

  let ρ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ :=
    ev ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G) u *
      (ev (fst (splitTorus S X) G ≫ Q.i) u)⁻¹ * (ev (snd (splitTorus S X) G) u)⁻¹
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift t y) ρ = ev ((t ≫ Q.i) * y) u * (ev (t ≫ Q.i) u)⁻¹ * (ev y u)⁻¹ := by
    intro Z t y
    simp only [ρ, ev_mul, ev_inv, ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hmul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ := by
    intro Z t t' y
    rw [hρ, hρ, hρ, MonObj.mul_comp]
    exact mul_inv_inv_eq_of_mul_mul_mul_eq _ _ _ _ _ _ _ (hcub Z (t ≫ Q.i) (t' ≫ Q.i) y)
  obtain ⟨χ, hχ⟩ := exists_char G ρ hmul

  have hsplit : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev ((t ≫ Q.i) * y) u = ev (t ≫ Q.i) u * ev y u := by
    intro Z t y
    have e1 := hχ Z t y
    have e0 := hχ Z t 1
    rw [hρ] at e1 e0
    simp only [_root_.mul_one, h1, _root_.inv_one, _root_.mul_inv_cancel] at e0
    rw [← e0] at e1
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one e1

  let ρ₂ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ := ev (fst (splitTorus S X) G ≫ Q.i) u
  have hρ₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ₂ = ev (t ≫ Q.i) u := by
    intro Z t y
    simp only [ρ₂, ev_comp, lift_fst_assoc]
  have hmul₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ₂ = ev (lift t y) ρ₂ * ev (lift t' y) ρ₂ := by
    intro Z t t' y
    rw [hρ₂, hρ₂, hρ₂, MonObj.mul_comp, hsplit]
  obtain ⟨ψ, hψ⟩ := exists_char G ρ₂ hmul₂
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = chV t ψ := fun Z t => by
    rw [← hρ₂ Z t 1, hψ]
  have h2ψ : ψ + ψ = 0 := by
    refine eq_zero_of_chV G (ψ + ψ) fun Z t => ?_
    have e := hinv Z (t ≫ Q.i)
    rw [← GrpObj.inv_comp, hψ', hψ', chV_inv] at e
    rw [chV_add]
    calc chV t ψ * chV t ψ = (chV t ψ)⁻¹ * chV t ψ := by rw [e]
      _ = 1 := _root_.inv_mul_cancel _
  have hψ0 : ψ = 0 := by
    rw [← two_zsmul] at h2ψ
    exact (smul_eq_zero.mp h2ψ).resolve_left (by norm_num)
  have htor : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = 1 := fun Z t => by
    rw [hψ', hψ0, chV_zero]
  have hsec : (1 : 𝟙_ (Over S) ⟶ G).left.appTop.hom u.val = 1 := by
    rw [← ev_val, h1, Units.val_one]

  have L : ∀ {Z : Scheme.{0}} (k : Z ⟶ G.left) (h : ⊤ ≤ k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤))
      (f : Γ(G.left, Q.q.left ⁻¹ᵁ ⊤)), (k.appLE (Q.q.left ⁻¹ᵁ ⊤) ⊤ h).hom f = k.appTop.hom f := by
    intro Z k h f
    show (k.appLE _ (k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) le_rfl).hom f = _
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.invariant_functions_descend S G Q.B (splitTorus S X) Q.q Q.i Q.q_hom Q.i_hom
    Q.q_flat Q.q_surj inferInstance Q.isKernel ⊤).2.2 u.val (fun Z t g h₁ h₂ => by
      have e := congrArg Units.val
        (show ev ((t ≫ Q.i) * g) u = ev g u by rw [hsplit, htor, _root_.one_mul])
      rw [ev_val, ev_val] at e
      exact (L _ _ _).trans (e.trans (L _ _ _).symm))
  have hq : Q.q.left.appTop.hom a = u.val := ha
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilCube.surj_fst hG Q.isAb (𝟙_ (Over S))
    ((snd (𝟙_ (Over S)) Q.B).left.appTop.hom a)
  have hB : a = (toUnit Q.B).left.appTop.hom c₀ := by
    have e := congrArg (lift (toUnit Q.B) (𝟙 Q.B)).left.appTop.hom hc₀
    rw [← GlobalTheory.FunDescent.comp_appTop_apply, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_snd, Over.id_left] at e
    simpa using e.symm
  have hG0 : u.val = (toUnit G).left.appTop.hom c₀ := by
    rw [← hq, hB, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique (Q.q ≫ toUnit Q.B) (toUnit G)]
  have hc : c₀ = 1 := by
    have e := hsec
    rw [hG0, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G) ≫ toUnit G) (𝟙 _), Over.id_left] at e
    simpa using e
  exact Units.ext (by rw [hG0, hc, map_one, Units.val_one])

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfChartPull
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_gen_of_chartPull {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen A', t'.IsGen := by
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have v : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (t.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (t.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (ht (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (v i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (v j hy.2)))

theorem polarisation_extends : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∃ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V)))) := by
  intro hL V _ _ _ A G _ _ hG gen hgen
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨t, ht⟩ := A.rigid
  have e₁ : eSec ((Over.pullback (jK V)).obj G) ≫ gen.hom.left = eSec A.A := by
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have e₂ : eSec ((Over.pullback (jK V)).obj G) ≫ jA V (FractionRing V) G = eK V (FractionRing V) G := by
    unfold eSec eK eSec
    simp
  obtain ⟨ρ, hρ⟩ := exists_gen_of_chartPull
    (chartPullLinComb A.L gen.hom.left (K := PUnit) (fun _ => eSec ((Over.pullback (jK V)).obj G))
      (fun _ => eSec A.A) (fun _ => 1) (𝟙 _) (fun _ => e₁.trans (Category.id_comp _).symm)) t ht
  obtain ⟨L, φ, hφ⟩ := hL.extend V (FractionRing V) G _ e₂ (A.L.pull gen.hom.left) (pull_isLB A.isLB _) ρ hρ
  exact ⟨L, LBIso.symm ⟨φ, hφ⟩⟩

end GlobalTheory.UU
end

