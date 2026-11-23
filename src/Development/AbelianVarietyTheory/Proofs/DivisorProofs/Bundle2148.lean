module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharacterSymmetricDefectTwiceFieldExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_char_of_cub [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have := connectedSpace_torus (S := S) (X := X)
  let pb : ∀ {W : Over S}, (W ⟶ splitTorus S X) → Γ(W.left, ⊤)ˣ := fun p => Units.map p.left.appTop.hom.toMonoidHom u
  have hpb : ∀ {W Z : Over S} (p : W ⟶ splitTorus S X) (r : Z ⟶ W) (z : Z.left),
      gm r.left z ⊤ (pb p) = gm (r ≫ p).left z ⊤ u := fun p r z => gm_pull r.left p.left z ⊤ trivial u
  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    let d : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ :=
      pb (fst _ _ * snd _ _) * (pb (fst _ _))⁻¹ * (pb (snd _ _))⁻¹
    have hd : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left), gm (lift x y).left z ⊤ d =
        gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := fun Z x y z => by
      simp only [d, map_mul, map_inv, hpb, MonObj.comp_mul, lift_fst, lift_snd]
    have e := eq_one_of_mul d (fun Z t t' y z => by
      have e' := congrArg Additive.ofMul (h₃ Z t t' y z)
      rw [hd, hd, hd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e') (fun Z t z => by
        rw [hd, _root_.mul_one, h₁, mul_inv_cancel, inv_one, _root_.one_mul]) Z x y z
    rw [hd, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at e
    exact e
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  let ρ : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ := pb (fst _ _)
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm t.left z ⊤ u := fun Z t y z => by rw [hpb, lift_fst]
  obtain ⟨χ, hχ, -⟩ := existsUnique_char ρ fun Z t t' y z => by rw [hρ, hρ, hρ, hmul]
  exact ⟨χ, fun Z t z => (hρ Z t (toUnit _) z).symm.trans (hχ Z t _ z)⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem cub_down_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₀ c c₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : U}
    (h : v₁ * v₂ * v₃ * v₄ = c * v₅ * v₆ * v₇) (hc : c * w₅ * w₆ * w₇ * w₀ = w₁ * w₂ * w₃ * w₄ * c₀)
    (r₁ : v₁ = w₁ * w₀⁻¹ * a₁) (r₂ : v₂ = w₂ * w₀⁻¹ * a₂) (r₃ : v₃ = w₃ * w₀⁻¹ * a₃) (r₄ : v₄ = w₄ * w₀⁻¹ * a₄)
    (r₅ : v₅ = w₅ * w₀⁻¹ * a₅) (r₆ : v₆ = w₆ * w₀⁻¹ * a₆) (r₇ : v₇ = w₇ * w₀⁻¹ * a₇) :
    a₁ * a₂ * a₃ * a₄ = c₀ * a₅ * a₆ * a₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul h
  have b := congrArg Additive.ofMul hc
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b ⊢
  linear_combination (norm := abel) a + b

theorem ratio_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ s₁ s₂ s₃ s₄ s₅ s₆ s₇ g₁ g₂ g₃ g₄ g₅ g₆ g₇ c : U}
    (ha : a₁ * a₂ * a₃ * a₄ = c * a₅ * a₆ * a₇) (hs : s₁ * s₂ * s₃ * s₄ = c * s₅ * s₆ * s₇)
    (r₁ : s₁ = g₁ * a₁) (r₂ : s₂ = g₂ * a₂) (r₃ : s₃ = g₃ * a₃) (r₄ : s₄ = g₄ * a₄)
    (r₅ : s₅ = g₅ * a₅) (r₆ : s₆ = g₆ * a₆) (r₇ : s₇ = g₇ * a₇) :
    g₁ * g₂ * g₃ * g₄ = g₅ * g₆ * g₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul ha
  have b := congrArg Additive.ofMul hs
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b ⊢
  linear_combination (norm := abel) b - a

theorem even_alg {U : Type} [CommGroup U] {A₁ A Wi Wx W₀ E s s' g : U}
    (e₁ : Wi * W₀⁻¹ * A₁ = E * (s * (Wx * W₀⁻¹ * A))) (e₂ : s * Wx = Wi * s')
    (e₃ : g⁻¹ * A₁ = s' * (g * A)) : E = g * g := by
  have a := congrArg Additive.ofMul e₁
  have b := congrArg Additive.ofMul e₂
  have d := congrArg Additive.ofMul e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b d ⊢
  linear_combination (norm := abel) d - a - b

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_char_odd {S : Scheme.{0}} [ConnectedSpace S] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G} [IsMonHom i] (P : CP G) (σ : CubTriv P.c i) :
    ∃ κ : X, ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
      val σ.s (x⁻¹).left z J = gm (𝟙 T.left) z ⊤ (chV x κ) * (val P.sym (x ≫ i).left z J * val σ.s x.left z J) := by
  obtain ⟨E, hE⟩ := exists_odd P σ.s σ.gen
  obtain ⟨κ, hκ⟩ := exists_char_of_cub E (fun T x y u z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
      have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
      simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
      have o := odd_alg (σ := fun a : T ⟶ splitTorus S X => val σ.s a.left z C)
        (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
        (σ.cub T x y u z C hC) a b
      have o' := congrArg Additive.ofMul o
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_one] at o' ⊢
      linear_combination (norm := abel) o')
    (fun T z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have e := hE T 1 z C hC
      rw [inv_one, σ.val_one hC, MonObj.one_comp, P.val_sym_one hC, _root_.mul_one, _root_.mul_one] at e
      exact e.symm)
  exact ⟨κ, fun T x z J hJ => (hE T x z J hJ).trans (by rw [hκ])⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_twist_even : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  intro k k' _ _ hk hk' ρ G₀ _ _ G'₀ _ _ β₀ hβ₀ P₀ P'₀ w₀ hm X _ _ _ i i₁ hi hi₁ hc σ σ₁ hσ₁
  haveI := hi
  haveI := hi₁
  haveI : ConnectedSpace (Sp k) := by letI := hk.toField; infer_instance
  haveI : ConnectedSpace (Sp k') := by letI := hk'.toField; infer_instance
  obtain ⟨κ, hκ⟩ := exists_char_odd P₀ σ
  let f := spMap ρ
  let hw : β₀ ≫ G₀.hom = G'₀.hom ≫ f := hβ₀.1.w
  have hi' : SplitTorus.bcMap f X ≫ i.left = i₁.left ≫ β₀ := torusCompat_iff.1 hc
  have hcc : ∀ n : Fin 2, ![i₁.left, (1 : splitTorus (Sp k') X ⟶ G'₀).left] n ≫ β₀ =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left] n := fun n => by
    fin_cases n
    · exact hi'.symm
    · refine (one_left_comp hm.mul _).trans (Eq.trans ?_ (congrArg (SplitTorus.bcMap f X ≫ ·) (one_left G₀ _)).symm)
      rw [← SplitTorus.bcMap_hom, Category.assoc]
  obtain ⟨a, ha, H⟩ := CubTransport.exists_pmaps ((isGen_iff w₀).1 hm.gen) P₀.L.isLB P'₀.L.isLB
    (SplitTorus.bcMap f X) hcc σ.s σ.gen

  let up : ∀ T : Over (Sp k'), (T ⟶ splitTorus (Sp k') X) →* (Over.mk (T.hom ≫ f) ⟶ splitTorus (Sp k) X) :=
    fun T => toBaseHom (hw := SplitTorus.bcMap_hom f X) (fun T x y => Over.OverMorphism.ext
      (SplitTorus.mul_left_bcMap f X T x y _ _ rfl rfl).symm) T
  have up_left : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x).left = x.left ≫ SplitTorus.bcMap f X :=
    fun _ => rfl
  have up_comp : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x ≫ i).left = (x ≫ i₁).left ≫ β₀ :=
    fun x => by rw [Over.comp_left, up_left, Category.assoc, hi', Over.comp_left, Category.assoc]
  have vrel : ∀ (T : Over (Sp k')) (z : T.left) (C₀ C), Good P'₀.L.L z C₀ → Good P₀.L.L z C →
      ∀ x : T ⟶ splitTorus (Sp k') X, val σ.s (up T x).left z C =
        gw w₀ (x ≫ i₁).left z (C ((x ≫ i₁).left ≫ β₀)) (C₀ (x ≫ i₁).left) *
          (gw w₀ (1 : T ⟶ G'₀).left z (C ((1 : T ⟶ G'₀).left ≫ β₀)) (C₀ (1 : T ⟶ G'₀).left))⁻¹ *
          val a x.left z C₀ := fun T z C₀ C hC₀ hC x =>
    (CubTransport.val_pmaps hcc H x.left hC hC₀).trans
      (congrArg₂ (· * ·) (prod_triv (i := i₁) x (fun q => gw w₀ q z (C (q ≫ β₀)) (C₀ q))) rfl)

  obtain ⟨r, hr⟩ := TorusCoord.exists_ratio P'₀.L.isLB (fun _ _ _ => rfl) σ₁.s σ₁.gen a ha
  have a_one : ∀ (T : Over (Sp k')) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (1 : T ⟶ splitTorus (Sp k') X).left z C₀ = 1 := fun T z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have e := vrel T z C₀ C hC₀ hC 1
    rw [map_one, σ.val_one hC, MonObj.one_comp, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm
  have a_cub : ∀ (T : Over (Sp k')) (x y u : T ⟶ splitTorus (Sp k') X) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (x * y * u).left z C₀ * val a x.left z C₀ * val a y.left z C₀ * val a u.left z C₀ =
        cubV P'₀.c z C₀ (x ≫ i₁) (y ≫ i₁) (u ≫ i₁) * val a (x * y).left z C₀ * val a (x * u).left z C₀ *
          val a (y * u).left z C₀ := fun T x y u z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have h₀ := σ.cub (Over.mk (T.hom ≫ f)) (up T x) (up T y) (up T u) z C hC
    have hup : ∀ q : T ⟶ splitTorus (Sp k') X, up T q ≫ i = toBase hw (q ≫ i₁) :=
      fun q => Over.OverMorphism.ext (up_comp q)
    simp only [← map_mul, hup] at h₀
    have c := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.2 (x ≫ i₁) (y ≫ i₁) (u ≫ i₁)
    simp only [← MonObj.mul_comp] at c
    exact cub_down_alg h₀ c (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
      (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
  obtain ⟨ψ, hψ⟩ := exists_char_of_cub r (fun T x y u z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      exact ratio_alg (a_cub T x y u z C₀ hC₀) (σ₁.cub T x y u z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀)
        (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀))
    (fun T z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      have e := hr _ (1 : T ⟶ splitTorus (Sp k') X).left z C₀ hC₀
      rw [σ₁.val_one hC₀, a_one T z C₀ hC₀, _root_.mul_one] at e
      exact e.symm)

  have key : ∀ (T : Over (Sp k')) (x : T ⟶ splitTorus (Sp k') X) (z : T.left),
      gm (𝟙 T.left) z ⊤ (chV x κ) = gm (𝟙 T.left) z ⊤ (chV x (ψ + ψ)) := fun T x z => by
    obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have hchv : chV (up T x) κ = chV x κ := Units.ext (by
      rw [chV_val, chV_val, up_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
        bcMap_charUnit])
    have e₁ := hκ (Over.mk (T.hom ≫ f)) (up T x) z C hC
    rw [← map_inv, up_comp, vrel T z C₀ C hC₀ hC, vrel T z C₀ C hC₀ hC, hchv] at e₁
    have s₁ := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.1 (x ≫ i₁)
    rw [← GrpObj.inv_comp] at s₁
    have ev := hσ₁ T x z C₀ hC₀
    rw [hr _ _ z C₀ hC₀, hr _ _ z C₀ hC₀, hψ, hψ, chV_inv, map_inv] at ev
    exact (even_alg e₁ s₁ ev).trans (by rw [chV_add, map_mul])
  have hκψ : κ = ψ + ψ := by
    apply SplitTorusHom.charUnit_injective (S := Sp k')
    have e : chV (𝟙 (splitTorus (Sp k') X)) κ = chV (𝟙 (splitTorus (Sp k') X)) (ψ + ψ) :=
      unit_ext fun z _ => key _ _ z
    have e' := congrArg Units.val e
    rwa [chV_val, chV_val, Over.id_left, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply,
      RingHom.id_apply] at e'
  refine ⟨ψ, fun T t z J hJ => ?_⟩
  rw [σ.val_twist ψ _ hJ, σ.val_twist ψ _ hJ, hκ T t z J hJ, hκψ, chV_inv, chV_add, map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwistCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CoeffDenom

theorem dvd_pow_of_ne_zero_of_not_isUnit {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {d π : V} (hd : d ≠ 0) (hπ : π ≠ 0) (hπu : ¬ IsUnit π) : ∃ N : ℕ, d ∣ π ^ N := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  obtain ⟨b, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ hϖ
  have hb : b ≠ 0 := by
    rintro rfl
    exact hπu (by rw [hu', pow_zero, mul_one]; exact u'.isUnit)
  refine ⟨a, ?_⟩
  rw [hu, hu', mul_pow, ← pow_mul]
  refine (Units.isUnit u).mul_left_dvd.2 (Dvd.dvd.mul_left ?_ _)
  exact pow_dvd_pow ϖ (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb))

end GlobalTheory.CoeffDenom

namespace GlobalTheory.CoeffDenom


open GlobalTheory.LamT in
theorem exists_clear_coeff_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 → ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
    ∃ x : 𝓞 z.K, x ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K ((x : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he p
  classical
  obtain ⟨T, iK, hT, hiK⟩ := _root_.GlobalTheory.exists_cdvr_completion_integral_iff z.K p
  obtain ⟨M⟩ := (_root_.GlobalTheory.LamT.locMod_exists E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  choose c0 hc0 using fun (b : E →+* ℂ) (j : Fin (Dw.mult b)) =>
    LocClause.exists_isLocGen p (z.ℓ (z.e ⟨b, j⟩)).I
  let cl : ∀ b : E →+* ℂ, Fin (Dw.mult b) → T.Fr := fun b j => iK (c0 b j)
  have hcl : ∀ b j i, cl b j * (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i =>
    GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i _ (hc0 b j)
  have hloc := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg
    hL hS cl hcl

  let D : ℤ := ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩))
  let S : Finset (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := Formalism.L2.LamCM.FrVar Dw.mult) D.toNat).toFinset
  let τ : T.Fr := ∏ b, (g b).det ^ k b
  let yμ : (Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ) → T.Fr := fun μ => τ * (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v)⁻¹
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors T.V) (S.image yμ)

  obtain ⟨ϖ, hϖp, hϖ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.ne_bot
  have hϖv : p.valuation z.K (ϖ : z.K) < 1 := (p.valuation_lt_one_iff_mem ϖ).2 hϖp
  obtain ⟨π, hπ⟩ := (hiK (ϖ : z.K)).2 (p.valuation_le_one ϖ)
  have hϖK : (ϖ : z.K) ≠ 0 := fun h => hϖ0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at hπ
    exact hϖK hπ
  have hπu : ¬ IsUnit π := by
    rintro ⟨u, rfl⟩
    have h1 : iK ((ϖ : z.K)⁻¹) ∈ Set.range (algebraMap T.V T.Fr) := by
      refine ⟨((u⁻¹ : T.Vˣ) : T.V), ?_⟩
      rw [map_inv₀, ← hπ]
      exact map_units_inv (algebraMap T.V T.Fr) u
    have h2 := (hiK _).1 h1
    rw [map_inv₀] at h2
    have h0 : p.valuation z.K (ϖ : z.K) ≠ 0 := (Valuation.ne_zero_iff _).2 hϖK
    have h4 : (1 : _) ≤ p.valuation z.K (ϖ : z.K) :=
      calc (1 : _) = p.valuation z.K (ϖ : z.K) * (p.valuation z.K (ϖ : z.K))⁻¹ := (mul_inv_cancel₀ h0).symm
        _ ≤ p.valuation z.K (ϖ : z.K) * 1 := by gcongr
        _ = p.valuation z.K (ϖ : z.K) := mul_one _
    exact absurd hϖv (not_lt.2 h4)
  obtain ⟨N, t, hNt⟩ := dvd_pow_of_ne_zero_of_not_isUnit (nonZeroDivisors.ne_zero d.2) hπ0 hπu
  refine ⟨ϖ ^ N, pow_ne_zero _ hϖ0, ?_⟩
  intro F hF hv G hG μ
  by_cases hμ : AddMonoidAlgebra.coeff G μ = 0
  · simp [hμ]
  have hG1 : ∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K),
      (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 z.y y' →
      (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := fun y'' Y hY hc =>
    hG y'' Y 1 hY (by rw [Units.val_one]; exact hc)
  have hdeg := _root_.GlobalTheory.FrameHom.frPoly_secZ_degree_eq E H Dw l Xo c z.K z.y e k he F hF G hG1 μ hμ
  have hμS : μ ∈ S := by
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  obtain ⟨w, hw⟩ := hloc F hF hv G hG1 μ
  obtain ⟨r, hr⟩ := hd (yμ μ) (Finset.mem_image_of_mem yμ hμS)
  apply (hiK _).1
  have hP : (∏ v : Formalism.L2.LamCM.FrVar Dw.mult, cl v.1 v.2.2 ^ μ v) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ ((map_ne_zero iK).2 (hc0 v.1 v.2.2).1)
  have hc : iK (AddMonoidAlgebra.coeff G μ) = yμ μ * algebraMap T.V T.Fr w := by
    simp only [yμ]
    rw [mul_comm τ, mul_assoc, ← hw]
    field_simp
  rw [Algebra.smul_def] at hr
  have e1 : (((ϖ ^ N : 𝓞 z.K)) : z.K) = (ϖ : z.K) ^ N := by simp
  refine ⟨t * r * w, ?_⟩
  rw [map_mul iK, e1, map_pow, ← hπ, ← map_pow, hNt, hc]
  simp only [map_mul]
  rw [hr]
  ring

end GlobalTheory.CoeffDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPowTransitionOfFrobeniusKillsClass
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FrobKill

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}}
  {s : X ⟶ Sp R}

abbrev tU (s : X ⟶ Sp R) (U : AffOp X) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop)


include hR in
theorem cast_sec (U : X.Opens) : (p : Sec s U) = 0 := by
  rw [← map_natCast (algebraMap R (Sec s U)), hR, map_zero]

abbrev resHom (s : X ⟶ Sp R) {U V : AffOp X} (a : U ⟶ V) : tU s U ⟶ tU s V :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := tU s V) (Sec.res s (leOfHom a.unop))
    (affPt_res s (leOfHom a.unop))

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta (U : AffOp X) : tU s U ⟶ h.obj (tU s U) :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := h.obj (tU s U))
    { frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) with
      commutes' := fun r ↦ by
        show frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) (algebraMap R (Sec s U.unop.1) r) = _
        rw [frobR_apply]
        change _ = algebraMap R (Sec s U.unop.1) (frobR p R hR r)
        rw [frobR_apply, map_pow] }
    (by
      have h0 : (p : Γ(Sp (Sec s U.unop.1), ⊤)) = 0 :=
        GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_sec p hR U.unop.1)
      change spMap (frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1)) ≫ affPt s U.unop =
        affPt s U.unop ≫ GlobalTheory.VB.frob X p hX
      rw [← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX _ h0])

theorem eta_φ (U : AffOp X) (b : Sec s U.unop.1) : (eta p hR h U).φ b = b ^ p :=
  frobR_apply p _ (cast_sec p hR U.unop.1) b

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'

end GlobalTheory.CechDR.FrobKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomCyclotomicAwayToFieldPrimitiveRootStatement
section
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_cyclotomicAway_to_field_primitiveRoot : ∀ (M : ℕ), M ≠ 0 → ∀ (K : Type) [Field K] (y : K), IsPrimitiveRoot y M → IsUnit (M : K) →
  ∃ β : cycAway M →+* K, β (zetaAway M) = y := by
  first | (exact @GlobalTheory.CycLift.exists_hom_to_field) | (exact GlobalTheory.CycLift.exists_hom_to_field) | (intros; apply GlobalTheory.CycLift.exists_hom_to_field  <;> assumption)
end

