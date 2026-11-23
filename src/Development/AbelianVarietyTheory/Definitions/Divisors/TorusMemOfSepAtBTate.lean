module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart.SepBModel

theorem gm_field {W : Type} [Field W] {Z : Scheme.{0}} (r : Z ⟶ Sp W) (z : Z) (U : (Sp W).Opens) (h : r z ∈ U)
    (a : Γ(Sp W, U)ˣ) : ∃ x : Wˣ, gm r z U a = gm r z ⊤ (unitOn x) := by
  obtain rfl : U = ⊤ := top_unique fun y _ => by rwa [Subsingleton.elim y (r z)]
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).hom.hom.toMonoidHom a, congrArg _ (Units.ext ?_)⟩
  exact ((Scheme.ΓSpecIso (CommRingCat.of W)).hom_inv_id_apply a.val).symm

theorem gm_spMap {W V : Type} [CommRing W] [CommRing V] (f : W →+* V) (z : Sp V) (x : Wˣ) :
    gm (spMap f) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn (Units.map f.toMonoidHom x)) := by
  have e : unitOn (Units.map f.toMonoidHom x) = pullU (spMap f) ⊤ (unitOn x) := by
    apply Units.ext
    exact congrArg (fun q => q.hom (x : W)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  rw [e]
  exact (gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn x)).symm

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] (z : Sp V) {x y : Vˣ}
    (h : gm (𝟙 (Sp V)) z ⊤ (unitOn x) = gm (𝟙 (Sp V)) z ⊤ (unitOn y)) : x = y := by
  have h1 := congrArg Units.val h
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at h1
  have h2 := germ_injective_of_isIntegral (Sp V) (U := ⊤) z trivial h1
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv).1 h2)





theorem lbIso_two {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (φ : Y ⟶ X) (r : Z ⟶ Y) :
    LBIso (L.pull (r ≫ φ)) ((L.pull φ).pull r) := by
  have h : LBIso L L := by
    refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
    refine (gm_res (𝟙 X) y _ hy _).trans (Eq.symm ?_)
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div L L (𝟙 X) y p q hy) (gm_res (𝟙 X) y _ hy _))).trans ?_
    have e := (gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2).trans (gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2).symm
    exact (mul_right_comm _ _ _).trans (mul_inv_eq_of_eq_mul e)
  exact (LBIso.chartPull (Geo.Tor.chartPullPull L φ φ rfl) (Geo.Tor.chartPullPull L φ φ rfl) h).chartPull
    (chartPullSame L (fun _ => r ≫ φ) (fun _ => φ) _ r fun _ => rfl) (Geo.Tor.chartPullPull (L.pull φ) r r rfl)



variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem stalkMap_gm {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (r z) ∈ U) (a : Γ(X, U)ˣ) :
    Units.map (r.stalkMap z).hom.toMonoidHom (gm f (r z) U a) = gm (r ≫ f) z U a := by
  apply Units.ext
  rw [gm_val (r ≫ f) z U h]
  show (r.stalkMap z).hom (gm f (r z) U a).val = _
  rw [gm_val f (r z) U h]
  exact Scheme.Hom.germ_stalkMap_apply r (f ⁻¹ᵁ U) z h _


end GlobalTheory.UChart.SepBModel
