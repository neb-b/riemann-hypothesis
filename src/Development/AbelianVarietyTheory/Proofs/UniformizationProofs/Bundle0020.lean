module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIsoAppTopOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionTotal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange

theorem globalFns : GlobalFnsSt :=
  GlobalFunctions.globalFns_of forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth

variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)

def toBK : DegPre.BF D F ⟶ DegPre.BF D F' := lift (fst _ _ ≫ θ) (snd _ _)

theorem toBK_fst : toBK θ D ≫ fst _ _ = fst _ _ ≫ θ := lift_fst _ _

theorem toBK_prB : toBK θ D ≫ DegPre.prB D F' = DegPre.prB D F := lift_snd _ _

theorem famφ_eq (α : D.X) (i : Fin 4) :
    DegPre.famφ D F α i = (toBK θ D).left ≫ DegPre.famφ D F' α i := by
  have e₀ := toBK_prB θ D
  have e₂ := comp_cP D (toBK θ D) α
  fin_cases i
  · exact congrArg (fun q => q.left) e₀.symm
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul (toBK θ D) (DegPre.prB D _) (cP D _ α)).trans
      (congrArg₂ (· * ·) e₀ e₂)).symm
  · exact congrArg (fun q => q.left) e₂.symm
  · exact congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toBK θ D)).symm

theorem trF_toBK (mu : D.X) :
    DegPre.trF D F mu ≫ toBK θ D = toBK θ D ≫ DegPre.trF D F' mu := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, toBK_fst, Category.assoc, trF_eq, trF_eq, tr_fst, toBK_fst, ← Category.assoc, tr_fst]
  · refine (Category.assoc _ _ _).trans ((congrArg _ (toBK_prB θ D)).trans (Eq.trans ?_ (Category.assoc _ _ _).symm))
    rw [trF_eq, trF_eq, tr_pr]
    refine Eq.trans ?_ (congrArg (toBK θ D ≫ ·) (tr_pr D F' (cP D _ mu))).symm
    rw [MonObj.comp_mul, toBK_prB, comp_cP, comp_cP, comp_cP]

theorem exists_famPull (hθ : θ.left ≫ jFK (R := R) F' = jFK (R := R) F) (k : ℕ) (S : Fam D F' k) : ∃ S' : Fam D F k,
    ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (S'.s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := by
  have hp : (toBK θ D).left ≫ (DegPre.BF D F').hom =
      (DegPre.BF D F).hom ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) :=
    (Over.w _).trans ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm))
  let s : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k)) := fun α =>
    pullOver D.P.L (DegPre.famε k) hp (famφ_eq θ D α) (S.s α)
  have hs : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = sval (S.s α) (r ≫ (toBK θ D).left) z J := fun α Z r z J hJ =>
    sval_pullOver hp (famφ_eq θ D α) (S.s α) r hJ
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩, hs⟩
  have e₁ := (gen_fe globalFns k mu α).2 u hu hc _ (𝟙 _) y J hJ
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := F') globalFns k mu α
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (S.fe mu α u' hu' hc') _ (toBK θ D).left y J hJ
  rw [hv' u' hu' hc' _ (toBK θ D) y J hJ, ← Over.comp_left, ← trF_toBK, Over.comp_left] at e₂
  rw [Over.id_left] at e₁
  rw [hs _ _ _ y J hJ, hs _ _ _ y J hJ, Category.id_comp, Category.id_comp, e₂, e₁]
  have a : (toBK θ D ≫ fst _ _).left ≫ jFK (R := R) F' =
      (𝟙 (DegPre.BF D F) ≫ fst _ _).left ≫ jFK (R := R) F := by
    rw [toBK_fst, Category.id_comp, Over.comp_left, Category.assoc, hθ]
  rw [val_famMult _ hJ, val_famMult _ hJ, a, uVal, uVal, toBK_prB, comp_cP, comp_cP, comp_cP, comp_cP,
    Category.id_comp (DegPre.prB D F)]




end GlobalTheory.ExpansionTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftTest

theorem stalkMap_injective_of_flat {W Z : Scheme.{0}} (f : W ⟶ Z) [Flat f] (w : W) :
    Function.Injective (f.stalkMap w).hom := by
  have h := Flat.stalkMap f w
  algebraize [(f.stalkMap w).hom]
  have : IsLocalHom (algebraMap (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)) := f.toLRSHom.prop w
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Z.presheaf.stalk (f w)) (B := W.presheaf.stalk w)
  exact FaithfulSMul.algebraMap_injective (Z.presheaf.stalk (f w)) (W.presheaf.stalk w)

theorem gs_comp {W Z Y : Scheme.{0}} (f : W ⟶ Z) (r : Z ⟶ Y) (w : W) (U : Y.Opens) (h : r (f w) ∈ U)
    (a : Γ(Y, U)) : gs (f ≫ r) w U a = (f.stalkMap w).hom (gs r (f w) U a) := by
  rw [← gs_pull f r w U h, gs_eq f w (r ⁻¹ᵁ U) h, gs_eq r (f w) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (r ⁻¹ᵁ U) w h _).symm

theorem sval_eq_zero_of_flat {X Y Z W : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (f : W ⟶ Z) [Flat f] (w : W)
    (h : ∀ J, Good L w J → sval d (f ≫ r) w J = 0) (J) (hJ : Good L (f w) J) : sval d r (f w) J = 0 := by
  choose I hI using fun χ : W ⟶ X => exists_chart hL (χ w)
  have hm : r (f w) ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have e := sec_trans d (f ≫ r) w (j := fun k => J (r ≫ φ k)) hm (Good.mem hI φ (f ≫ r))
  have e0 : gs (f ≫ r) w (LB.wchart L φ (fun k => I ((f ≫ r) ≫ φ k))) (d.f (fun k => I ((f ≫ r) ≫ φ k))) = 0 := h I hI
  rw [e0, mul_zero] at e
  exact (map_eq_zero_iff _ (stalkMap_injective_of_flat f w)).1 ((gs_comp f r w _ hm _).symm.trans e)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p X L hL K _ φ ε d H Z r ⟨ρ, hρ⟩ z J hJ
  have := g.q_flat
  have := g.q_surj
  let b : Z ⟶ (thickObj R I e D.P.A).left :=
    pullback.lift (r ≫ p.left) ρ (by rw [Category.assoc, Over.w p, hρ])
  have hb : b ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ p.left := pullback.lift_fst _ _ _
  obtain ⟨w, rfl⟩ := (pullback.fst b g.q.left).surjective z
  refine sval_eq_zero_of_flat hL d r (pullback.fst b g.q.left) w (fun J' hJ' => ?_) J hJ
  refine H _ (pullback.snd b g.q.left) _ ?_ w J' hJ'
  rw [Category.assoc, ← hb, pullback.condition_assoc]
  rfl

end GlobalTheory.LiftTest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfFaithfullyFlatBase
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem levelff_stalkMap_injective {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  have h := Flat.stalkMap f x
  have hl : IsLocalHom (f.stalkMap x).hom := inferInstance
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (f x)) (B := X.presheaf.stalk x)
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem levelff_gs_comp {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (h : r (p z) ∈ U)
    (a : Γ(X, U)) : gs (p ≫ r) z U a = (p.stalkMap z).hom (gs r (p z) U a) := by
  rw [← gs_pull p r z U h, gs_eq p z (r ⁻¹ᵁ U) h, gs_eq r (p z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply p (r ⁻¹ᵁ U) z h _).symm

theorem sval_eq_zero_of_faithfullyFlat_base : ∀ (R W : Type) [CommRing R] [CommRing W] [Algebra R W] [Module.FaithfullyFlat R W] (I : Ideal R) (e : ℕ) (Y : Over (Spec (CommRingCat.of R))) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (ω : Z ⟶ Spec (CommRingCat.of W)), ω ≫ Spec.map (CommRingCat.ofHom (algebraMap R W)) = r ≫ Y.hom → (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0 := by
  intro R W _ _ _ _ I e Y X L hL K _ φ ε d H Z r hρ z J hJ
  let g : Spec (CommRingCat.of W) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom (algebraMap R W))
  have hg : Flat g ∧ Surjective g := by
    refine (flat_and_surjective_SpecMap_iff _).2 ?_
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  obtain ⟨_, _⟩ := hg
  let p : pullback (r ≫ Y.hom) g ⟶ Z := pullback.fst _ _
  have : Flat p := inferInstance
  have : Surjective p := inferInstance
  obtain ⟨z', rfl⟩ := p.surjective z
  obtain ⟨ρ, hρ⟩ := hρ
  choose J' hJ' using fun χ : pullback (r ≫ Y.hom) g ⟶ X => exists_chart hL (χ z')
  have h0 := H _ (p ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition.symm)
    ⟨p ≫ ρ, by rw [Category.assoc, hρ, Category.assoc]⟩ z' J' hJ'
  have hm : r (p z') ∈ LB.wchart L φ (fun k => J (r ≫ φ k)) := hJ.mem φ r
  have h1 := sec_trans d (p ≫ r) z' (j := fun k => J (r ≫ φ k)) hm (Good.mem hJ' φ (p ≫ r))
  have h2 : gs (p ≫ r) z' (LB.wchart L φ (fun k => J (r ≫ φ k))) (d.f (fun k => J (r ≫ φ k))) = 0 :=
    h1.trans ((congrArg _ h0).trans (mul_zero _))
  apply levelff_stalkMap_injective p z'
  rw [map_zero]
  exact (levelff_gs_comp p r z' _ hm _).symm.trans h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TranslationUnitMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_mul_cubN_add {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'

theorem translationUnit_mul :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e

end GlobalTheory
end

