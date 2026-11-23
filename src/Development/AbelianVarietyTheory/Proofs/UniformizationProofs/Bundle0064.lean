module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.PsiScalUnit

theorem exists_ratio {X Y : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val u r z J = gm r z ⊤ w * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hF U h, mul_inv_cancel])
    (LB.mulGen M _ _ _ _ u (LB.invGen M _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← mul_inv_eq_iff_eq_mul, ← val_inv, ← val_mul hJ, ← hv Z r z J hJ, val_of t r z J PEmpty.elim (fun k => k.elim)]
  exact (gm_res r z le trivial _).symm

variable {V : Type} [CommRing V] [IsDomain V]

def ev (z : (TK V).left) : FractionRing V →+* (TK V).left.presheaf.stalk z :=
  ((TK V).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem ev_eq (z : (TK V).left) (k : FractionRing V) :
    gs (𝟙 _) z ⊤ (scal (𝟙 (TK V) : TK V ⟶ TK V).left k) = ev z k := by
  rw [gs_eq _ z ⊤ trivial]; rfl

theorem ev_unit (z : (TK V).left) (w : Γ(Spec (CommRingCat.of V), ⊤)ˣ) :
    ∃ u : Vˣ, (gm (jK V) z ⊤ w).val = ev z (algebraMap V (FractionRing V) u.val) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom w, ?_⟩
  rw [← gs_unit _ z ⊤ trivial, gs_eq _ z ⊤ trivial]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at e
  exact congrArg ((TK V).left.presheaf.germ ⊤ z trivial).hom e.symm

theorem c_left (D : DegPre V) (χ : D.X) : (D.c χ).left = (DVR.cP D (𝟙_ _) χ).left := by
  rw [DVR.cP, toUnit_unit, Category.id_comp]

theorem exists_setup (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) :
    ∃ (z : (TK V).left) (J : _), Good D.P.L z J ∧ ∀ χ, val (D.psi χ) (𝟙 _) z J =
      Units.map (ev z).toMonoidHom (a χ) * val (ga χ) (toUnit (TK V)).left z J := by
  obtain ⟨z⟩ : Nonempty (TK V).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing V)))
  choose J hJ using fun χ : (TK V).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
  refine ⟨z, J, hJ, fun χ => Units.ext ?_⟩
  exact ((h χ).2 (TK V) (𝟙 _) z J hJ).trans (congrArg₂ (· * ·) (ev_eq z _) rfl)

theorem ev_inj (z : (TK V).left) : Function.Injective (ev z) := (ev z).injective

theorem cub_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hB : D.TauBimult) (x y w : D.X) :
    ∃ u : Vˣ, (a (x + y + w) * a x * a y * a w).val =
      algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + w) * a (y + w)).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have vτ : ∀ a b : D.X, val (D.tau a b) (𝟙 _) z J =
      val (D.psi (a + b)) (𝟙 _) z J * (val (D.psi a) (𝟙 _) z J)⁻¹ * (val (D.psi b) (𝟙 _) z J)⁻¹ *
        (val D.rigK (𝟙 _) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have vρ : val D.rigK (𝟙 _) z J = val D.rig (toUnit (TK V)).left z J := by
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp]
  have vc : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 x y w)) (𝟙 _) z J =
      cubV D.cub z J (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w) := by
    refine (val_cub D.cub (𝟙 (TK V)) hJ (DVR.cP D _ x) (DVR.cP D _ y) (DVR.cP D _ w)).trans ?_
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB x y w) (𝟙 _)).trans (val_mul hJ _ _ _))
  rw [vc, vτ, vτ, vτ, vρ] at e
  simp only [hψ] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have p₁ := prod_cub (DVR.cP D (𝟙_ _) x) (DVR.cP D _ y) (DVR.cP D _ w) f
      have q : eSec D.P.A = (1 : 𝟙_ _ ⟶ D.P.A).left := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
      refine Eq.trans ?_ (DVR.prod_sum₂ (U := U) _ rfl p₁).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c_left, DVR.cPoint_add, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y)).1 (h (x + w)).1) (h (y + w)).1)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (x + y + w)).1 (h x).1) (h y).1) (h w).1)
      D.rig_gen) (DVR.pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε _ D.cub.isGen
        (lift (DVR.cP D (𝟙_ _) x) (lift (DVR.cP D (𝟙_ _) y) (DVR.cP D (𝟙_ _) w))).left))
  have e₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)).symm.trans
    ((hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_mul hJ _ _ _) rfl)) rfl)) rfl))
      (val_cub D.cub (toUnit (TK V)) hJ _ _ _)))))
  rw [DVR.comp_cP, DVR.comp_cP, DVR.comp_cP] at e₂
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (x + y + w) * a x * a y * a w) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a (x + y) * a (x + w) * a (y + w)) := by
    simp only [map_mul]
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem even_part (D : DegPre V)
    (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)))
    (a : D.X → (FractionRing V)ˣ) (h : PsiScal D ga a) (hE : D.PsiEven) (x : D.X) :
    ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val := by
  obtain ⟨z, J, hJ, hψ⟩ := exists_setup D ga a h
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE x) (𝟙 _))
  rw [hψ, hψ, Category.id_comp] at e
  obtain ⟨W, hW⟩ := exists_ratio D.P.isLB (fun U _ f => by
      have q : (D.c x).left ≫ (ι[D.P.A]).left = (D.c (-x)).left := by
        have h0 : DVR.cP D (𝟙_ _) 0 = 1 := by simpa using DVR.cPoint_nsmul D (𝟙_ _) 0 x
        have h1 := DVR.cPoint_add D (𝟙_ _) (-x) x
        rw [neg_add_cancel, h0] at h1
        rw [c_left, c_left, eq_inv_of_mul_eq_one_left h1.symm, ← Over.comp_left]
        rfl
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (h x).1 (DVR.mulGen_isGen _ _ _ _ _ _ _ (h (-x)).1 (DVR.pullGen_isGen D.P.L _ _ _ D.sym_gen (D.c x).left))
  have e₂ := (hW _ (toUnit (TK V)).left z J hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
  obtain ⟨u, hu⟩ := ev_unit z W
  refine ⟨u, ev_inj z ?_⟩
  rw [map_mul (ev z) (algebraMap _ _ _), ← hu]
  have : Units.map (ev z).toMonoidHom (a (-x)) =
      gm (toUnit (TK V)).left z ⊤ W * Units.map (ev z).toMonoidHom (a x) := by
    have e' : Units.map (ev z).toMonoidHom (a (-x)) * val (ga (-x)) (toUnit (TK V)).left z J *
        val D.sym ((toUnit (TK V)).left ≫ (D.c x).left) z J =
        Units.map (ev z).toMonoidHom (a x) * val (ga x) (toUnit (TK V)).left z J := e
    apply Additive.ofMul.injective
    have a₁ := congrArg Additive.ofMul e'
    have a₂ := congrArg Additive.ofMul e₂
    simp only [ofMul_mul] at a₁ a₂ ⊢
    linear_combination (norm := abel) a₁ + a₂
  exact congrArg Units.val this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing V)ˣ), PsiScal D ga a → (D.TauBimult → ∀ x y z, ∃ u : Vˣ, (a (x + y + z) * a x * a y * a z).val = algebraMap V (FractionRing V) u.val * (a (x + y) * a (x + z) * a (y + z)).val) ∧ (D.PsiEven → ∀ x, ∃ u : Vˣ, (a (-x)).val = algebraMap V (FractionRing V) u.val * (a x).val) :=
  fun _ _ _ _ D ga a h => ⟨cub_part D ga a h, even_part D ga a h⟩

end GlobalTheory.PsiScalUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RedIffReduction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.UU.RedOnto

open GlobalTheory.FormalPoint

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)
  {T : Over (Spec (CommRingCat.of R))}

def Coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (y : Z ⟶ (thickObj R I e G).left) : Prop :=
  y ≫ (U.gt e).pG.left = r ≫ g.b.left ∧
    ∀ (χ : D.X) (z : Z) (J), Good D.P.L z J → val ((U.gt e).t χ) y z J = val (g.s χ) r z J

variable {U}

theorem Coords.comp {e : ℕ} {g : GtPt D T} {Z W : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (k : W ⟶ Z) :
    Coords U e g (k ≫ r) (k ≫ y) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, h1, Category.assoc], fun χ w J hJ => ?_⟩

  have hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ ((U.gt e).t χ) y) (LB.pullGen D.P.L _ _ (g.s χ) r) :=
    corr_of_val D.P.isLB fun z J' hJ' => by
      rw [val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp]
      exact h2 χ z J' hJ'
  have hk := val_corr hJ hc k
  rwa [val_pull hJ, val_pull hJ] at hk

theorem Coords.unique {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y y' : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) (h' : Coords U e g r y') : y = y' := by
  unfold Coords at h h'
  exact GlobalTheory.TorusCoord.ext_of_val (U.gt e) y y' (h.1.trans h'.1.symm)
    fun χ w J hJ => (h.2 χ w J hJ).trans (h'.2 χ w J hJ).symm


variable (U) in
theorem exists_coords (e : ℕ) (g : GtPt D T) {Z : Scheme.{0}} (r : Z ⟶ T.left)
    (σ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (h : σ ≫ thick R I e = r ≫ T.hom) :
    ∃ y, Coords U e g r y := by
  obtain ⟨x, hx1, hx2⟩ := GlobalTheory.FormalPoint.exists_point (U.gt e) g (Z := Over.mk σ)
    (Over.homMk r h.symm)
  refine ⟨x, ?_⟩
  unfold Coords
  refine ⟨hx1, fun χ z J hJ => ?_⟩
  have hv := hx2 χ Z (𝟙 Z) z J hJ
  rw [Category.id_comp, Category.id_comp] at hv
  exact hv

theorem Coords.succ {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    Coords U (e + 1) g r (y ≫ thickMap R I e G) := by
  unfold Coords at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Category.assoc, U.gt_q e]; exact h1, fun χ z J hJ => ?_⟩
  rw [← val_pull hJ ((U.gt (e + 1)).t χ) (thickMap R I e G) y, val_corr hJ (U.gt_t e χ) y]
  exact h2 χ z J hJ

private theorem comp_hom_eq_of_coords {e : ℕ} {g : GtPt D T} {Z : Scheme.{0}} {r : Z ⟶ T.left}
    {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    r ≫ T.hom = y ≫ (thickObj R I e G).hom ≫ thick R I e := by
  obtain ⟨h1, -⟩ := h
  have e1 : g.b.left ≫ D.P.A.hom = T.hom := Over.w g.b
  have e2 : (U.gt e).pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (U.gt e).pG
  calc r ≫ T.hom = (r ≫ g.b.left) ≫ D.P.A.hom := by rw [Category.assoc, e1]
    _ = (y ≫ (U.gt e).pG.left) ≫ D.P.A.hom := by rw [h1]
    _ = y ≫ (thickObj R I e G).hom ≫ thick R I e := by rw [Category.assoc, e2]

theorem comp_fstG_eq {g : GtPt D T} {x : T ⟶ G} (hx : U.Red x g) {e : ℕ} {Z : Scheme.{0}}
    {r : Z ⟶ T.left} {y : Z ⟶ (thickObj R I e G).left} (h : Coords U e g r y) :
    y ≫ (fstG I e G).left = r ≫ x.left := by
  have hb := comp_hom_eq_of_coords h
  have ex : x.left ≫ G.hom = T.hom := Over.w x

  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (Z := Over.mk (y ≫ (thickObj R I e G).hom))
    (Over.homMk (r ≫ x.left) (by
      show (r ≫ x.left) ≫ G.hom = (y ≫ (thickObj R I e G).hom) ≫ thick R I e
      rw [Category.assoc, ex, hb, Category.assoc]))
  have ha' : a.left ≫ (fstG I e G).left = r ≫ x.left := congrArg CommaMorphism.left ha
  have hc : Coords U e g r a.left := hx e Z r a.left ha'
  rw [← Coords.unique hc h]
  exact ha'

end Level

section Complete

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {S : Type} [CommRing S] {φ : R →+* S} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreU I D A G)

theorem red_iff_reduction (g : GtPt D (Over.mk (spMap φ))) (x : Over.mk (spMap φ) ⟶ G) :
    U.Red x g ↔ ∀ e, Coords U e g (adicLevelι (I.map φ) (e + 1)) (reduction I x e) := by
  constructor
  · intro hx e
    exact hx e _ _ _ (GlobalTheory.FormalPoint.reduction_fstG I x e)
  · intro h e Z r xe hxe
    have ex : x.left ≫ G.hom = spMap φ := Over.w x
    have ef : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
    have hs : r ≫ spMap φ = (xe ≫ (thickObj R I e G).hom) ≫ thick R I e := by
      rw [← ex, ← Category.assoc, ← hxe]
      simp only [Category.assoc, ef]

    obtain ⟨l, hl⟩ := GlobalTheory.FormalPoint.exists_factor_level I φ r _ hs
    have hc := Coords.comp (h e) l
    have hred : l ≫ GlobalTheory.FormalPoint.reduction I x e = xe := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, GlobalTheory.FormalPoint.reduction_fstG, ← Category.assoc,
        hl, hxe]
    rw [hl, hred] at hc
    exact hc

variable [IsLocalRing S]


variable {U} in
theorem red_unique [IsHausdorff (I.map φ) S] {g : GtPt D (Over.mk (spMap φ))}
    {x x' : Over.mk (spMap φ) ⟶ G} (h : U.Red x g) (h' : U.Red x' g) : x = x' := by
  have hr := (red_iff_reduction U g x).1 h
  have hr' := (red_iff_reduction U g x').1 h'
  apply Over.OverMorphism.ext
  apply GlobalTheory.hom_ext_of_isHausdorff (I.map φ)
  intro n
  rw [← GlobalTheory.FormalPoint.reduction_fstG I x n, ← GlobalTheory.FormalPoint.reduction_fstG I x' n, Coords.unique (hr n) (hr' n)]

theorem existsUnique_red [IsAdicComplete (I.map φ) S] (g : GtPt D (Over.mk (spMap φ))) :
    ∃! x : Over.mk (spMap φ) ⟶ G, U.Red x g := by
  have hy : ∀ e, ∃ y, Coords U e g (adicLevelι (I.map φ) (e + 1)) y := fun e =>
    exists_coords U e g (adicLevelι (I.map φ) (e + 1)) (GlobalTheory.FormalPoint.levelMap I φ e)
      (GlobalTheory.FormalPoint.levelMap_thick I φ e)
  choose y hy using hy
  have htf : ∀ n, thickMap R I n G ≫ (fstG I (n + 1) G).left = (fstG I n G).left := by
    intro n
    unfold thickMap fstG
    simp only [pullback.map, Category.comp_id, Over.homMk_left, pullback.lift_fst]

  have hcomp : ∀ n, GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) = y n ≫ thickMap R I n G := by
    intro n
    refine Coords.unique ?_ (Coords.succ (hy n))
    have hk := Coords.comp (hy (n + 1)) (GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)))
    rwa [GlobalTheory.adicLevelMap_ι] at hk
  have hf : GlobalTheory.IsAdicFamily (I.map φ) (fun n => y n ≫ (fstG I n G).left) := by
    intro n
    show GlobalTheory.adicLevelMap (I.map φ) (Nat.le_succ (n + 1)) ≫ y (n + 1) ≫ (fstG I (n + 1) G).left =
      y n ≫ (fstG I n G).left
    rw [← Category.assoc, hcomp n, Category.assoc, htf n]
  have hs : ∀ n, (y n ≫ (fstG I n G).left) ≫ G.hom = adicLevelι (I.map φ) (n + 1) ≫ spMap φ := by
    intro n
    have ef : (fstG I n G).left ≫ G.hom = (thickObj R I n G).hom ≫ thick R I n := Over.w (fstG I n G)
    rw [Category.assoc, ef]
    exact (comp_hom_eq_of_coords (hy n)).symm

  obtain ⟨x₀, ⟨hx₀, hxn⟩, -⟩ := GlobalTheory.existsUnique_over_of_isAdicFamily (spMap φ) G.hom hf hs
  have hred : U.Red (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) g := by
    refine (red_iff_reduction U g _).2 fun e => ?_
    have he : GlobalTheory.FormalPoint.reduction I (Over.homMk x₀ hx₀ : Over.mk (spMap φ) ⟶ G) e = y e := by
      rw [← cancel_mono (fstG I e G).left, GlobalTheory.FormalPoint.reduction_fstG]
      exact hxn e
    rw [he]
    exact hy e
  exact ⟨_, hred, fun x' hx' => red_unique hx' hred⟩

end Complete

theorem main : (AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ g : GtPt D (TA V W), ∃! x : TA V W ⟶ G, U.Red x g) := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW g
  obtain ⟨-, -, -, -, hc⟩ := hW
  exact existsUnique_red (φ := algebraMap V W) U g

end GlobalTheory.UU.RedOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultPsiEvenOverExtensionField
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.TauValues

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem comp_cT {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) (χ : D.X) :
    κ ≫ toUnit (TK R) ≫ D.c χ = cT D T χ := by
  rw [← Category.assoc, comp_toUnit]

theorem val_rigK {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val D.rigK κ.left z J = rigV D z J := by
  refine (val_pull hJ _ _ _).trans ?_
  have e : κ.left ≫ (toUnit (TK R)).left = T.hom := by
    rw [← Over.comp_left, comp_toUnit]; rfl
  exact congrArg (fun q : T.left ⟶ Spec (CommRingCat.of R) =>
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig q z J) e

theorem bimult_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (a b m : D.X) :
    val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J ↔
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + b) m)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m))) κ.left z J =
      val (LB.mulGen D.P.L _ _ _ _ (D.tau a m) (D.tau b m)) κ.left z J := by
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left z J =
      cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) := by
    refine (val_cub D.cub κ hJ (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c m)).trans ?_
    rw [comp_cT, comp_cT, comp_cT]
  have l := (val_mul hJ (D.tau (a + b) m)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) c)
  have r := (val_mul hJ (D.tau a m) (D.tau b m) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) (val_tau D κ.left hJ _ _))
  rw [val_rigK D κ hJ] at l r
  rw [l, r]
  constructor <;> intro h <;> apply Additive.ofMul.injective <;> have e := congrArg Additive.ofMul h <;>
    simp only [ofMul_mul, ofMul_inv] at e ⊢ <;> linear_combination (norm := abel) e

theorem val_even {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (m : D.X) :
    val (LB.mulGen D.P.L _ _ _ _ (D.psi (-m)) (LB.pullGen D.P.L _ _ D.sym (D.xK m))) κ.left z J =
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J := by
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans ?_))
  have e : κ.left ≫ D.xK m = (cT D T m).left := by
    rw [← comp_cT D κ m]; rfl
  rw [e]

theorem bimult_iff' {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ a b m : D.X,
      val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J) ↔
    D.TauBimult :=
  ⟨fun h a b m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (bimult_iff D κ hJ a b m).1 (h z J hJ a b m),
    fun h _ _ hJ a b m => (bimult_iff D κ hJ a b m).2 (val_corr hJ (h a b m) κ.left)⟩

theorem even_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ m : D.X,
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J = val (D.psi m) κ.left z J) ↔ D.PsiEven :=
  ⟨fun h m => corr_of_val_flat_surjective κ.left D.P.isLB fun z J hJ => (val_even D κ hJ m).trans (h z J hJ m),
    fun h _ _ hJ m => (val_even D κ hJ m).symm.trans (val_corr hJ (h m) κ.left)⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F], ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ a b m : D.X, val (Z := (TF (R := R) F).left) (D.psi (a + b + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J * rigV D z J * cubV D.cub z J (cT D _ a) (cT D _ b) (cT D _ m) = val (Z := (TF (R := R) F).left) (D.psi (a + b)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (a + m)) (jFK (R := R) F) z J * val (Z := (TF (R := R) F).left) (D.psi (b + m)) (jFK (R := R) F) z J) ↔ D.TauBimult) ∧ ((∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ m : D.X, val (Z := (TF (R := R) F).left) (D.psi (-m)) (jFK (R := R) F) z J * val D.sym (cT D (TF (R := R) F) m).left z J = val (Z := (TF (R := R) F).left) (D.psi (m)) (jFK (R := R) F) z J) ↔ D.PsiEven) := by
  intro R _ _ D F _ _
  let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hκ : κ.left = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)) := rfl
  have : Flat κ.left := by
    rw [hκ]
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField (FractionRing R)) _)
  have : Surjective κ.left := by
    have : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
    exact ⟨fun y => ⟨(default : PrimeSpectrum F), Subsingleton.elim _ _⟩⟩
  exact ⟨bimult_iff' D κ, even_iff D κ⟩

end GlobalTheory.TauValues
end

