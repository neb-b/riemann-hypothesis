module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem pt_eq (z z' : (TF (R := R) F).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum F) z z'

def cstH (z : (TF (R := R) F).left) : F →+* (TF (R := R) F).left.presheaf.stalk z :=
  ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

omit [IsDomain R] in
theorem cst_eq (z : (TF (R := R) F).left) (x : F) : cst F z x = cstH z x :=
  gs_eq (𝟙 _) z ⊤ trivial _

omit [IsDomain R] in
theorem cstH_surj (z : (TF (R := R) F).left) : Function.Surjective (cstH (R := R) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TF (R := R) F).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom hx⟩

omit [IsDomain R] in
theorem cstH_inj (z : (TF (R := R) F).left) : Function.Injective (cstH (R := R) z) :=
  (cstH (R := R) z).injective

omit [IsDomain R] in
theorem exists_pt : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩

theorem exists_good' {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

def trU {X Z : Scheme.{0}} (L : LB X) (z : Z) (J J' : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))

theorem val_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)

theorem sval_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    sval s r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k).val * sval s r z J' :=
  sec_trans s r z (hJ.mem φ r) (hJ'.mem φ r)

theorem exists_gen_pt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (y₀ : Y) (hY : ∀ y : Y, y = y₀) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨J, hJ⟩ := exists_good' hL y₀
  let j₀ : K → L.ι := fun k => J (𝟙 Y ≫ φ k)
  have h₀ : ∀ y : Y, (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j₀ := fun y => by
    rw [hY y]; exact hJ.mem φ (𝟙 Y)
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀ := fun j y hy => ⟨hy, h₀ y⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j j₀)) =
      trF φ ε (𝟙 Y) y j j₀ := fun j hj =>
    (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb L φ ε (𝟙 Y) y j j₀ hj (h₀ y))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h₀ y)).symm

theorem prod_line (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i = h (1 : TF (R := R) F ⟶ D.P.A).left ^ k * (h b.left ^ k)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

theorem isCoef_unique {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s} {x y : F}
    (hx : IsCoef k g w χ s x) (hy : IsCoef k g w χ s y) : x = y := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have e := (hx z J hJ).trans (hy z J hJ).symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_left_inj, cst_eq, cst_eq] at e
  exact cstH_inj z e

theorem coef_eq {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s : Fam D F k} {x : F}
    (hx : IsCoef k g w χ (s.s χ) x) : coef s g w χ = x :=
  isCoef_unique (Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) ⟨x, hx⟩) hx

theorem exists_isCoef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s) :
    ∃ x, IsCoef k g w χ s x := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨x, hx⟩ := cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val *
    (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)
  refine ⟨x, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'
  have a₂ := val_tr (g.isGen χ) (𝟙 _) hJ hJ'
  have a₃ := val_tr hw (𝟙 _) hJ hJ'
  have a₄ : rigV D (TF (R := R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left *
      rigV D (TF (R := R) F).hom z J' := by
    refine (val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
      (TF (R := R) F).hom hJ hJ').trans ?_
    rw [Fintype.prod_unique, zpow_one]; rfl
  rw [prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd] at a₁
  simp only [Category.id_comp] at a₂ a₃
  rw [prod_gt g.b χ (trU D.P.L z J J')] at a₂
  rw [prod_line k g.b (trU D.P.L z J J')] at a₃
  rw [cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem isCoef_coef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s : Fam D F k) :
    IsCoef k g w χ (s.s χ) (coef s g w χ) :=
  Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) (exists_isCoef g hw χ _)

theorem sval_lin {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (s s' : Fam D F k) (c : F) (χ : D.X) {z : (TF (R := R) F).left} {J}
    (hJ : Good D.P.L z J) : sval ((c • s + s').s χ) (lift (𝟙 (TF (R := R) F)) b).left z J =
      cst F z c * sval (s.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J +
        sval (s'.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J := by
  have hm := hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left
  refine (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)
  refine (gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]; rfl

theorem exists_frame_ratio {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w w' : Frm D F k b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (val w' (𝟙 _) z J' * (val w (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq z z'
    rw [cst_eq, hc, val_tr hw (𝟙 _) hJ hJ', val_tr hw' (𝟙 _) hJ hJ', ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem coef_basic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F), (∃ w : Frm D F k g.b, w.IsGen) ∧ (g.b = 1 → ∃ w : Frm D F k g.b, FrmOne w) ∧ ∀ w : Frm D F k g.b, w.IsGen → (∀ χ s, ∃! x, IsCoef k g w χ s x) ∧ (∀ (s s' : Fam D F k) (c : F) χ, coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ) ∧ (∀ w' : Frm D F k g.b, w'.IsGen → ∃ c : F, c ≠ 0 ∧ (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) ∧ ∀ (s : Fam D F k) χ, coef s g w' χ = c * coef s g w χ) ∧ ∀ (t : Multiplicative D.X →* Fˣ) (g₀ g' : GtPtF D F) (w' : Frm D F k g'.b), IsTor t g₀ → g.IsAdd g₀ g' → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) → ∀ (s : Fam D F k) χ, coef s g' w' χ = (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  intro R _ _ D F _ _ k g
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  refine ⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k)
      (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _)
      (LB.oneGen D.P.L (Y := (TF (R := R) F).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  · obtain ⟨x, hx⟩ := exists_isCoef g hw χ s
    exact ⟨x, hx, fun y hy => isCoef_unique hy hx⟩
  · intro s s' c χ
    refine coef_eq fun z J hJ => ?_
    have a := isCoef_coef g hw χ s z J hJ
    have a' := isCoef_coef g hw χ s' z J hJ
    rw [sval_lin g.b s s' c χ hJ]
    simp only [cst_eq, map_add (f := _), map_mul] at a a' ⊢
    linear_combination cstH z c * a + a'
  · intro w' hw'
    obtain ⟨c, hc, hv⟩ := exists_frame_ratio hw hw'
    refine ⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩
    have a := isCoef_coef g hw χ s z J hJ
    rw [hv z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z c * a
  · intro t g₀ g' w' ht hadd hv s χ
    obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
    have a := isCoef_coef g hw χ s z J hJ
    have e := hs χ z J hJ
    rw [ht.1, _root_.mul_one] at hb
    have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
    rw [e₀, _root_.mul_one] at e
    have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
    rw [hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z (t (Multiplicative.ofAdd χ)).val * a

end GlobalTheory.UT.CoefBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLiftOfRetraction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RatLift

theorem exists_lift_of_retraction {X B Z : Scheme.{0}} [IsAffine Z] (q : X ⟶ B) [IsAffineHom q] {V : B.Opens}
    (hV : IsAffineOpen V) (r : Γ(X, q ⁻¹ᵁ V) ⟶ Γ(B, V)) (hr : q.app V ≫ r = 𝟙 _) (b : Z ⟶ B)
    (hb : ⊤ ≤ b ⁻¹ᵁ V) : ∃ x : Z ⟶ X, x ≫ q = b := by
  refine ⟨Z.isoSpec.hom ≫ Spec.map (b.appLE V ⊤ hb) ≫ Spec.map r ≫ (hV.preimage q).fromSpec, ?_⟩
  simp only [Category.assoc]
  rw [← hV.SpecMap_appLE_fromSpec q (hV.preimage q) le_rfl, Scheme.Hom.appLE_eq_app, ← Spec.map_comp_assoc (q.app V) r, hr,
    Spec.map_id, Category.id_comp, hV.SpecMap_appLE_fromSpec b (isAffineOpen_top Z) hb, IsAffineOpen.fromSpec_top,
    Iso.hom_inv_id_assoc]

theorem exists_retraction {A C X : Type} [CommRing A] [CommRing C] [AddCommGroup X] (f : A →+* C)
    (g : Multiplicative X →* C)
    (h : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g (fun _ _ => Commute.all _ _))) :
    ∃ r : C →+* A, r.comp f = RingHom.id A := by
  let e := RingEquiv.ofBijective _ h
  let a : AddMonoidAlgebra A X →+* A :=
    AddMonoidAlgebra.liftNCRingHom (RingHom.id A) (1 : Multiplicative X →* A) (fun _ _ => Commute.all _ _)
  refine ⟨a.comp e.symm.toRingHom, RingHom.ext fun c => ?_⟩
  have : e.symm (f c) = AddMonoidAlgebra.single 0 c := by
    rw [RingEquiv.symm_apply_eq]
    simp [e, AddMonoidAlgebra.liftNCRingHom]
  simp [this, a, AddMonoidAlgebra.liftNCRingHom]

attribute [local instance] SplitExt.free SplitExt.finite

theorem exists_point_over :
    ∀ (F : Type) [Field F] (E : SplitExt (Spec (CommRingCat.of F))) (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G) (b : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ E.B), ∃ x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G, x ≫ Dat.q = b := by
  intro F _ E G _ Dat b
  let b' : Spec (CommRingCat.of F) ⟶ E.B.left := b.left
  let p : Spec (CommRingCat.of F) := default
  choose j hj using fun k => exists_chart (E.O (E.basis k)).isLB (b' p)
  have hp : b' p ∈ E.chart j := by
    have : ((E.chart j : E.B.left.Opens) : Set E.B.left) =
      ⋂ k, ((E.O (E.basis k)).L.U (j k) : Set E.B.left) := TopologicalSpace.Opens.coe_iInf _
    exact this.ge (Set.mem_iInter.2 hj)
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVj⟩ :=
    E.B.left.isBasis_affineOpens.exists_subset_of_mem_open hp (E.chart j).2
  obtain ⟨r, hr⟩ := exists_retraction _ _ (Dat.coord j V hV hVj)
  have := Dat.q_affine
  obtain ⟨x, hx⟩ := exists_lift_of_retraction Dat.q.left hV (CommRingCat.ofHom r) (CommRingCat.hom_ext hr) b'
    (fun y _ => by
      obtain rfl : y = p := Subsingleton.elim _ _
      exact hpV)
  refine ⟨Over.homMk x ?_, Over.OverMorphism.ext hx⟩
  rw [← Over.w Dat.q, ← Category.assoc, hx]
  exact Over.w b

end GlobalTheory.RatLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixAction

variable {S : Scheme.{0}}


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.MatrixAction.comp_finsetProd {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S}
    (a : T' ⟶ T) {κ : Type} (s : Finset κ) (x : κ → (T ⟶ G)) :
    a ≫ (∏ l ∈ s, x l) = ∏ l ∈ s, a ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, comp_mul, ih]


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.MatrixAction.isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h1 : ∀ T : Over S, (1 : T ⟶ G) ≫ f = 1)
    (hm : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have := h1 (𝟙_ (Over S))
    simpa [Hom.one_def] using this
  · have := hm (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using this

section
variable {G : Over S} [GrpObj G] {O : Type} [Ring O] (ρ : RingAct G O)

end

end GlobalTheory.MatrixAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif.RigidifyIso

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_ratio {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (f : Y' ⟶ Y) (hφ : ∀ k, φ' k ≫ F = f ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm (r ≫ f) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ c * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have le : ∀ p, LB.wchart L (fun k => φ' k ≫ F) p ≤ f ⁻¹ᵁ LB.wchart L φ p := fun p y hy =>
    Set.mem_iInter.2 fun k => (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (p k)) (hφ k)).mp (Set.mem_iInter.1 hy k)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res (inf_le_left.trans (le p)) (pullU f _ (t.s p)) * (u p q * res inf_le_right (a.s q))⁻¹) =
        gm (r ≫ f) z (LB.wchart L φ p) (t.s p) * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q))⁻¹ :=
    fun Z r z p q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hz _).trans (gm_pull r f z _ (le p hz.1) _))
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (hu p q Z r z hz) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y'.Opens)
    (fun i : (K → L.ι) × (K → L'.ι) => LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩)
    (fun i => res (inf_le_left.trans (le i.1)) (pullU f _ (t.s i.1)) * (u i.1 i.2 * res inf_le_right (a.s i.2))⁻¹)
    (fun i i' y hy => by
      have e : trF φ ε (𝟙 Y' ≫ f) y i.1 i'.1 = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y i.1 i'.1 := by
        simp only [trF, hφ, Category.assoc]
      rw [hv _ _ y _ _ hy.1, hv _ _ y _ _ hy.2, pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2,
        gen_trans ha (𝟙 Y') y hy.1.2 hy.2.2, gen_trans ht (𝟙 Y' ≫ f) y (le _ hy.1.1) (le _ hy.2.1), e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun Z r z p q h₁ h₂ => ?_⟩
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
  have e := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hv Z r z p q hz))
  rw [e, inv_mul_cancel_right]

theorem exists_scaled {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (π : X' ⟶ B) (c : Γ(B, ⊤)ˣ) : ∃ w' : LB.Iso L' (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
      (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k → gw w' r z j k = gm (r ≫ π) z ⊤ c * gw w r z j k := by
  refine ⟨⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩, fun Z r z j k hj hk => ?_⟩
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r π z ⊤ trivial c)) rfl)

theorem exists_rigidified_iso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (he : eSec G' ≫ Ψ = f ≫ eSec G) (L : RigLB G) (L' : RigLB G'), (∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen) → ∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) := by
  rintro S S' f G _ _ G' _ _ Ψ he L L' ⟨w, hw⟩
  have hw := (isGen_iff w).1 hw
  obtain ⟨c, hc⟩ := exists_ratio (K := PUnit) (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1)
    hw L.isLB L'.isLB f (fun _ => he) L'.rig L'.rigGen L.rig L.rigGen
  obtain ⟨w', hw'⟩ := exists_scaled (B := (𝟙_ (Over S')).left) w G'.hom c
  have hs : eSec G' ≫ (show G'.left ⟶ (𝟙_ (Over S')).left from G'.hom) = 𝟙 _ := Over.w η[G']
  refine ⟨w', (isGen_iff w').2 fun Y r y j j' k k' hj hj' hk hk' => ?_,
    (maps_iff w' _ (fun _ => eSec G) _ L'.rig L.rig f _ (rigPull_le Ψ f he L.L) (fun _ => rfl)).2
      fun Z r z p q hp hq => ?_⟩
  · rw [hw' Y r y j k hj hk, hw' Y r y j' k' hj' hk', hw Y r y j j' k k' hj hj' hk hk', mul_left_comm]
  · refine (hc Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)).trans ?_
    rw [← _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one,
      hw' Z (r ≫ eSec G') z _ _ (hp _) (hq _), Category.assoc]
    exact congrArg (fun g => gm g z ⊤ c * _) ((congrArg (r ≫ ·) hs).trans (Category.comp_id r)).symm

end GlobalTheory.Unif.RigidifyIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionTheta

theorem exists_theta_acts : KerPowSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ), 1 ≤ n → ∀ x : Over.mk t ⟶ P.A, x ^ n = 1 → ∃ θ : ThetaGrp P.A P.L (n : ℤ) (Over.mk t), θ.pt = x ∧ ∀ s : LB.Sec (LPow P.A P.L (n : ℤ) (Over.mk t)), ∃ s', IsActOf P.A P.L (n : ℤ) θ s s' := by
  intro hK S _ P F _ t n hn x hx

  have : Unique (Over.mk t).left := inferInstanceAs (Unique (PrimeSpectrum F))
  obtain ⟨θ, hθ⟩ := GlobalTheory.BoxTheta.exists_theta hK P hn x hx

  exact ⟨θ, hθ, fun s => GlobalTheory.VVRank.exists_isTwistPull P.A P.isLB θ.isGen s⟩

end GlobalTheory.TorsionTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaOfPowEqOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionThetaLocal

theorem exists_theta_of_pow_eq_one : ∀ (S₀ : Scheme.{0}) (G : Over S₀) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (_ : CubicalStr G L) (S : Type) [CommRing S] [IsLocalRing S] (t : Spec (CommRingCat.of S) ⟶ S₀) (k : ℕ) (x : Over.mk t ⟶ G), x ^ k = 1 → ∃ θ : ThetaGrp G L.L (k : ℤ) (Over.mk t), θ.pt = x := by
  intro S₀ G _ _ L c S _ _ t k x hx
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_cubN c (1 : Over.mk t ⊗ G ⟶ G) (fst (Over.mk t) G ≫ x) (snd (Over.mk t) G) k
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := S) L.L L.isLB (K := Fin 2)
    ![x.left, (1 : Over.mk t ⟶ G).left] ![-(k : ℤ), k]
  have hm : (fst (Over.mk t) G ≫ x) ^ k = 1 := by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have h1 : (fst (Over.mk t) G).left ≫ (1 : Over.mk t ⟶ G).left = (1 : Over.mk t ⊗ G ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  have h2 : (fst (Over.mk t) G).left ≫ x.left = (fst (Over.mk t) G ≫ x).left := rfl
  have h3 : translPt G x = (fst (Over.mk t) G ≫ x) * snd (Over.mk t) G := rfl
  obtain ⟨w, hw, -⟩ := Geo.Tor.exists_gen L.isLB
    (φ' := ![(snd (Over.mk t) G).left, (translPt G x).left]) (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      erw [h1, h2]
      rw [hm, h3]
      simp only [_root_.one_mul, _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ e (fst (Over.mk t) G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.pullGen_isGen _ _ _ _ he _))
  exact ⟨⟨x, w, hw⟩, rfl⟩

end GlobalTheory.TorsionThetaLocal
end

