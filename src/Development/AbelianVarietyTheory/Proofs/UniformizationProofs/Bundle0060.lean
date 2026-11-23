module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitLevels
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.RedTotal

section Units

variable {S : Type} [CommRing S] (J : Ideal S)

theorem appTop_specMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec.map (CommRingCat.ofHom f)).appTop.hom a) =
      f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom a) :=
  congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem ΓSpecIso_injective (A : Type) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective

theorem fn_ext_levels [IsHausdorff J S] {a b : Γ(Spec (CommRingCat.of S), ⊤)}
    (h : ∀ e, (adicLevelι J (e + 1)).appTop.hom a = (adicLevelι J (e + 1)).appTop.hom b) : a = b := by
  apply ΓSpecIso_injective
  have := IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom b) fun n _ =>
      (appTop_specMap _ a).symm.trans ((congrArg _ (h n)).trans (appTop_specMap _ b))
  exact congrFun this ()

theorem exists_fn_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤))
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)) = ρ e) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤), ∀ e, (adicLevelι J (e + 1)).appTop.hom a = ρ e := by
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  let f : ∀ n : ℕ, Polynomial ℤ →+* S ⧸ J ^ (n + 1) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) ((Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n))
  have hf : ∀ n, f n Polynomial.X = (Scheme.ΓSpecIso (CommRingCat.of _)).hom.hom (ρ n) := fun n =>
    Polynomial.eval₂_X _ _
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    rw [RingHom.comp_apply, hf, hf, ← h m]
    exact (appTop_specMap _ _).symm
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    (IsAdicComplete.StrictMono.liftRingHom J ha f hc Polynomial.X), fun e => ΓSpecIso_injective _ ?_⟩
  rw [appTop_specMap, Iso.inv_hom_id_apply, ← hf]
  exact congrArg (fun q => q Polynomial.X) (IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha f hc (n := e))

theorem exists_unit_levels [IsAdicComplete J S] (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (S ⧸ J ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom (ρ (e + 1)).val = (ρ e).val) :
    ∃ a : Γ(Spec (CommRingCat.of S), ⊤)ˣ, ∀ e, pullU (adicLevelι J (e + 1)) ⊤ a = ρ e := by
  obtain ⟨a, ha⟩ := exists_fn_levels J (fun e => (ρ e).val) h
  obtain ⟨b, hb⟩ := exists_fn_levels J (fun e => ((ρ e)⁻¹).val) fun e => by
    have : Units.map (adicLevelMap J (Nat.le_succ (e + 1))).appTop.hom.toMonoidHom (ρ (e + 1)) = ρ e :=
      Units.ext (h e)
    rw [← this]; rfl
  have hab : a * b = 1 := fn_ext_levels J fun e => by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact ⟨⟨a, b, hab, (mul_comm _ _).trans hab⟩, fun e => Units.ext (ha e)⟩

end Units

section Gens

variable {S : Type} [CommRing S] (J : Ideal S) {X : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_levels [IsHausdorff J S] (hL : L.IsLB) {φ : K → (Spec (CommRingCat.of S) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of S) ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) {u' : LB.Gen (LB.LinComb L φ' ε')} (hu' : u'.IsGen)
    (hv : ∀ e z C, Good L z C → val u (adicLevelι J (e + 1)) z C = val u' (adicLevelι J (e + 1)) z C) :
    LB.Gen.Corr L φ ε φ' ε' u u' := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio hL h u hu u' hu'
  have h2 : a = 1 := Units.ext (fn_ext_levels J fun e =>
    (FormalPoint.appTop_eq_one_of_gm _ a fun z => by
      obtain ⟨C, hC⟩ := exists_good_pt hL z
      exact mul_eq_right.1 ((ha _ _ z C hC).symm.trans (hv e z C hC))).trans (map_one _).symm)
  exact corr_of_val hL fun y C hC => by rw [ha _ _ y C hC, h2, map_one, _root_.one_mul]

theorem exists_gen_levels [IsLocalRing S] [IsAdicComplete J S] (hL : L.IsLB)
    (φ : K → (Spec (CommRingCat.of S) ⟶ X)) (ε : K → ℤ) {Y : ℕ → Scheme.{0}} {ψ : ∀ e, K' → (Y e ⟶ X)}
    {ε' : K' → ℤ} (u : ∀ e, LB.Gen (LB.LinComb L (ψ e) ε')) (hu : ∀ e, (u e).IsGen)
    (y : ∀ e : ℕ, Spec (CommRingCat.of (S ⧸ J ^ (e + 1))) ⟶ Y e)
    (h : ∀ e, FormEq (fun k => adicLevelι J (e + 1) ≫ φ k) ε (fun k => y e ≫ ψ e k) ε')
    (hc : ∀ e z C, Good L z C →
      val (u (e + 1)) (adicLevelMap J (Nat.le_succ (e + 1)) ≫ y (e + 1)) z C = val (u e) (y e) z C) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = val s (k ≫ adicLevelι J (e + 1)) z C := by
  obtain ⟨s₀, hs₀⟩ := DVR.exists_gen_of_local L hL φ ε
  choose ρ hρ using fun e => TorusCoord.exists_ratio hL (fun U _ f => (h e U f).symm)
    (LB.pullGen L _ _ (u e) (y e)) (DVR.pullGen_isGen _ _ _ _ (hu e) _)
    (LB.pullGen L _ _ s₀ (adicLevelι J (e + 1))) (DVR.pullGen_isGen _ _ _ _ hs₀ _)
  have hρ' : ∀ e (Z : Scheme.{0}) (k : Z ⟶ _) z C, Good L z C →
      val (u e) (k ≫ y e) z C = gm k z ⊤ (ρ e) * val s₀ (k ≫ adicLevelι J (e + 1)) z C := fun e Z k z C hC =>
    (val_pull hC _ _ _).symm.trans ((hρ e Z k z C hC).trans (congrArg₂ (· * ·) rfl (val_pull hC _ _ _)))
  obtain ⟨a, ha⟩ := exists_unit_levels J ρ fun e => by
    refine (FormalPoint.appTop_eq_of_gm _ (𝟙 _) (ρ (e + 1)) (ρ e) fun z => ?_).trans (by simp)
    obtain ⟨C, hC⟩ := exists_good_pt hL z
    have e₁ := hρ' (e + 1) _ (adicLevelMap J (Nat.le_succ (e + 1))) z C hC
    have e₂ := hρ' e _ (𝟙 _) z C hC
    rw [Category.id_comp, Category.id_comp] at e₂
    rw [hc e z C hC, adicLevelMap_ι, e₂] at e₁
    exact (mul_right_cancel e₁).symm
  refine ⟨scaleGen a s₀, scaleGen_isGen a hs₀, fun e Z k z C hC => ?_⟩
  rw [val_scaleGen a s₀ _ hC, hρ' e Z k z C hC, ← ha e]
  exact congrArg (· * _) (gm_pull k _ z ⊤ trivial a)

end Gens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}

theorem formEq_mult {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ'))
        (fun k => (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k))
      (Sum.elim DegPre.gtε thε)
      (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ')) (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ f
  have p : ∀ α, ∏ k, f (DegPre.gtφT D T b α k) ^ DegPre.gtε k =
      (f (DVR.cP D T α * b).left)⁻¹ * f (DVR.cP D T α).left * f b.left * (f (1 : T ⟶ D.P.A).left)⁻¹ := fun α => by
    have := FormalPoint.prod_gtφT (𝟙 T) b α f
    simpa only [Over.id_left, Category.id_comp] using this
  have q := prod_cub (DVR.cP D T χ) (DVR.cP D T χ') b f
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [p, p, p]
  refine (congrArg (_ * ·) q).trans ?_
  rw [DVR.cPoint_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : PreU I D A G) {S : Type} [CommRing S] {φ : R →+* S}



omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
open FormalPoint in
theorem reduction_succ (x : Over.mk (spMap φ) ⟶ G) (e : ℕ) :
    adicLevelMap (I.map φ) (Nat.le_succ (e + 1)) ≫ reduction I x (e + 1) = reduction I x e ≫ thickMap R I e G := by
  have h₄ : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, h₄, reduction_fstG, reduction_fstG]
  exact adicLevelMap_ι_assoc _ _ _

variable [IsLocalRing S]



end Main

end GlobalTheory.RedTotal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefDet

theorem fn_ext_of_points {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType p] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Spec (CommRingCat.of F) ⟶ Y, r ≫ p = 𝟙 _ → ∀ z, r z ∈ U → gs r z U a = gs r z U b) : a = b := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn (Y.basicOpen (a - b)).isOpen.isLocallyClosed
  let r := pointOfClosedPoint p c hc
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hz : r z ∈ Y.basicOpen (a - b) := (congrArg (· ∈ Y.basicOpen (a - b)) (pointOfClosedPoint_apply p c hc z)).mpr hcW
  have hU : r z ∈ U := Y.basicOpen_le _ hz
  have e := h r (pointOfClosedPoint_comp p c hc) z hU
  have hu : IsUnit (gs r z U (a - b)) := by
    rw [gs_eq r z U hU, ← Scheme.mem_basicOpen _ _ z hU, ← Scheme.preimage_basicOpen]
    exact hz
  rw [gs_eq r z U hU, gs_eq r z U hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [gs_eq r z U hU, e] at hu
  exact not_isUnit_zero hu

theorem fam_eq_of_coef_eq : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (s s' : Fam D.toPre F k), (∀ g : GtPtF D.toPre F, ∃ w : Frm D.toPre F k g.b, w.IsGen ∧ ∀ χ, coef s g w χ = coef s' g w χ) → s = s' := by
  intro hL R _ _ _ I hA D F _ _ _ k s s' H
  have hsm := D.toPre.P.isAb.smooth
  let p : (DegPre.BF D.toPre F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.toPre.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.toPre.P.A.hom))
  have : IsReduced (DegPre.BF D.toPre F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine fam_ext fun χ j => fn_ext_of_points p fun r hr z hz => ?_
  let r' : TF (R := R) F ⟶ DegPre.BF D.toPre F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.toPre.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  obtain ⟨g, hg⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 (r' ≫ snd _ _)
  have er : lift (𝟙 (TF (R := R) F)) g.b = r' := by
    rw [hg]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  obtain ⟨w, hw, hc⟩ := H g
  obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TF (R := R) F).left) D.toPre.P.isLB z
  have a := CoefBasic.isCoef_coef g hw χ s z J hJ
  have a' := CoefBasic.isCoef_coef g hw χ s' z J hJ
  rw [hc χ, a', Units.mul_left_inj, Units.mul_left_inj, er] at a
  exact (sec_trans (s.s χ) r z hz (hJ.mem _ r)).trans ((congrArg _ a.symm).trans
    (sec_trans (s'.s χ) r z hz (hJ.mem _ r)).symm)

end GlobalTheory.UT.CoefDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamFEOneOfPsiRel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.UU

section
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem val_famMult_one {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (mu α : D.X) :
    val (DegPre.famMult D F 1 mu α) σ.left z J * val (D.psi α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau mu α) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (mu + α)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi α) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) 1) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi mu) (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK 1) (σ.left ≫ jFK (R := R) F) z J =
      val D.rigK (σ.left ≫ jFK (R := R) F) z J := congrArg (gm _ z _) (pow_one _)
  rw [val_famMult σ hJ, e, p₁, p₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem uVal_one (α : D.X) (m : TF (R := R) F ⟶ D.P.A) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) : uVal D F 1 α m ρ z J = 1 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  rw [uVal, cubN, Finset.prod_range_one, pow_zero, _root_.mul_one, C.s12, mul_inv_cancel]

theorem sval_of_const (s₀ s : Raw D F 1) (c : F) (hs : ∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j)
    (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval (s α) r z J =
      gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) *
        sval (s₀ α) r z J :=
  (congrArg (gs r z _) (hs α _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
    ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))

end

theorem famFE_one_of_psiRel : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ s : Raw D F 1) (c : F), PsiRel D (TF (R := R) F) s₀ → (∀ α j, (s α).f j = DegPre.constBF D F c _ * (s₀ α).f j) → DegPre.FamFE D F 1 s := by
  intro hG R _ _ D F _ _ s₀ s c hψ hs mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e₃ := (gen_fe hG 1 mu α).2 u hu hc _ (𝟙 _) y J hJ
  rw [uVal_one D F _ _ _ hJ, _root_.one_mul, Category.id_comp, Over.id_left] at e₃
  have e₄ := val_famMult_one D F (fst (TF (R := R) F) D.P.A) hJ mu α
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have e₁ := hψ (α + 1 • mu) _ (fst _ _) κ (snd _ _) y J hJ
  have e₂ := hψ α _ (fst _ _) κ (snd _ _ * cT D _ mu) y J hJ
  have q : snd (TF (R := R) F) D.P.A * cT D _ mu * cT D _ α = snd (TF (R := R) F) D.P.A * cT D _ (α + 1 • mu) := by
    rw [one_nsmul, add_comm, _root_.mul_assoc]
    exact congrArg _ (cPoint_add D _ mu α).symm
  rw [q] at e₂
  rw [lift_fst_snd, Over.id_left] at e₁
  have e₅ : val (D.psi (α + 1 • mu)) κ.left y J =
      val (DegPre.famMult D F 1 mu α) (fst (TF (R := R) F) D.P.A).left y J * val (D.psi α) κ.left y J := by
    rw [one_nsmul, add_comm]; exact e₄.symm
  have t : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have e₁' : sval (s₀ (α + 1 • mu)) (𝟙 _) y J = _ := e₁
  have e₂' : sval (s₀ α) (DegPre.trF D F mu).left y J = _ := e₂
  rw [sval_of_const D F s₀ s c hs _ _ y hJ, sval_of_const D F s₀ s c hs _ _ y hJ, Category.id_comp, Category.id_comp, t,
    e₁', e₂', e₃, e₅]
  simp only [Units.val_mul]
  ring

end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FromSpecStalkComp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.LevelVanishing

theorem fromSpecStalk_comp {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (z : Y) :
    Y.fromSpecStalk z ≫ p =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫ Y.presheaf.germ ⊤ z trivial) := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem sval_mem_map {R : Type} [CommRing R] (I : Ideal R) {X Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0)
    (z : Y) (J) (hJ : Good L z J) :
    sval d (𝟙 _) z J ∈ I.map ((Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by
  set ψ := (Y.presheaf.germ ⊤ z trivial).hom.comp
      ((p.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) with hψ
  by_cases htop : I.map ψ = ⊤
  · rw [htop]; trivial
  have : Nontrivial (Y.presheaf.stalk z ⧸ I.map ψ) := Ideal.Quotient.nontrivial_iff.2 htop
  have : IsLocalRing (Y.presheaf.stalk z ⧸ I.map ψ) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let Q : CommRingCat.{0} := CommRingCat.of (Y.presheaf.stalk z ⧸ I.map ψ)
  let q : Y.presheaf.stalk z ⟶ Q := CommRingCat.ofHom (R := Y.presheaf.stalk z) (Ideal.Quotient.mk (I.map ψ))
  have : IsLocalHom q.hom := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let r : Spec Q ⟶ Y := Spec.map q ≫ Y.fromSpecStalk z
  let w : Spec Q := IsLocalRing.closedPoint Q
  have hw : r w = z := by
    rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have hl : ∃ ρ : Spec Q ⟶ Spec (CommRingCat.of (R ⧸ I)),
      ρ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = r ≫ p := by
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map)), ?_⟩
    rw [Category.assoc, fromSpecStalk_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  choose I' hI' using fun χ : Spec Q ⟶ X => exists_chart hL (χ w)
  have hz : z ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hJ.mem φ (𝟙 _)
  have hm : r w ∈ LB.wchart L φ (fun k => J (𝟙 _ ≫ φ k)) := hw ▸ hz
  have e := sec_trans d r w (j := fun k => J (𝟙 _ ≫ φ k)) hm (Good.mem hI' φ r)
  have e0 : gs r w (LB.wchart L φ (fun k => I' (r ≫ φ k))) (d.f (fun k => I' (r ≫ φ k))) = 0 := H _ r hl w I' hI'
  rw [e0, mul_zero] at e
  replace e := (Scheme.Hom.germ_stalkMap_apply r _ w hm _).trans ((gs_eq r w _ hm _).symm.trans e)
  have e1 := congrArg (fun t => t.hom (d.f (fun k => J (𝟙 _ ≫ φ k))))
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk q _ hm)
  simp only [Scheme.stalkClosedPointTo, CommRingCat.hom_comp, RingHom.comp_apply] at e1
  refine Ideal.Quotient.eq_zero_iff_mem.1 ((congrArg _ (gs_eq (𝟙 Y) z _ hz _)).trans ?_)
  exact e1.symm.trans ((congrArg (stalkClosedPointIso Q).hom.hom e).trans (map_zero _))

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by
  intro V _ _ _ _ D A G _ _ U k σ f h e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, fun α hα z J hJ => sval_mem_map _ (𝟙_ _ ⊗ D.P.A).hom D.P.isLB (f α) ?_ z J hJ⟩
  refine GlobalTheory.LiftTest.main V _ D e G (U.gt e) (𝟙_ _ ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (f α) ?_
  intro Z x r hr z J hJ
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  have hb : r ≫ (𝟙_ _ ⊗ D.P.A).hom = x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left ≫ G.hom := by
    rw [← Over.w (snd (𝟙_ _) D.P.A), ← Category.assoc, hr, Category.assoc, Over.w, Over.w]
  let xG : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ G :=
    Over.homMk (x ≫ (fstG (IsLocalRing.maximalIdeal V) e G).left) (by rw [Category.assoc]; exact hb.symm)
  let rB : Over.mk (r ≫ (𝟙_ _ ⊗ D.P.A).hom) ⟶ 𝟙_ _ ⊗ D.P.A := Over.homMk r
  refine (hs Z x (lift (rB ≫ fst _ _) xG).left r ?_ hr ?_ z JG J hJG hJ).1 α hα
  · exact congrArg CommaMorphism.left (lift_snd (rB ≫ fst _ _) xG)
  · exact (congrArg CommaMorphism.left (lift_fst (rB ≫ fst _ _) xG)).symm

end GlobalTheory.LevelVanishing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiZeroMulRigV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psi_zero_mul_rigV : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1), PsiRel D (TF (R := R) F) s₀ → (∃ j, (s₀ 0).f j ≠ 0) → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → val (Z := (TF (R := R) F).left) (D.psi (0)) (jFK (R := R) F) z J * rigV D z J = 1 := by
  intro R _ _ D F _ _ s₀ H hs z J hJ
  have hc : cT D (DegPre.BF D F) 0 = 1 := by
    have h := DVR.cPoint_add D (DegPre.BF D F) 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left :=
    isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  let ζ : (TF (R := R) F).left ⟶ (DegPre.BF D F).left := (DegPre.zF D F).left
  let p : DegPre.BF D F ⟶ TF (R := R) F := fst _ _
  have hζ : ζ ≫ p.left = 𝟙 _ := by
    show (DegPre.zF D F ≫ p).left = _
    rw [show DegPre.zF D F ≫ p = 𝟙 _ from lift_fst _ _]
    rfl
  let κ₀ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  let J' : ((DegPre.BF D F).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ => J (ζ ≫ ψ)
  have hJ' : Good D.P.L (ζ z) J' := fun ψ => hJ (ζ ≫ ψ)
  have e := H 0 (DegPre.BF D F) p (p ≫ κ₀) (snd _ _) (ζ z) J' hJ'
  rw [hc, _root_.mul_one, show lift p (snd _ _) = 𝟙 (DegPre.BF D F) from lift_fst_snd] at e
  have hne : sval (s₀ 0) (𝟙 (DegPre.BF D F).left) (ζ z) J' ≠ 0 :=
    sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s₀ 0) hs _ (𝟙 _) (ζ z) J' hJ'
  have e1 : (val (D.psi 0) (p ≫ κ₀).left (ζ z) J' * rigV D (ζ z) J').val = 1 :=
    (mul_eq_right₀ hne).1 e.symm
  have n1 := (values_natural _ _ _ _ D.P.L _ _ _ (p ≫ κ₀).left ζ z J hJ).2.2.1 (D.psi 0)
  have n2 := (values_natural _ _ _ _ D.P.L PUnit (fun _ => eSec D.P.A) (fun _ => 1)
    (DegPre.BF D F).hom ζ z J hJ).2.2.1 D.rig
  have a1 : ζ ≫ (p ≫ κ₀).left = jFK (R := R) F := by
    show ζ ≫ p.left ≫ jFK (R := R) F = _
    rw [← Category.assoc, hζ, Category.id_comp]
  have a2 : ζ ≫ (DegPre.BF D F).hom = (TF (R := R) F).hom := Over.w (DegPre.zF D F)
  rw [a1] at n1
  rw [a2] at n2
  apply Units.ext
  have e2 := congrArg (ζ.stalkMap z).hom e1
  rw [map_one, Units.val_mul, map_mul] at e2
  rw [Units.val_mul, Units.val_one]
  exact (congrArg₂ (· * ·) n1 n2).trans e2

end GlobalTheory
end

