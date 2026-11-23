module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValuePullbackBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPoinc.USum

theorem ptSecT_comp_whisker {B : Scheme.{0}} {A : Over B} [GrpObj A] {T T' : Over B} (c : T' ⟶ T) (y : T ⟶ A) :
    (ptSecT A (c ≫ y)).left ≫ (c ▷ A).left = c.left ≫ (ptSecT A y).left := by
  rw [← Over.comp_left, ← Over.comp_left, ptSecT, ptSecT, lift_whiskerRight, comp_lift, Category.id_comp,
    Category.comp_id]

theorem isTwVal_pull {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) {T' : Over B} (c : T' ⟶ T) :
    IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ (c ≫ β) (c ≫ x) (c ≫ h) (c.left.appTop.hom v) := by
  rintro ⟨α, U, hα, hU, H⟩
  obtain ⟨α', hα', vα⟩ := GlobalTheory.VVRank.exists_gen_pullTo
    (φ' := ![(snd T' P.A).left, (snd T' P.A ^ m).left]) α hα (c ▷ P.A).left (fun k => by
      fin_cases k
      · exact GlobalTheory.VVRank.whisker_snd_left P.A c
      · change (c ▷ P.A).left ≫ (snd T P.A ^ m).left = (snd T' P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, whiskerRight_snd])
  obtain ⟨U', hU', vU⟩ := GlobalTheory.SymLiftGlobal.exists_symLift_pull_val P.isLB c hU
  refine ⟨α', U', hα', hU', fun Z r z J hJ => ?_⟩
  have eq₁ : (c ≫ x) * (c ≫ h) = c ≫ (x * h) := (MonObj.comp_mul _ _ _).symm
  have q := H Z (r ≫ c.left) z J hJ
  have g : gs r z ⊤ (c.left.appTop.hom v) = gs (r ≫ c.left) z ⊤ v := gs_pull r c.left z ⊤ trivial v
  have w : ∀ (y : T ⟶ P.A) {W : Scheme.{0}} (k : (T ⊗ P.A).left ⟶ W),
      (ptSecT P.A (c ≫ y)).left ≫ (c ▷ P.A).left ≫ k = c.left ≫ (ptSecT P.A y).left ≫ k := fun y W k => by
    rw [← Category.assoc, ptSecT_comp_whisker, Category.assoc]
  have eq₃ : (c ≫ (x * h)) ^ m = c ≫ (x * h) ^ m := (MonObj.comp_pow _ _ _).symm
  rw [g, vα _ _ z J hJ, vα _ _ z J hJ, vU _ _ z J hJ, eq₁, eq₃]
  simp only [Category.assoc, ptSecT_comp_whisker, comp_whiskerRight, Over.comp_left, w]
  simpa only [Category.assoc] using q

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueTranslateOrthogonalTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum


open GlobalTheory.ThetaCompare GlobalTheory.CommPairing in
theorem isTwVal_transl : ∀ {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀)) {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1))) (β : T ⟶ T₀) (x h : T ⟶ P.A) (v : Γ(T.left, ⊤)) (k : T ⟶ P.A), k ^ m = 1 → WeilIs P.A P.L N x k 1 → IsTwVal P N m θ τ β x h v → IsTwVal P N m θ τ β x (h * k) v := by
  intro B P N m T₀ T θ z₀ τ β x h v k hk hw H
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have := P.isAb.comm
  obtain ⟨α, U, hα, hU, H⟩ := H
  refine ⟨α, U, hα, hU, fun Z r z J hJ => ?_⟩
  have e₀ : (translT P.A k).left ≫ (snd T P.A).left = (translPt P.A k).left := by
    rw [← Over.comp_left, translT, lift_snd]
  have e₁ : (translT P.A k).left ≫ (snd T P.A ^ m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, SymLiftOdd.comp_pow', translT, lift_snd,
      show translPt P.A k = (fst T P.A ≫ k) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hk,
      MonObj.comp_one, _root_.one_mul]
  obtain ⟨d, hd, hv⟩ := exists_gen P.isLB (K' := Fin 2) (φ' := ![(snd T P.A).left, (translPt P.A k).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ g => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, e₀, e₁, neg_neg, zpow_neg, zpow_one, _root_.mul_assoc]
      rw [inv_inv, mul_left_comm (g (snd T P.A ^ m).left)⁻¹, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen P.L _ _ _ _ α (LB.invGen P.L _ _ (LB.pullGen P.L _ _ α (translT P.A k).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  let D : ThetaGrp P.A P.L N T := ⟨k, d, hd⟩
  have hD : ∀ s : Z ⟶ (T ⊗ P.A).left,
      tval D s z J = val α s z J * (val α (s ≫ (translT P.A k).left) z J)⁻¹ := fun s =>
    (hv Z s z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (val α s z J * ·)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have hx : U.pt = x := hU.pt_eq
  have hc : CommIsOf P.A P.L N U D 1 :=
    (GlobalLift.weilIs_iff_commIsOf hG P.isAb P.isLB U D 1).1 (hx ▸ hw)
  have q := val_corr hJ hc (r ≫ (ptSecT P.A h).left)
  have q₁ : val (constGen P.A P.L (1 : Γ(T.left, ⊤)ˣ)) (r ≫ (ptSecT P.A h).left) z J = 1 := by
    refine ((gm_res _ z le_top (Set.mem_iInter.2 fun k => k.elim) _).trans
      (gm_pull _ (fst T P.A).left z ⊤ trivial 1)).trans (map_one _)
  have q₂ : tval U (r ≫ (ptSecT P.A h).left) z J * tval D ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A U.pt).left) z J =
      tval D (r ≫ (ptSecT P.A h).left) z J * tval U ((r ≫ (ptSecT P.A h).left) ≫ (translT P.A k).left) z J * 1 :=
    ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))).symm.trans (q.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _))) q₁)))
  simp only [hD, Category.assoc, pt_translT, hx, _root_.mul_one] at q₂
  have p₁ : (x * (h * k)) ^ m = (x * h) ^ m := by
    rw [← _root_.mul_assoc, mul_pow, hk, _root_.mul_one]
  have p₂ : k * (x * h) = x * (h * k) := by rw [mul_comm k, _root_.mul_assoc]
  rw [p₂, mul_comm k h] at q₂
  rw [p₁]
  have H' := H Z r z J hJ
  set a₁ := val α (r ≫ (ptSecT P.A h).left) z J
  set a₂ := val α (r ≫ (ptSecT P.A (h * k)).left) z J
  set a₃ := val α (r ≫ (ptSecT P.A (x * h)).left) z J
  set a₄ := val α (r ≫ (ptSecT P.A (x * (h * k))).left) z J
  set u₁ := tval U (r ≫ (ptSecT P.A h).left) z J
  set u₂ := tval U (r ≫ (ptSecT P.A (h * k)).left) z J
  set t := val τ (r ≫ β.left) z J
  have f₁ : a₂ * t = (a₂ * a₁⁻¹) * (a₁ * t) := by
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  have f₂ : u₂ * a₄ = (a₂ * a₁⁻¹) * (u₁ * a₃) := by
    apply Additive.ofMul.injective
    replace q₂ := congrArg Additive.ofMul q₂
    simp only [ofMul_mul, ofMul_inv] at q₂ ⊢
    linear_combination (norm := module) -q₂
  rw [f₁, f₂, Units.val_mul _ (a₁ * t), Units.val_mul _ (u₁ * a₃), mul_left_comm, H', _root_.mul_assoc]

end GlobalTheory.UPoinc.USum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistedThetaValueUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

namespace GlobalTheory.UPoinc.USum

theorem isTwVal_unique {B : Scheme.{0}} (P : PolAV B) (N m : ℕ) {T₀ T : Over B} (θ : LB.Sec (LPow P.A P.L 1 T₀))
    {z₀ : T₀ ⟶ P.A} (τ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => z₀.left) (fun _ => 1)))
    (β : T ⟶ T₀) (x h : T ⟶ P.A) (v v' : Γ(T.left, ⊤)) (hN : Odd N) (H : IsTwVal P N m θ τ β x h v)
    (H' : IsTwVal P N m θ τ β x h v') : v = v' := by
  obtain ⟨α, U, hα, hU, e⟩ := H
  obtain ⟨α', U', hα', hU', e'⟩ := H'
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have hc := GlobalTheory.SymLiftOdd.symLift_unique hG P.isAb P.isLB hN U U' hU hU'
  obtain ⟨c, hcv⟩ := GlobalTheory.SymLiftOdd.exists_const P.isLB (fst T P.A).left (lift (𝟙 T) (1 : T ⟶ P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (GlobalTheory.SymLiftOdd.surj_fst hG P.isAb T)
    (fun U _ h => (Fintype.prod_sum_type _).trans (by
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel]))
    (DVR.mulGen_isGen P.L _ _ _ _ α (LB.invGen P.L _ _ α') hα (DVR.invGen_isGen _ _ _ _ hα'))
  refine fn_ext fun y _ => ?_
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  have r : ∀ w : T ⟶ P.A, val α (𝟙 _ ≫ (ptSecT P.A w).left) y J =
      val α' (𝟙 _ ≫ (ptSecT P.A w).left) y J * gm (𝟙 T.left) y ⊤ c := fun w => by
    have k := hcv _ (𝟙 _ ≫ (ptSecT P.A w).left) y J hJ'
    have k₂ : (𝟙 _ ≫ (ptSecT P.A w).left) ≫ (fst T P.A).left = 𝟙 T.left := by
      rw [Category.id_comp, ← Over.comp_left, ptSecT, lift_fst]; rfl
    rw [k₂, val_mul hJ', val_inv] at k
    rw [← k, mul_comm, inv_mul_cancel_right]
  have t : GlobalTheory.CommPairing.tval U (𝟙 _ ≫ (ptSecT P.A h).left) y J =
      GlobalTheory.CommPairing.tval U' (𝟙 _ ≫ (ptSecT P.A h).left) y J := val_corr hJ' hc _
  have e₁ := e _ (𝟙 _) y J hJ'
  have e₂ := e' _ (𝟙 _) y J hJ'
  rw [r, r, t] at e₁
  refine (Units.mul_left_inj (val α' (𝟙 _ ≫ (ptSecT P.A h).left) y J * gm (𝟙 T.left) y ⊤ c *
    val τ (𝟙 _ ≫ β.left) y J)).1 (e₁.trans ?_)
  simp only [Units.val_mul] at e₂ ⊢
  linear_combination (-(gm (𝟙 T.left) y ⊤ c).val) * e₂

end GlobalTheory.UPoinc.USum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitSvalIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermLocus

theorem isUnit_sval_iff {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (U : Y.Opens) (_ : r z ∈ U) (f : Γ(Y, U)), IsUnit (gs r z U f) ↔ IsUnit (gs (𝟙 Y) (r z) U f) :=
    fun U h f => by rw [gs_stalkMap r z U h, isUnit_map_iff]
  refine ⟨fun h => (mem_nonzeroLocus s _).2 ⟨_, hJ.mem φ r, (key _ (hJ.mem φ r) _).1 h⟩, fun h => ?_⟩
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 h
  rw [sval, sec_trans s r z (hJ.mem φ r) hj]
  exact (Units.isUnit _).mul ((key _ hj _).2 hu)

theorem nonzeroLocus_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (α : D.X) (b : D.SecB k α)
    (τ : SecK D.P.L Y.q.left k), IsTermOf Y b τ → nonzeroLocus τ = Y.q.left ⁻¹ᵁ nonzeroLocus b := by
  intro R _ _ D Y k α b τ h
  ext y
  choose J hJ using fun χ : Y.H.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ' : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 Y.H) y J hJ'
  rw [Over.id_left, Category.id_comp] at e
  change y ∈ nonzeroLocus τ ↔ Y.q.left y ∈ nonzeroLocus b
  refine (isUnit_sval_iff τ (𝟙 _) y hJ').symm.trans ?_
  rw [e, IsUnit.mul_iff, isUnit_sval_iff b _ y hJ']
  exact and_iff_left (Units.isUnit _)

end GlobalTheory.Mum.TermLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoAbelianSchemeSemiAbelianOfCommonGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem iso_of_common_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (A G : Over (Sp O)) [GrpObj A] [GrpObj G] [IsCommMonObj G], IsAbelianScheme A → IsSemiAbelian G → ∀ (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (B : Over (Sp K)) [GrpObj B] (a : B.left ⟶ A.left) (g : B.left ⟶ G.left), IsGrpPullback B A (spMap (algebraMap O K)) a → IsGrpPullback B G (spMap (algebraMap O K)) g → ∃ i : A ≅ G, IsMonHom i.hom ∧ a ≫ i.hom.left = g ∧ (∀ (L : LB A.left) (L' : LB G.left), L.IsLB → L'.IsLB → LBIso (L.pull a) (L'.pull g) → LBIso L (L'.pull i.hom.left)) ∧ ∀ (e : A ⟶ A) (f : G ⟶ G) (eB : B ⟶ B), eB.left ≫ a = a ≫ e.left → eB.left ≫ g = g ≫ f.left → e ≫ i.hom = i.hom ≫ f := by
  intro O _ _ _ _ _ A G _ _ _ hA hG K _ _ _ B _ a g ha hg
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj := GlobalTheory.IsGenericPointHom.fractionField O K
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ :=
    GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions hS hj hA' hG ha hg
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian A hA'
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  refine ⟨E, hE, hEa, ?_, ?_⟩
  · intro L L' hL hL' h
    refine GlobalTheory.Poinc.Extend.lbIso_of_generic A hA ha.1 hL (pull_isLB hL' _) ?_
    exact LBIso.trans (pull_isLB hL _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h
      (GlobalTheory.GenSpread.lbIso_pull_pull hL' a hEa.symm)
  · intro e f eB he hf
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback ha.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc a e.left, ← he, Category.assoc, hEa,
      reassoc_of% hEa]
    exact hf

end GlobalTheory.UPoinc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreCoordinateMapAffineSpace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem surjective_of_isProper_of_app_injective : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsProper a → (∀ V : Y.Opens, Function.Injective (a.app V).hom) → Function.Surjective a := by
  intro X Y a ha hinj
  haveI := ha
  by_contra hne
  simp only [Function.Surjective, not_forall] at hne
  obtain ⟨y, hy⟩ := hne
  have hcl : IsClosed (Set.range a) := by
    simpa using a.isClosedMap _ isClosed_univ
  let V : Y.Opens := ⟨(Set.range a)ᶜ, hcl.isOpen_compl⟩
  haveI : Nonempty V := ⟨⟨y, fun ⟨p, hp⟩ => hy ⟨p, hp⟩⟩⟩
  have hV : a ⁻¹ᵁ V = ⊥ := by
    ext p
    simp [V]
  haveI : Subsingleton Γ(X, a ⁻¹ᵁ V) :=
    CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hV)
  have : Subsingleton Γ(Y, V) := (hinj V).subsingleton
  exact not_subsingleton Γ(Y, V) this

theorem isolated_in_coordinate_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj
  set F := pullback.fst (𝔸(Fin g; Sp R) ↘ Sp R) π with hF
  have hw : (a.fiberι x ≫ c) ≫ F = (a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x)) ≫
      (𝔸(Fin g; Sp R)).fromSpecResidueField (τ x) := by
    rw [Category.assoc, hF, hc1, ← Category.assoc, Scheme.Hom.fiber_fac, Category.assoc, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let φ : a.fiber x ⟶ F.fiber (τ x) := pullback.lift _ _ hw
  have hφ1 : φ ≫ F.fiberι (τ x) = a.fiberι x ≫ c := pullback.lift_fst _ _ _
  have hφ2 : φ ≫ F.fiberToSpecResidueField (τ x) = a.fiberToSpecResidueField x ≫ Spec.map (τ.residueFieldMap x) :=
    pullback.lift_snd _ _ _
  have hUO := _root_.GlobalTheory.FibOpen.fibre_universallyOpen R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs hap haV hτ hc1 hc2 hc x hxc hxR hinj hsurj φ hφ1 hφ2
  haveI : IsPreimmersion (F.fiberι (τ x)) := inferInstance
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_open_range_eq_inter_preimage_etale_univOpen X _ _ _ c (F.fiberι (τ x)) (a.fiberι x) φ hc inferInstance hUO hφ1.symm
  rw [Scheme.Hom.range_fiberι, Scheme.Hom.range_fiberι] at hW
  have hs := surjective_of_isProper_of_app_injective X U.left a hap (fun V => (haV V).1)
  haveI := hap
  refine ⟨⟨(a '' (W : Set X)ᶜ)ᶜ, (a.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨p, hp, hpx⟩
    have : p ∈ a ⁻¹' {x} := hpx
    rw [hW] at this
    exact hp this.1
  · intro u hu hτu
    obtain ⟨p, rfl⟩ := hs u
    by_cases hp : p ∈ W
    · have : p ∈ (W : Set X) ∩ c ⁻¹' (F ⁻¹' {τ x}) := by
        refine ⟨hp, ?_⟩
        show F (c p) = τ x
        rw [← Scheme.Hom.comp_apply, hF, hc1, Scheme.Hom.comp_apply, hτu]
      rw [← hW] at this
      exact this
    · exact absurd ⟨p, hp, rfl⟩ hu

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IzumiBoundModPrincipalIdeal
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Izumi

theorem small_mod_principal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  intro o Ω _ _ _ _ M hn U hU x hx f hf hf0
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x
  have hB := _root_.GlobalTheory.Izumi.iInf_map_smallIdeal_le_span o Ω M hn U hU x hx f hf hf0
  choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩
    (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB
  refine ⟨C, fun e F hF => ?_⟩
  have hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e := hC e (mem_smallIdeal.2 hF)
  obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := Ideal.span_eq (maximalIdeal (M.O x))
  refine ⟨a, b, rfl, ?_⟩
  rw [hm]
  exact hb

end GlobalTheory.Izumi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalIffEtalePullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem kltAt_iff_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  intro M W _ _ _ _ p f _ n m _ _ U D₀ D₁ hU hm hD y hy
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme M := ModifSections.isNormalScheme_of_smooth (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := ModifSections.isNormalScheme_of_smooth p
  have hnM := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
  have hnW := NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hne : ∀ η : RatForms p n, η ≠ 0 → ratPull p f n η ≠ 0 := _root_.GlobalTheory.EtaleKlt.ratPull_ne_zero M W p f n U hU ⟨y, hy⟩
  have hlog : ∀ (η : RatForms p n) (m' : ℕ) (g : W.functionFieldˣ), η ≠ 0 →
      IsLogEqn p (qWeil D₀ m) η (f y) m' g →
      IsLogEqn (f ≫ p) (qWeil D₁ m) (ratPull p f n η) y m'
        (Units.map (functionFieldMap f).toMonoidHom g) := by
    intro η m' g hη h z hz E' hE'
    have hzU : z ∈ U := hz.mem_open U.isOpen hy
    obtain ⟨E, hE, hord, hform⟩ := _root_.GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd M W p f n U hU z hzU E' hE'
    have key := h (f z) (hz.map f.continuous) E hE
    obtain ⟨d, hd⟩ := D₀.exists_isEqn (f z)
    have hd' := hD z d hd
    have hmult : D₁.mult z = D₀.mult (f z) := by
      rw [hd'.mult_eq, hd.mult_eq, ← hE'.ord_eq, ← hE.ord_eq, hord]
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [hf, hord, ← key]
    simp [qWeil, hmult]
  constructor
  · intro hk
    obtain ⟨η, hη, hG⟩ := isLogCanonicalMultiple_canonical (p := p) (n := n) hnW D₀ hm
    obtain ⟨g, hg⟩ := (m • canonical p n + D₀).exists_isEqn (f y)
    have h1 := hG (f y) g hg
    refine (h1.kltAt_iff hnW hη hm).2 fun E hE => ?_
    obtain ⟨E', hE', hord, hform⟩ := _root_.GlobalTheory.EtaleKlt.divOver_lift M W p f n U hU y hy E hE
    have h2 := ((hlog η m g hη h1).kltAt_iff hnM (hne η hη) hm).1 hk E' hE'
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [discrep, hord, hf] at h2
    exact h2
  · rintro ⟨η, m', g, hη, hm', h1, h2⟩
    refine ⟨ratPull p f n η, m', _, hne η hη, hm', hlog η m' g hη h1, fun E' hE' => ?_⟩
    obtain ⟨E, hE, hord, hform⟩ := _root_.GlobalTheory.EtaleKlt.divOver_restrict M W p f n U hU y hy E' hE'
    have h3 := h2 E hE
    rw [discrep] at h3 ⊢
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [hord, hf]
    exact h3
end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInclusionFirstFactorOverAbelianInclusion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd

theorem c_inc_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (i₁ : D₁.P.A ⟶ D.P.A) (j₁ : D₁.X →+ D.X), i₁ ≫ p₁ = 𝟙 _ → i₁ ≫ p₂ = toUnit _ ≫ η[D₂.P.A] → (∀ y, q₁ (j₁ y) = y) → (∀ y, q₂ (j₁ y) = 0) → ∀ y, D.c (j₁ y) = D₁.c y ≫ i₁ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS i₁ j₁ e₁ e₂ hq₁ hq₂ y
  haveI := hS.lim
  apply (cancel_mono (lift p₁ p₂)).1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
    rw [hS.c_pr₁, hq₁, e₁, Category.comp_id]
  · simp only [Category.assoc, lift_snd]
    rw [hS.c_pr₂, hq₂, e₂, degPre_c_zero, Hom.one_def, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

end GlobalTheory.MumProd
end

