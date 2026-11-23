module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermNonzeroIndexMemMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.GSep.HighTerms

theorem term_mem_maximalIdeal : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : Y1 → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev X _ t δ 𝔪 C₀ lab₀ _ T hT c₁ mu₁ hmu₁
  obtain ⟨x, fr, th, w₀, s, g₀, ω₀, hx, hfr, hth, hw₀, hs, hg₀, hT⟩ := hT
  have hV := 𝔪.cn
  haveI : IsNoetherianRing V := hV.1
  haveI : IsIntegrallyClosed V := hV.2.1
  haveI : CharZero V := hV.2.2.2
  have hA := admissibleBase_of_completeNormalLocalCharZero hV
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hN₂ : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := by omega
  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', k, hk, hNW, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  obtain ⟨hNu, h0, hdv⟩ := _root_.GlobalTheory.GSep.unit_ne_zero_dvd I X₁ z₁ act V ev X t δ 𝔪 x₀ hdiv
  obtain ⟨θ, hθ⟩ := IntTerm.exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi
  have hu₀ : IsUnit ((υ 0 : V) * t 0) := by
    obtain ⟨r₀, hr₀, -, -, hu⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).1
    obtain ⟨u, hu'⟩ := (GlobalTheory.PsiCoordLocal.main V 𝔪.D hV.2.1 (𝔪.e₈ 0)).2.1 _ _ hr₀ (hυ 0)
    rw [hu']
    exact u.isUnit.mul (hu (map_zero _))

  have core : ∀ (a : X₁.S.Gam) (gi : GtPt 𝔪.D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
      (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left gi g' →
      (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x a) (fr a) →
      ∀ mu, ∃ α : V, coef s g' w (𝔪.e₈ mu) = k * κ * algebraMap V (FractionRing V) (υ mu * t mu * α) ∧
        (IntTerm.UnitAt 𝔪.D.toPre θ (𝔪.D.toPre.c (𝔪.e₈ mu) * gi.b) → IsUnit α) := by
    intro a gi g' w hP ho hw hov mu
    obtain ⟨w', fr', hw', hfr', hov', hco, hval⟩ := Tors.liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
      g' w (x a) (fr a) hw (hfr _).1 hov k hk
    have hb : g'.b = toUnit _ ≫ gi.b := ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 hP).1
    obtain ⟨τ, hτ⟩ := exists_gen_of_local (V := V) 𝔪.D.toPre.P.L 𝔪.D.toPre.P.isLB
      ![(η[𝔪.D.toPre.P.A]).left, gi.b.left] (DegPre.lineε 1)
    obtain ⟨u, hu⟩ := Sep.Frames.frame_unit_core hN gi.b (Sep.Frames.torsion_of_nsmul g' _ hb ho).2 hb w' hw' (by
      obtain ⟨o, h₁, h₂⟩ := ho
      exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hNW _ hN _ o h₁ h₂ _ _ _ hw' hov'
        (hmove _ _ _ _ _ (htf _) hfr' hval)) τ hτ
    have hif : IntTerm.IntFrm 𝔪.D.toPre gi.b w' (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)) :=
      ⟨τ, hτ, fun z J hJ => by
        rw [hu z J hJ, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, ← map_mul,
          Units.inv_mul, map_one, map_one, _root_.one_mul]⟩
    obtain ⟨α, hα, hαu⟩ := hκ gi g' w' _ hP hw' hif (𝔪.e₈ mu) _ (hυ mu)
    refine ⟨u * α, ?_, fun h => u.isUnit.mul (hαu h)⟩
    have e : algebraMap V (FractionRing V) u * algebraMap V (FractionRing V) (u⁻¹ : Vˣ) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [← hco]
    simp only [map_mul] at hα ⊢
    linear_combination k * algebraMap V (FractionRing V) u * hα - k * coef s g' w' (𝔪.e₈ mu) * e

  let C := ↥(X₁.S.HH X₁.M z₁)
  let lab : C → X₁.S.Gam := Subtype.val
  obtain ⟨l, hl, hlf⟩ := GlobalTheory.T.exists_torsion_frame_eq_const_mul_integral_generator V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ ρ hρ _ hN
  have hint := _root_.GlobalTheory.GSep.mem_HH_iff_yy_zero I X₁ z₁ act x₀ hdiv V ev X t δ 𝔪
  have hxb : ∀ (a) (xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A),
      xb.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left →
      xb.left = spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ (x a).left := by
    intro a xb h
    refine 𝔪.cart.1.hom_ext ?_ ?_
    · rw [h, Category.assoc, hx a, ← Category.assoc]
      congr 1
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
    · rw [Category.assoc, Over.w, Over.w]
      change _ = _ ≫ Spec.map (𝟙 _)
      rw [Spec.map_id, Category.comp_id]; rfl
  have hyy : ∀ c, 𝔪.YY (lab c) 0 := fun c => (hint _).1 c.2
  choose p xb hp hq hxp using hyy
  have hp0 : ∀ c, (p c).y = 0 := fun c => (hp c).trans (map_zero _)
  choose h gi hh hgt hfe hext hpull using fun c => GlobalTheory.T.rationalTorsionPoint_lift_section_torusExtension V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN (x (lab c)) (xb c) (p c)
    (hxb _ _ (hxp c)) (hp0 c) (hq c)
  choose g' hg' using fun c => GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) (gi c)
  choose w hw hif hlies using fun c => GlobalTheory.T.sectionValue_integralPoint_eq_adicSum_terms V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ (x (lab c)) (fr (lab c)) (h c) (gi c)
    (g' c) l hl (hfe c) (hext c) (hg' c) (hlf _ _ _ (htf _) (hh c) (hext c))
  have htor : ∀ c, ∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g' c) o ∧ o.IsZero := fun c => by
    obtain ⟨o, ho, hz⟩ := hgt c
    obtain ⟨o', ho'⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) o
    exact ⟨o', GlobalTheory.FieldRestrictionTest.isNsmul_restrict (hg' c) ho' ho,
      GlobalTheory.FieldRestrictionTest.isZero_restrict ho' hz⟩
  have hb : ∀ c, (g' c).b = toUnit _ ≫ (gi c).b := fun c =>
    ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hg' c)).1
  have hex : IntTerm.Exhausts 𝔪.D.toPre.P (X₁.S.r * X₁.S.N) fun c => (gi c).b := by
    refine GlobalTheory.T.torsionSections_exhaust_of_generic_geometric V _ _ hN C _ (fun c => (Sep.Frames.torsion_of_nsmul (g' c) _ (hb c) (htor c)).2) fun β hβ => ?_
    obtain ⟨y, hy, ⟨q, hq0, hqy⟩, H⟩ := GlobalTheory.T.geometricTorsionPoint_abelianPart_lies_under_classZero V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hN β hβ
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_member_has_label I X₁ z₁ act V ev X t δ 𝔪 y hy
    have hmem : a ∈ X₁.S.HH X₁.M z₁ := (hint a).2 ⟨q, y, hq0.trans (map_zero _).symm, hqy, ha⟩
    let c : C := ⟨a, hmem⟩
    have e : xb c = y := Over.OverMorphism.ext ((hxb _ _ (hxp c)).trans (hxb _ _ ha).symm)
    exact ⟨c, (H (p c) (hp0 c) (e ▸ hq c)).symm.trans ((GlobalTheory.FieldRestrictionTest.isPullF_iff _ _ _).1 (hpull c)).1⟩
  choose a hco hau using fun mu c => core (lab c) (gi c) (g' c) (w c) (hg' c) (htor c) (hw c) (hlies c) mu
  have hunit : ∃ c, IsUnit (a 0 c) :=
    (_root_.GlobalTheory.Poinc.IntTerm.exists_unitAt_mul V 𝔪.D.toPre θ hθ _ hN₂ hNu C _ hex (𝔪.D.toPre.c (𝔪.e₈ 0))).imp fun c hc => hau 0 c hc
  have hsum : ∀ c, ∃ S : V, 𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) S ∧
      (IsUnit S ↔ IsUnit (a 0 c)) := fun c => by
    obtain ⟨S, hS, hm⟩ := _root_.GlobalTheory.Poinc.AdicTerm.sumF_mul V _ (𝔪.e₈ 0) (coef s (g' c) (w c))
      (fun χ => υ (𝔪.e₈.symm χ) * t (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (k * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (IntTerm.mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (IntTerm.isUnit_of_sub_mem hm).trans ?_⟩
    rw [AddEquiv.symm_apply_apply]
    exact ⟨isUnit_of_mul_isUnit_right, fun h => hu₀.mul h⟩
  choose S hS hSu using hsum
  let c₀ : C := ⟨x₀, AddSubgroup.subset_closure hdiv⟩
  have hS0 : 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem _⟩ = k * κ * algebraMap V (FractionRing V) (S c₀) := hS c₀
  have hκ0 : k * κ ≠ 0 := left_ne_zero_of_mul (hS0 ▸ h0)
  have inj := IsFractionRing.injective V (FractionRing V)
  have hS₀ : IsUnit (S c₀) := by
    obtain ⟨c, hc⟩ := hunit
    obtain ⟨r, hr⟩ := hdv (lab c)
    rw [hS, hS0, mul_left_comm, ← map_mul] at hr
    have e := inj (mul_left_cancel₀ hκ0 hr)
    exact isUnit_of_mul_isUnit_right (e ▸ (hSu c).2 hc)
  obtain ⟨gi₁, hgi₁⟩ := GlobalTheory.Poinc.Sep.HighTerms.exists_integral V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.U _ hN (g₀ c₁) (hg₀ c₁).1
  obtain ⟨α, hα, -⟩ := core (lab₀ c₁) gi₁ (g₀ c₁) (ω₀ c₁) hgi₁ (hg₀ c₁).1 (hg₀ c₁).2.1 (hg₀ c₁).2.2 mu₁
  have e₁ := hT mu₁ c₁
  rw [hα, hS0, mul_left_comm, ← map_mul] at e₁
  have e₂ := inj (mul_left_cancel₀ hκ0 e₁)
  have hm : T mu₁ c₁ * S c₀ ∈ maximalIdeal V :=
    e₂ ▸ Ideal.mul_mem_right _ _ (IntTerm.mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ mu₁)
      (by rwa [Ne, map_eq_zero_iff _ 𝔪.e₈.injective]) (hυ mu₁))
  exact (Ideal.mul_unit_mem_iff_mem _ hS₀).1 hm

end GlobalTheory.GSep.HighTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsIsThetaTermsTorsionFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.GSep.ThetaTerms

theorem yK_ne_zero {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {x₀ : X₁.S.Gam}
    (hd : X₁.M.Div X₁.S.th x₀ z₁) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {X : Type} [AddCommGroup X] {t : X → V}
    {δ : I → X → X} (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) :
    𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  obtain ⟨a, ha⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL.1 hL.2.1 _ _ X₁.S X₁.ρ (FractionRing V) 𝔪.yK
  intro h0
  apply ha
  set y := jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ with hy
  have hs : y (closedPoint (FractionRing V)) ⤳ z₁ := by
    have : y (closedPoint (FractionRing V)) ∈ Set.range (X₁.M.Z.fromSpecStalk z₁) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hw : ∀ w, y w ⤳ y (closedPoint (FractionRing V)) := fun w => by
    rw [Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) w (closedPoint _)]
  have e : X₁.S.th a = X₁.S.th a / X₁.S.th x₀ * X₁.S.th x₀ := (div_mul_cancel₀ _ hd.1).symm
  rw [𝔪.yK_eq] at h0 ⊢
  change X₁.M.val y (X₁.S.th a) = 0
  change X₁.M.val y (X₁.S.th x₀) = 0 at h0
  rw [e, RatModel.val_mul hw ((hd.of_specializes hs).2 a) (𝔪.reg _ (X₁.S.th_mem x₀)), h0, mul_zero]

theorem isThetaTerms₀_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), Set.range lab = X₁.S.HH X₁.M z₁ → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → IsThetaTerms₀ 𝔪.D.toPre (X₁.S.r * X₁.S.N) 𝔪.e₈ T := by
  intro I X₁ z₁ act x₀ hd V _ _ _ ev X _ t δ 𝔪 C lab hlab T hT
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, hT⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  have h0 := yK_ne_zero hd 𝔪

  obtain ⟨ρ, hρ, Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) 𝔪.wl_gen X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm 𝔪.cart) X₁.ρ.rig X₁.ρ.rig_gen
  have htf : ∀ a, IsTorsFrame 𝔪.A ρ (X₁.S.r * X₁.S.N) (x a) (fr a) := fun a =>
    GlobalTheory.FrameMove.isTorsFrame_move (T := baseOver (Sp X₁.S.R)) (T' := TFK (R := V) (FractionRing V)) (w := 𝔪.wl)
      (h := spMap 𝔪.yK) 𝔪.cart 𝔪.wl_gen
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx a) (X₁.ρ.fr_tors a) (hfr a).1 (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)
  obtain ⟨ρ', c, hc, hN, hmove⟩ := GlobalTheory.T.exists_renormalization_rigidification_multiple V _ 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre w₀ hw₀ ρ hρ
  choose w' fr' hw' hfr' hov hco hval using fun a : C => liesOver_scale V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.U.toUnifPre (FractionRing V) w₀
    (g' a) (w a) (x (lab a)) (fr (lab a)) (hg a).2.1 (hfr _).1 (hg a).2.2 c hc
  have htors : ∀ a, (g' a).b ^ (X₁.S.r * X₁.S.N) = 1 := fun a => by
    obtain ⟨o, h₁, h₂⟩ := (hg a).1
    letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
    have e := congrArg (GlobalTheory.TorusExt.gtProj 𝔪.D.toPre (FractionRing V)) ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 h₁)
    rw [map_nsmul] at e
    exact (congrArg Additive.toMul e).symm.trans ((isZero_iff o).1 h₂).1
  choose b hb₁ hb₂ using fun a => GlobalTheory.T.torsionPoint_extends_over_normal_domain hL.1 V 𝔪.cn.1 𝔪.cn.2.1 𝔪.D.toPre.P _ hk (g' a).b (htors a)
  refine ⟨(c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0, g', b, w', hb₂, fun a => (hg a).1, ?_, fun a => ⟨hw' a, ?_⟩,
    fun mu a => ?_⟩
  · refine GlobalTheory.T.torsion_sections_exhaust_geometric_fibres hL.1 V 𝔪.cn.1 𝔪.D.toPre.P _ hk hu C b hb₁ fun p hp => ?_
    obtain ⟨a, ha⟩ := exhaust_of_labels hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ hk C g' (fun a => x (lab a)) (fun a => (hg a).1)
      (fun a a' e => by
        have h₁ := hg a
        have h₂ := hg a'
        generalize w a' = om at h₂
        generalize g' a' = ga at e om h₂
        subst e
        exact GlobalTheory.T.eq_of_framedPoint_lies_over_torus_extension hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ hw₀ _ _ _ _ _ _ _ h₁.2.1 h₂.2.1 (hfr _).1 (hfr _).1
          h₁.2.2 h₂.2.2)
      (fun q y hq hy => by
        have hyN : y ^ (X₁.S.r * X₁.S.N) = 1 := (hy w₀ hw₀).1
        have e : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
            spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
          (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
        obtain ⟨l, hl, -⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Geo.Tor.pushHom 𝔪.cart _ y)
          (by rw [← map_pow, hyN, map_one])
        have hl' : y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
            (X₁.ρ.pt l).left := by
          rw [← e]
          exact (congrArg (fun q => q.left) hl).symm
        have hH : l ∈ X₁.S.HH X₁.M z₁ := (_root_.GlobalTheory.GSep.mem_HH_iff_yy_zero I X₁ z₁ act x₀ hd V ev X t δ 𝔪 l).2
          ⟨q, y, by rw [hq, map_zero], hy, hl'⟩
        obtain ⟨a, rfl⟩ : l ∈ Set.range lab := by rw [hlab]; exact hH
        refine ⟨a, 𝔪.cart.1.hom_ext ?_ ?_⟩
        · rw [hl', ← e]
          exact ((Category.assoc _ _ _).trans ((congrArg _ (hx _)).trans (Category.assoc _ _ _).symm)).symm
        · refine (Over.w y).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans (congrArg _ (Over.w (x (lab a))))).symm)
          exact (Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) p hp
    refine ⟨a, Over.OverMorphism.ext ?_⟩
    rw [ha, hb₂ a, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    change spMap _ ≫ spMap _ ≫ jK V = spMap _ ≫ jK V
    rw [Algebra.algebraMap_self, show spMap (RingHom.id (FractionRing V)) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  · obtain ⟨o, h₁, h₂⟩ := (hg a).1
    exact GlobalTheory.T.torsion_frame_abelian_part_torsion_frame hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U _ w₀ ρ' hN _ hk _ o h₁ h₂ _ _ _ (hw' a) (hov a)
      (hmove _ _ _ _ _ (htf _) (hfr' a) (hval a))
  · have h₁ := ((CoefBasic.coef_basic V 𝔪.D.toPre (FractionRing V) 1 (g' a)).2.2 (w' a) (hw' a)).2.1
    have h₂ : coef (0 : Fam 𝔪.D.toPre (FractionRing V) 1) (g' a) (w' a) (𝔪.e₈ mu) = 0 := by
      have := h₁ 0 0 1 (𝔪.e₈ mu)
      rw [one_smul, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    have h₃ : algebraMap V (FractionRing V) (T mu a) =
        coef ((c / 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) • s + 0) (g' a) (w' a) (𝔪.e₈ mu) := by
      rw [h₁, h₂, add_zero, div_mul_eq_mul_div, hco, ← hT, mul_div_cancel_right₀ _ h0]
    rw [h₃]
    exact CoefBasic.isCoef_coef _ (hw' a) _ _

end GlobalTheory.GSep.ThetaTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionPointsEqSameValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_torsion_points_eq_same_values : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b ∧ ∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J := by
  first | exact @GlobalTheory.GSep.TorsUniq.same_point | exact GlobalTheory.GSep.TorsUniq.same_point | (intros; apply GlobalTheory.GSep.TorsUniq.same_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTwistWeightWellDefinedLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.GSep.WtWd

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkSub {I : Type} (X₁ : GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y)
    (𝔪 : GMem X₁ z₁ act V ev Y t δ) (p p' : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N))
    (x x' : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A) (hp : p.y = p'.y)
    (hx : QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p x)
    (hx' : QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p' x') :
    ∃ q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N), q.y = 0 ∧
      QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q (x * x'⁻¹) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
    have hn := X₁.ρ.n_prime.pos
    rw [hj, X₁.ρ.N_eq]
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hB := 𝔪.D.tau_bimult
  obtain ⟨f, hto, -, -, hadd, -⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk
  have e := (hto p x).1 hx
  have e' := (hto p' x').1 hx'
  let F := AlgebraicClosure (FractionRing V)
  have gen_ext {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ 𝔪.D.toPre.P.A.left)} {ε : K → ℤ}
      {u v : LB.Gen (LB.LinComb 𝔪.D.toPre.P.L φ ε)} (hu : u.IsGen) (hv : v.IsGen)
      (h : ∀ y J, Good 𝔪.D.toPre.P.L y J → val u (𝟙 _) y J = val v (𝟙 _) y J) : u = v := by
    obtain ⟨s⟩ := u
    obtain ⟨s'⟩ := v
    congr 1
    funext j
    refine unit_ext (V := LB.wchart 𝔪.D.toPre.P.L φ j) fun y hy => ?_
    choose J hJ using fun χ : (TF (R := V) F).left ⟶ 𝔪.D.toPre.P.A.left =>
      exists_chart 𝔪.D.toPre.P.isLB (χ y)
    exact (gen_trans hu (𝟙 _) y hy (Good.mem hJ φ (𝟙 _))).trans
      ((congrArg _ (h y J hJ)).trans (gen_trans hv (𝟙 _) y hy (Good.mem hJ φ (𝟙 _))).symm)
  have uniq {a b : GtPtF 𝔪.D.toPre F} {y : 𝔪.D.toPre.X}
      (ha : a.IsIota y) (hb : b.IsIota y) : a = b := by
    obtain ⟨ba, va⟩ := (isIota_iff y a).1 ha
    obtain ⟨bb, vb⟩ := (isIota_iff y b).1 hb
    have be : a.b = b.b := ba.trans bb.symm
    cases a with
    | mk a sa hsa za ma =>
      cases b with
      | mk b sb hsb zb mb =>
        cases be
        congr 1
        funext χ
        exact gen_ext (hsa χ) (hsb χ) (fun y J hJ => (va χ y J hJ).trans (vb χ y J hJ).symm)
  obtain ⟨h, hn, hi⟩ := p.eq
  obtain ⟨h', hn', hi'⟩ := p'.eq
  have he : h = h' := uniq hi (hp.symm ▸ hi')
  have hg : (X₁.S.r * X₁.S.N) • p.g = (X₁.S.r * X₁.S.N) • p'.g := by
    rw [← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn,
      ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn', he]
  have iz : GtPtF.IsIota 0 (0 : GtPtF 𝔪.D.toPre F) := by
    have hz : (0 : GtPtF 𝔪.D.toPre F).IsZero := (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl
    obtain ⟨hb, hv⟩ := (isZero_iff _).1 hz
    refine (isIota_iff 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (th 𝔪.D.toPre (T := TF (R := V) F) y J) := isCub_cubV 𝔪.D.toPre.cub hJ
    have tt := tau_mul (𝟙 (TF (R := V) F)) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let q : QkPt 𝔪.D.toPre F (X₁.S.r * X₁.S.N) :=
    ⟨0, p.g - p'.g, 0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by simp [smul_sub, hg]), iz⟩
  have hrel : QkAdd q p' p := by
    refine ⟨p, ?_, ?_, qk_equiv_refl hB p⟩
    · simp [q, hp]
    · apply (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2
      simp [q]
  have hf := hadd _ _ _ hrel
  refine ⟨q, rfl, (hto _ _).2 ?_⟩
  rw [e, e']
  exact ((eq_mul_inv_iff_mul_eq).2 hf.symm).symm

section
variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y} (𝔪 : GMem X₁ z₁ act V ev Y t δ)

theorem yy_sub {a a' : X₁.S.Gam} {mu : Y} (h : 𝔪.YY a mu) (h' : 𝔪.YY a' mu) : 𝔪.YY (a - a') 0 := by
  obtain ⟨p, x, hp, hx, hxa⟩ := h
  obtain ⟨p', x', hp', hx', hxa'⟩ := h'
  obtain ⟨q, hq, hqx⟩ := qkSub X₁ z₁ act V ev Y t δ 𝔪 p p' x x' (hp.trans hp'.symm) hx hx'
  refine ⟨q, x * x'⁻¹, by rw [hq, map_zero], hqx, ?_⟩
  let T := TFK (R := V) (AlgebraicClosure (FractionRing V))
  have e2 : spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) =
      T.hom ≫ spMap 𝔪.yK := by
    simp [T, spMap, jFK, ← Spec.map_comp]
  let U : Over.mk (T.hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) := Over.homMk (T.hom ≫ spMap 𝔪.yK) (by simp)
  have hU : ∀ (b : X₁.S.Gam) (y : T ⟶ 𝔪.A.A),
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt b).left →
      pushHom 𝔪.cart T y = U ≫ X₁.ρ.pt b := fun b y hy => by
    apply Over.OverMorphism.ext
    show y.left ≫ 𝔪.φ = (U ≫ X₁.ρ.pt b).left
    rw [Over.comp_left, hy, e2]
    rfl
  have hpt : X₁.ρ.pt (a - a') = X₁.ρ.pt a * (X₁.ρ.pt a')⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← X₁.ρ.pt_add, sub_add_cancel]
  have key : pushHom 𝔪.cart T (x * x'⁻¹) = U ≫ X₁.ρ.pt (a - a') := by
    rw [map_mul, map_inv, hU a x hxa, hU a' x' hxa', hpt]
    show _ = preHom U _
    rw [map_mul, map_inv]
    rfl
  have e3 := congrArg (fun z => z.left) key
  rw [e2]
  exact e3.trans (Over.comp_left _ _ _ U _)

end

theorem wt_wd : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (sg : ℤˣ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ wt : Y1 → ZMod (X₁.S.r * X₁.S.N), ∀ a mu, 𝔪1.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
  intro I X₁ z₁ act x₀ hD V1 _ _ _ ev1 Y1 _ t1 δ1 𝔪1 sg τ hτ
  classical
  refine ⟨fun mu => if h : ∃ a, 𝔪1.YY a mu then (sg : ℤ) • eStd X₁.S.g _ τ h.choose else 0, ?_⟩
  intro a mu hY
  have h : ∃ a, 𝔪1.YY a mu := ⟨a, hY⟩
  simp only [dif_pos h]
  congr 1
  have hd := yy_sub 𝔪1 h.choose_spec hY
  have hH : h.choose - a ∈ X₁.S.HH X₁.M z₁ :=
    (_root_.GlobalTheory.GSep.mem_HH_iff_yy_zero I X₁ z₁ act x₀ hD V1 ev1 Y1 t1 δ1 𝔪1 _).2 hd
  have h0 : eStd X₁.S.g _ τ (h.choose - a) = 0 := hτ _ hH
  have hs : eStd X₁.S.g _ τ (h.choose - a) = eStd X₁.S.g _ τ h.choose - eStd X₁.S.g _ τ a := by
    simp only [eStd, Pi.sub_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hs, sub_eq_zero] at h0
  exact h0

end GlobalTheory.GSep.WtWd
end

