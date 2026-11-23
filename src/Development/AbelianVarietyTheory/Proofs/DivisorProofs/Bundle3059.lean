module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2825
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2603
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelMemberTermMemMaximalIdeal
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

namespace GlobalTheory.Poinc.Sep.HighTerms


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_integral (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : IsCN V)
    (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (N : ℕ) (hN : 1 ≤ N) (g' : GtPtF D.toPre (FractionRing V))
    (ho : ∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) :
    ∃ g : GtPt D.toPre (𝟙_ (Over (Sp V))),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' := by
  have : CharZero V := hV.2.2.2
  haveI : IsNoetherianRing V := hV.1
  have hR : GlobalTheory.Mum.Base V := ⟨admissibleBase_of_completeNormalLocalCharZero hV, hV.2.2.2⟩
  obtain ⟨M, g₀, x₀, hfin, -, hg₀, huniv, hx₀, hform⟩ :=
    GlobalTheory.ToricTorsionUnif.exists_torsion_toG V hR G D A U N hN
  have hkg : N • g' = 0 := by
    obtain ⟨o, h₁, h₂⟩ := ho
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq N g' o).1 h₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq o).1 h₂)
  obtain ⟨n, hn, -⟩ := huniv _ _ (GlobalTheory.Poinc.TorsLift.gtTors_toT g' hkg)
  have hj : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ M :=
    Over.homMk (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left) (by
      rw [Category.assoc, Over.w n]
      show _ ≫ jFK (R := V) (FractionRing V) ≫ jK V = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V
      rw [← Category.assoc, hj])
  obtain ⟨s, hs⟩ := GlobalTheory.FinDescent.galoisFixed_point_of_finite V hV.2.1 M hfin nb (fun σ => by
    have hσ : spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun r => σ.commutes r
    show spMap σ.toAlgHom.toRingHom ≫ spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ n.left = _
    rw [reassoc_of% hσ]; rfl)
  have hns : n = toUnit _ ≫ s := by
    apply Over.OverMorphism.ext
    apply GlobalTheory.OnePoint.point_ext (spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))))
    refine (congrArg (·.left) hs).trans ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    have e1 : ∀ X : Over (Sp V), (toUnit X).left = X.hom := fun X => by simp
    rw [e1, e1]
    show jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ jFK (R := V) (FractionRing V) ≫ jK V
    rw [← Category.assoc, hj]
  obtain ⟨g, hg⟩ := GlobalTheory.ConstLie.exists_isPull s g₀
  obtain ⟨q, hq⟩ := GlobalTheory.FieldRestrictionTest.exists_isPullF (toUnit (TF (R := V) (FractionRing V))) g
  have h2 := GlobalTheory.FlatTors.TorsMapExists.isPullF_trans hg hq
  rw [← Over.comp_left, ← hns] at h2
  exact ⟨g, by rwa [GlobalTheory.FieldRestrictionTest.isPullF_unique h2 hn] at hq⟩

theorem term_mem_maximalIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C) (mu : Fin 8 → Y1), mu ≠ 0 → T mu c ∈ maximalIdeal V1 := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev X _ m t δ 𝔪 C₀ lab₀ _ T hT c₁ mu₁ hmu₁
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
  obtain ⟨hNu, h0, hdv⟩ := _root_.GlobalTheory.Poinc.IntTerm.unit_ne_zero_dvd g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
  obtain ⟨θ, hθ⟩ := IntTerm.exists_isTheta hV 𝔪.D.toPre
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.degree_one_term_eq_const_mul_psi_mul_theta V 𝔪.D.toPre θ hθ s
  choose υ hυ using 𝔪.psi

  have core : ∀ (a : X₁.S.Gam) (gi : GtPt 𝔪.D.toPre (𝟙_ (Over (Sp V)))) (g' : GtPtF 𝔪.D.toPre (FractionRing V))
      (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b),
      GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left gi g' →
      (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x a) (fr a) →
      ∀ mu, ∃ α : V, coef s g' w (𝔪.e₈ mu) = k * κ * algebraMap V (FractionRing V) (υ mu * mono W t δ mu * α) ∧
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
  have hint := _root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪
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
    obtain ⟨a, ha⟩ := GlobalTheory.T.geometricTorsionPoint_genericFibre_member_has_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 y hy
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
      (fun χ => υ (𝔪.e₈.symm χ) * mono W t δ (𝔪.e₈.symm χ) * a (𝔪.e₈.symm χ) c) (k * κ) _
      (fun χ => by rw [← hco, AddEquiv.apply_symm_apply])
      (fun χ hχ => Ideal.mul_mem_right _ _ (IntTerm.mem_of_psiCoord 𝔪.D (χ := 𝔪.e₈ (𝔪.e₈.symm χ))
        (by rwa [AddEquiv.apply_symm_apply, ← map_zero 𝔪.e₈]) (hυ _)))
      (hlies c 1 le_rfl (w c) (fun _ _ _ => (pow_one _).symm) (hw c) th s _ hs (hth _))
    refine ⟨S, hS, (IntTerm.isUnit_of_sub_mem hm).trans ?_⟩
    simp only [AddEquiv.symm_apply_apply, IntTerm.mono_zero, _root_.mul_one, Units.isUnit_units_mul]
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
  obtain ⟨gi₁, hgi₁⟩ := exists_integral V hV 𝔪.D 𝔪.A 𝔪.G 𝔪.U _ hN (g₀ c₁) (hg₀ c₁).1
  obtain ⟨α, hα, -⟩ := core (lab₀ c₁) gi₁ (g₀ c₁) (ω₀ c₁) hgi₁ (hg₀ c₁).1 (hg₀ c₁).2.1 (hg₀ c₁).2.2 mu₁
  have e₁ := hT mu₁ c₁
  rw [hα, hS0, mul_left_comm, ← map_mul] at e₁
  have e₂ := inj (mul_left_cancel₀ hκ0 e₁)
  have hm : T mu₁ c₁ * S c₀ ∈ maximalIdeal V :=
    e₂ ▸ Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (𝔪.mono_mem hmu₁))
  exact (Ideal.mul_unit_mem_iff_mem _ hS₀).1 hm

end GlobalTheory.Poinc.Sep.HighTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ShortBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hge)
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem one_le_of_ne_zero (T : UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 1 ≤ Dw.p + Dw.q := by
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Nontrivial T.P.D.toPre.X := ⟨x, 0, hx⟩
  have h1 : 0 < Module.finrank (𝓞 E) T.P.D.toPre.X := Module.finrank_pos
  have h2 := UTrait.finrank_le_min E H Dw l Xo c T
  omega

theorem exists_mem_maximalIdeal {C : UCompact Xo c} (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) (hx : x ≠ 0) :
    ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁),
      Real.exp (-(1 / (2 * X₁.S.N) * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le t.T.be (be_pos t.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨yy, hyy⟩ := _root_.GlobalTheory.UPoinc.exists_uIsLabW E H Dw (one_le_of_ne_zero t.T hx) l Xo c C X₁ wi p z₁ t
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR, G, _, α, β, -, -, -, y₀, hat, u, lb, j, hq, -⟩ :=
    hyy.uIsLab
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (X₁.hasDiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one t.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u lb
    (_root_.GlobalTheory.ZH.TestVal.main hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (_root_.GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (_root_.GlobalTheory.ZH.WeightBound.main hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (_root_.GlobalTheory.TestFibre.exists_norm_FF_eq hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
  let α₀ : τ.X := e.symm (j.symm x')
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v)), by
    have h1 := congrArg (fun s => j (e s)) h0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x' x' / 2 := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply]
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    t.y y₀ t.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos t
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (t.T.be x' x' : ℝ) ≤ t.T.be x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x x / 2 :=
    hqle.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsc.le) zero_le_two)
  rw [neg_le_neg_iff]
  refine (div_le_div_of_nonneg_right h1 hNpos.le).trans_eq ?_
  field_simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X' p _
  exact ⟨1 / (2 * X'.S.N), fun z' hz t _ x hx => exists_mem_maximalIdeal X' p z' hz t x hx⟩

end GlobalTheory.UPoinc.ShortBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingTransportGaloisConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

theorem exists_lift_rat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] {R : Subalgebra o Ω}
    {P : PolAV (Sp R)} {G : Over (Sp (ratHull R))} [GrpObj G] {α : G.left ⟶ P.A.left}
    (hα : IsGrpPullback G P.A (spMap (toRat R)) α) {K : Type} [Field K] [CharZero K] (q : Sp K ⟶ P.A.left) :
    ∃ g : Sp K ⟶ G.left, g ≫ α = q := by
  obtain ⟨x', hx', -⟩ := existsUnique_ratPoint R (q ≫ P.A.hom)
  exact ⟨hα.1.lift q x' hx'.symm, hα.1.lift_fst _ _ _⟩

set_option maxHeartbeats 1600000 in
theorem isLab_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs a hG _ p _ z₁ ct y h h' yy hy
  haveI : CharZero D.X.Ω₁ := D.X.ar.char
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, -, hu', hR, G, _, α, β, hα, hβ, hL, y₀, hy₀, u, lb, j, hq, hyy,
    hall⟩ := hy
  obtain ⟨wi, W₀, _, e, k₀, he, hk₀, heβ, htw⟩ :=
    _root_.GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit E H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hS hu' G _ α β hα hβ hL
  obtain ⟨yy₁, hW⟩ := _root_.GlobalTheory.UPoinc.exists_uIsLabW E H Dw hpq l Xo cf C D.X wi p _ (D.lift ct (y ≫ s) h')
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'',
    ⟨m'', hm'', hmβ, hmt⟩, y₁, hy₁, u₁, lb₁, j₁, -, -, -⟩ := hW
  have hk'' : IsGrpPullback W₀ G'' (spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp (ratHull R'').val.toRingHom)) (e ≫ m'') :=
    (he.comp hm'').congr (GalTrans.sp_comp rfl) rfl
  have hββ : k₀ ≫ β = (e ≫ m'') ≫ β'' := by rw [Category.assoc, hmβ, heβ]
  obtain ⟨P₀, ka, ka', hka, hka', lka, lka', htor, hβeq⟩ := GlobalTheory.T.unitaryRechartings_common_geometricFibre E H Dw l Xo cf C D.X (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs p
    (gPt p ≫ y) _ _ ρ' ρ'' hR (by rw [Category.assoc]; exact hR₁) y₀ y₁ hy₀ (by rw [Category.assoc]; exact hy₁) u u₁ u'
    u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ (e ≫ m'') hk₀ hk'' hββ
  obtain ⟨ee, hqe, hlab, hback⟩ := GalTrans.compare u u₁ lb lb₁ P₀ ka ka' hka hka' lka lka'
  have hrN : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  refine ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'', y₁, hy₁,
    u₁, lb₁, ee.symm.trans j, fun χ => ?_, fun x χ hχ => ?_, fun m A pk' pk₂' x' x₂' w w₂ hm hQ' hQ₂' hw hw₂ hA => ?_⟩
  · rw [← ee.apply_symm_apply χ, hqe, ee.apply_symm_apply]
    exact hq (ee.symm χ)
  · obtain ⟨w, hw1, hw2⟩ := hmt x
    obtain ⟨w₀, hw₀, hw₀e, hw₀k⟩ := htw x w hw1
    have c'' : w₀ ≫ (e ≫ m'') ≫ α'' =
        spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp R''.val.toRingHom) ≫ (ρ''.pt x).left := by
      rw [Category.assoc, reassoc_of% hw₀e, hw2, ← Category.assoc, GalTrans.sp_comp rfl]
    obtain ⟨v, xo, xo', hv, hva, hva', hx, hx'⟩ := htor (a x) x w₀ hw₀ hw₀k c''
    obtain ⟨pk, pk', hQ, hQ', hcm⟩ := hlab _ xo xo' v hrN
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ xo hx)
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u₁ _ xo' hx') hv hva hva'
    refine (hyy (a x) pk.y (lb.yy_eq _ pk xo hQ hx)).trans (GalTrans.cm_mk ?_)
    have c2 : CongMod (D.X.S.r * D.X.S.N) χ pk'.y := GalTrans.cm_of_mk (hχ.symm.trans (lb₁.yy_eq x pk' xo' hQ' hx'))
    simpa using GalTrans.cm_symm (GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom (GalTrans.cm_trans c2 hcm))
  · obtain ⟨pk, xo, vo, hQ, -, hvo, hvoa, hvoa', c1⟩ := hback m pk' x' hm hQ'
    obtain ⟨pk₂, xo₂, vo₂, hQ₂, -, hvo₂, hvo₂a, hvo₂a', c2⟩ := hback m pk₂' x₂' hm hQ₂'
    obtain ⟨g, hg⟩ := exists_lift_rat hα (xo.left ≫ u.φ)
    obtain ⟨g₂, hg₂⟩ := exists_lift_rat hα (xo₂.left ≫ u.φ)
    have e1 : g ≫ β = w ≫ β'' := hβeq vo g w hvo (by rw [hg, ← hvoa, Category.assoc])
      (by rw [hw, ← hvoa', Category.assoc])
    have e2 : g₂ ≫ β = w₂ ≫ β'' := hβeq vo₂ g₂ w₂ hvo₂ (by rw [hg₂, ← hvo₂a, Category.assoc])
      (by rw [hw₂, ← hvo₂a', Category.assoc])
    have hA' : g₂ ≫ β = g ≫ β ≫ (Xo.univ.t.act.act A).left := by
      rw [e2, hA, ← Category.assoc, ← e1, Category.assoc]
    have c3 := hall m A pk pk₂ xo xo₂ g g₂ hm hQ hQ₂ hg hg₂ hA'
    have c4 : CongMod m ((ee.symm.trans j) pk₂'.y) (j pk₂.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c2
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk₂.y) = j pk₂.y from
        congrArg j (ee.symm_apply_apply pk₂.y)] at this
    have c5 : CongMod m ((ee.symm.trans j) pk'.y) (j pk.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c1
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk.y) = j pk.y from
        congrArg j (ee.symm_apply_apply pk.y)] at this
    have c6 : CongMod m (A • j pk.y) (A • (ee.symm.trans j) pk'.y) :=
      GalTrans.cm_symm (GalTrans.cm_map (DistribSMul.toAddMonoidHom _ A) c5)
    exact GalTrans.cm_trans c4 (GalTrans.cm_trans c3 c6)

end GlobalTheory.UPoinc.UGalTrans
end
end

