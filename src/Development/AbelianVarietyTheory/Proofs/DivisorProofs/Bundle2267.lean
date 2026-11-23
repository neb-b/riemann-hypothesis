module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalPolarisationGenericFibreTwoTorsio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwistAV

open GlobalTheory.CechPic (cls pull)

section

variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G]

def genSec (a : 𝟙_ (Over (Sp R)) ⟶ G) : 𝟙_ (Over (Sp (FractionRing R))) ⟶ (Over.pullback (jK R)).obj G :=
  Over.homMk (pullback.lift (jK R ≫ a.left) (𝟙 _) (by
    rw [Category.assoc, Over.w a]; simp)) (pullback.lift_snd _ _ _)

theorem genSec_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (genSec a).left ≫ pullback.fst G.hom (jK R) = jK R ≫ a.left :=
  pullback.lift_fst _ _ _

theorem const_fst (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (toUnit ((Over.pullback (jK R)).obj G) ≫ genSec a).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ G.hom ≫ a.left := by
  rw [Over.comp_left, Category.assoc, genSec_fst, ← Category.assoc (pullback.fst G.hom (jK R)), pullback.condition]
  rfl

theorem hom_ext_gen {T : Over (Sp (FractionRing R))} {x y : T ⟶ (Over.pullback (jK R)).obj G}
    (h : x.left ≫ pullback.fst G.hom (jK R) = y.left ≫ pullback.fst G.hom (jK R)) : x = y :=
  Over.OverMorphism.ext ((isGrpPullback_pullback G (jK R)).1.hom_ext h (by
    show x.left ≫ ((Over.pullback (jK R)).obj G).hom = y.left ≫ ((Over.pullback (jK R)).obj G).hom
    rw [Over.w, Over.w]))

theorem genSec_sq (a : 𝟙_ (Over (Sp R)) ⟶ G) (ha : a ^ 2 = 1) : genSec a * genSec a = 1 := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let T : Over (Sp (FractionRing R)) := 𝟙_ _
  let x₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ a
  have hx : x₀.left = (genSec a).left ≫ pullback.fst G.hom (jK R) := by
    rw [genSec_fst]; rfl
  have e := hp T (genSec a) (genSec a) x₀ x₀ hx hx
  have haa : x₀ * x₀ = toUnit _ ≫ η[G] := by
    rw [← MonObj.comp_mul, ← sq, ha, Hom.one_def, ← Category.assoc, comp_toUnit]
  set c := genSec a * genSec a with hc
  let y₀ : Over.mk (T.hom ≫ jK R) ⟶ G := toUnit _ ≫ η[G]
  have hy : y₀.left = c.left ≫ pullback.fst G.hom (jK R) := by rw [show y₀ = x₀ * x₀ from haa.symm, e]
  have e₂ := hp T c c y₀ y₀ hy hy
  have hyy : y₀ * y₀ = y₀ := by
    rw [show y₀ = 1 from Hom.one_def.symm, _root_.one_mul]
  have hcc : c * c = c := hom_ext_gen (by rw [← e₂, hyy, hy])
  exact mul_eq_left.1 hcc

theorem transl_fst [IsCommMonObj G] (a : 𝟙_ (Over (Sp R)) ⟶ G) :
    (GlobalTheory.PolTranslate.transl (genSec a)).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G.hom (jK R) ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
  have hp := (isGrpPullback_pullback G (jK R)).2
  let GK := (Over.pullback (jK R)).obj G
  let p : Over.mk (GK.hom ≫ jK R) ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
  have e := hp GK (𝟙 GK) (toUnit GK ≫ genSec a) p (p ≫ toUnit G ≫ a) (by simp [p])
    (by rw [const_fst]; rfl)
  have e' : p * (p ≫ toUnit G ≫ a) = p ≫ ((toUnit G ≫ a) * 𝟙 G) := by
    rw [MonObj.comp_mul, Category.comp_id, _root_.mul_comm]
  rw [e', Over.comp_left] at e
  exact e.symm

end

theorem exists_translate_pol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (A₂ : PolAV (Sp (FractionRing R))) (gen₂ : (Over.pullback (jK R)).obj G ≅ A₂.A), IsMonHom gen₂.hom ∧ LBIso (A₂.L.pull gen₂.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D A G _ _ _ U a ha P hP
  haveI := U.gen_hom
  haveI := A.isAb.comm
  haveI : IsProper A.A.hom := A.isAb.proper
  let b := genSec a
  let a' : 𝟙_ (Over (Sp (FractionRing R))) ⟶ A.A := b ≫ U.gen.hom
  have ha' : a' * a' = 1 := by
    show (b ≫ U.gen.hom) * (b ≫ U.gen.hom) = 1
    rw [← MonObj.mul_comp, genSec_sq a ha, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  let A₂ : PolAV (Sp (FractionRing R)) :=
    { A := A.A
      isAb := A.isAb
      g := A.g
      smoothDim := A.smoothDim
      L := GlobalTheory.RigidTranslate.rigTransl A.L a'
      isLB := LB.isLB_linComb A.isLB _ _
      rigid := GlobalTheory.RigidTranslate.rigidified_rigTransl A.isLB
      sym := GlobalTheory.RigidTranslate.sym_rigTransl ha' A.isLB A.sym
      ample := GlobalTheory.RigidTranslate.relAmple_rigTransl_of_section a' A.isLB A.ample
      ktriv := GlobalTheory.RigidTranslate.kTriv_rigTransl_any _ _ _ A.isLB a' A.ktriv }
  refine ⟨A₂, U.gen, U.gen_hom, ?_⟩
  let f := pullback.fst G.hom (jK R)
  let τ := ((toUnit G ≫ a) * 𝟙 G).left
  have hLG := U.LG.isLB
  have hext : pull U.gen.hom.left (cls A.L A.isLB) = pull f (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hLG _)).2 U.ext
  have hP' : cls P.L.L P.L.isLB = pull τ (cls U.LG.L hLG) :=
    (GlobalTheory.CechPic.cls_eq_iff P.L.isLB (pull_isLB hLG _)).2 hP
  have hrig : pull (eSec G) (cls P.L.L P.L.isLB) = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB P.L.isLB _)).2 ⟨P.L.rig, P.L.rigGen⟩
  have ea : a.left = eSec G ≫ τ := by
    show a.left = (η[G] ≫ ((toUnit G ≫ a) * 𝟙 G)).left
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [MonObj.comp_mul, ← Category.assoc, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Category.id_comp, Category.comp_id,
      h1, _root_.mul_one]
  have hgt : U.gen.hom.left ≫ (GlobalTheory.PolTranslate.transl a').left =
      (GlobalTheory.PolTranslate.transl b).left ≫ U.gen.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PolTranslate.comp_transl, GlobalTheory.PolTranslate.transl, MonObj.mul_comp,
      Category.id_comp]
    rfl
  have hgc : U.gen.hom.left ≫ (toUnit A.A ≫ a').left = (toUnit _ ≫ b).left ≫ U.gen.hom.left := by
    rw [GlobalTheory.RigidTranslate.comp_const, ← Over.comp_left]
    rfl
  have h₁ := pull_isLB (LB.isLB_linComb A.isLB (K := Fin 2)
    ![(GlobalTheory.PolTranslate.transl a').left, (toUnit A.A ≫ a').left] ![1, -1]) U.gen.hom.left
  refine (GlobalTheory.CechPic.cls_eq_iff h₁ (pull_isLB P.L.isLB _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull _ _ h₁, GlobalTheory.CechPic.cls_linComb A.isLB, GlobalTheory.CechPic.cls_pull P.L.isLB]
  · rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg, map_sub]
    rw [← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, hgt, hgc, GlobalTheory.CechPic.pull_comp, GlobalTheory.CechPic.pull_comp, hext,
      ← GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.pull_comp, transl_fst a, const_fst a, GlobalTheory.CechPic.pull_comp,
      GlobalTheory.CechPic.pull_comp f, GlobalTheory.CechPic.pull_comp, ea, GlobalTheory.CechPic.pull_comp, ← hP', hrig, map_zero, map_zero, sub_zero]
  · exact LB.isLB_linComb A.isLB _ _

end GlobalTheory.TwistAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiGeneratorsDegenerationLawsSymmetricBala
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UTau0

theorem formEq_psi {R : Type} [CommRing R] [IsDomain R] (D₀ : DegPre R) (f : D₀.P.A ⟶ D₀.P.A) [IsMonHom f]
    (x x' : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) (hx : x' = x ≫ f) :
    FormEq (Sum.elim (Sum.elim (PolDeg.lamPts x x') fun k => x.left ≫ w0φ D₀ f k) fun _ : PUnit => eSec D₀.P.A)
      (Sum.elim (Sum.elim PolDeg.negε w0ε) fun _ => (-1 : ℤ)) (fun _ : PUnit => x.left) (fun _ => (-1 : ℤ)) := by
  intro U _ h
  subst hx
  have m₁ : x ≫ padd D₀.P.A (𝟙 _) f = x * (x ≫ f) := (MonObj.comp_mul _ _ _).trans (by simp)
  have m₃ : x ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]) = 1 := by
    rw [← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit _), ← Hom.one_def]
  have m₄ : (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A) = η[D₀.P.A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have e₁ : x.left ≫ (padd D₀.P.A (𝟙 _) f).left = (x * (x ≫ f)).left := by rw [← Over.comp_left, m₁]
  have e₂ : x.left ≫ f.left = (x ≫ f).left := (Over.comp_left _ _ _ _ _).symm
  have e₃ : x.left ≫ (toUnit D₀.P.A ≫ η[D₀.P.A]).left = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by
    rw [← Over.comp_left, m₃]
  have e₄ : eSec D₀.P.A = (1 : 𝟙_ (Over (Sp R)) ⟶ D₀.P.A).left := by rw [m₄]; rfl
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
    PolDeg.lamPts, PolDeg.negε, w0φ, w0ε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem exists_psi_rLaws : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ w0 : O, w0 + star w0 = 1 → ∀ uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ τ' : ∀ y z : D₀.X, LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.PolDeg.lamPts (D₀.c y) (D₀.c z)) GlobalTheory.PolDeg.negε),
    GlobalTheory.UTau0.BalTau ⟨D₀.P.L, D₀.rig, D₀.P.isLB, D₀.rig_gen⟩ D₀.cub onB.toRingAct D₀.c τ' →
    (∀ y z p J, Good D₀.P.L p J → val (τ' y z) (𝟙 _) p J = val (τ' z y) (𝟙 _) p J) →
    ∃ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
      GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ := by
  intro R _ _ _ D₀ O _ _ _ onB hc w0 hw uw huw uw0 τ' hbal hsym
  haveI := onB.hom w0
  haveI := onB.hom (star w0)
  obtain ⟨u, hu, hu0⟩ := exists_ros GlobalTheory.globalFns_holds D₀.P.isAb D₀.P.isLB (onB.act w0) (onB.act (star w0))
    (onB.rosati w0)
  have hfg : padd D₀.P.A (onB.act w0) (onB.act (star w0)) = 𝟙 _ := by
    rw [← onB.map_add, hw, onB.map_one]
  have cadd : ∀ a b, D₀.c (a + b) = D₀.c a * D₀.c b := fun a b => D₀.c_add a b
  have c0 : D₀.c 0 = 1 := by
    have := cadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have cneg : ∀ a, D₀.c (-a) = (D₀.c a)⁻¹ := fun a =>
    eq_inv_of_mul_eq_one_left (by rw [← cadd, neg_add_cancel, c0])
  let t := fun y : D₀.X => LB.mulGen D₀.P.L _ _ _ _
    (LB.mulGen D₀.P.L _ _ _ _ (τ' y (w0 • y)) (LB.pullGen D₀.P.L _ _ uw (D₀.c y).left))
    (LB.invGen D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => 1) D₀.rig)
  have ht : ∀ y, (t y).IsGen := fun y => DVR.mulGen_isGen _ _ _ _ _ _ _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hbal.1 y _) (DVR.pullGen_isGen _ _ _ _ huw _))
    (DVR.invGen_isGen _ _ _ _ D₀.rig_gen)
  choose ψ hψ hψv using fun y => exists_gen D₀.P.isLB (formEq_psi D₀ (onB.act w0) (D₀.c y) _ (hc w0 y)) (t y) (ht y)
  have Vψ : ∀ y p J, Good D₀.P.L p J → val (ψ y) (𝟙 _) p J =
      val (τ' y (w0 • y)) (𝟙 _) p J * val uw (D₀.c y).left p J * (rigV D₀ p J)⁻¹ := by
    intro y p J hJ
    rw [hψv y _ _ p J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp]
    rfl
  have key : ∀ y z p J, Good D₀.P.L p J → tauV D₀ ψ p J y z = val (τ' y z) (𝟙 _) p J := by
    intro y z p J hJ
    have e1 := hbal.2.1 y z (w0 • y + w0 • z) p J hJ
    have e2 := hbal.2.2.1 y (w0 • y) (w0 • z) p J hJ
    have e3 := hbal.2.2.1 z (w0 • y) (w0 • z) p J hJ
    have e4 := hsym z (w0 • y) p J hJ
    have e5 := hbal.2.2.2 w0 u hu hu0 y z p J hJ
    have e6 := hbal.2.2.1 y (w0 • z) (star w0 • z) p J hJ
    rw [← add_smul, hw, one_smul] at e6
    have g := _root_.GlobalTheory.UTau0.SecondDiff.uw_second_diff R D₀ (onB.act w0) (onB.act (star w0)) hfg uw huw uw0 u hu hu0 _ (D₀.c y) (D₀.c z) p J hJ
    simp only [cadd, hc] at e1 e2 e3 e6
    unfold tauV
    rw [Vψ _ p J hJ, Vψ _ p J hJ, Vψ _ p J hJ, smul_add]
    simp only [cadd]
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E e1; have a2 := E e2; have a3 := E e3; have a4 := E e4; have a5 := E e5; have a6 := E e6
    have b1 := E g
    simp only [ofMul_mul, ofMul_inv] at a1 a2 a3 a4 a5 a6 b1 ⊢
    linear_combination (norm := abel) a1 + a2 + a3 + b1 + a4 + a5 - a6
  refine ⟨ψ, hψ, ?_, ?_, ?_, ?_⟩
  · intro y y' z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.1 y y' z p J hJ
  · intro y p J hJ
    have C := isCub_cubV D₀.cub hJ
    rw [Vψ _ p J hJ, Vψ _ p J hJ, smul_neg]
    have f1 := hbal.2.1 y (-y) (w0 • y) p J hJ
    have z1 := hbal.2.1 0 0 (w0 • y) p J hJ
    have f2 := hbal.2.2.1 (-y) (w0 • y) (-(w0 • y)) p J hJ
    have z2 := hbal.2.2.1 (-y) 0 0 p J hJ
    rw [add_neg_cancel] at f1 f2
    rw [add_zero] at z1 z2
    have g := _root_.GlobalTheory.UTau0.uw_even_val R D₀ (onB.act w0) uw huw uw0 _ (D₀.c y) p J hJ
    simp only [cneg, hc, c0] at f1 z1 f2 z2 ⊢
    rw [C.face] at z1 z2
    apply Additive.ofMul.injective
    have E := fun {a b : ((𝟙_ (Over (Sp R))).left.presheaf.stalk p)ˣ} (e : a = b) => congrArg Additive.ofMul e
    have a1 := E f1; have a2 := E f2; have a3 := E z1; have a4 := E z2; have b1 := E g
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a1 a2 a3 a4 b1 ⊢
    linear_combination (norm := abel) b1 + a1 - a2 + a3 - a4
  · intro a u' hu' hu0' y z p J hJ
    rw [key _ _ p J hJ, key _ _ p J hJ]
    exact hbal.2.2.2 a u' hu' hu0' y z p J hJ
  · intro y p J hJ
    rw [key _ _ p J hJ, Vψ _ p J hJ, inv_mul_cancel_right]

end GlobalTheory.UTau0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackEighthPowerEndomorphismsFieldPoint
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.DiagPull


open MonObj in
theorem isDiagEnd_pull {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    {T T' : Scheme.{0}} (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hφ : IsGrpPullback P'.A P.A f φ) (hL : LBIso P'.L (P.L.pull φ))
    (hε' : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left) : IsDiagEnd F W P' (f ≫ u) ε' := by
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hε⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  refine ⟨c', hc'u, pr', hmon, huniv', ?_, fun E a => injψ ?_⟩
  swap
  · have e₁ : pushPt hφ.1.w (ε' E) = pushPt hφ.1.w (𝟙 P'.A) ≫ ε E := Over.OverMorphism.ext (by
      show (ε' E).left ≫ φ = ((𝟙 P'.A : P'.A ⟶ P'.A).left ≫ φ) ≫ (ε E).left
      rw [hε', Over.id_left, Category.id_comp])
    rw [push_comp, e₁, Category.assoc, hε]
    change diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A)) _ = pushHom hψ _ _
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    refine (map_zpow (diagPrecomp (M := c.A) (pushPt hφ.1.w (𝟙 P'.A))) (pr b) (E a b)).trans
      (Eq.trans ?_ (map_zpow (pushHom hψ P'.A) (pr' b) (E a b)).symm)
    congr 1
    have e₂ := push_comp (𝟙 P'.A) b
    rw [Category.id_comp] at e₂
    exact e₂.symm
  let ε₀ : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c.P q ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε₀
  have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε₀
  have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε₀).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε₀
  have l3 : (LB.LinComb c'.P q' ε₀).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε₀
  have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε₀).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
  have i3 : LBIso ((LB.LinComb c.P q ε₀).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) :=
    LBIso.chartPull (chartPullOut c.P q ε₀ φ _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε₀) (LB.LinComb (c.P.pull ψ₂) q' ε₀) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε₀ (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε₀) (LB.LinComb c'.P q' ε₀) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε₀
  have h1 := pull_isLB P.isLB φ
  have h2 := pull_isLB l0 φ
  exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

theorem exists_pull_field : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] (P : PolAV (Sp R)) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (u' : Sp R ⟶ F.X), IsDiagEnd F W P u' ε → ∀ (K : Type) [Field K] (yK : R →+* K), ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ P.A.left) (_ : IsGrpPullback A.A P.A (spMap yK) φ) (_ : LBIso A.L (P.L.pull φ)) (εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A)), IsDiagEnd F W A (spMap yK ≫ u') εA ∧ ∀ (Y : Over (Sp K)) (x x' : Y ⟶ A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), x'.left ≫ φ = x.left ≫ φ ≫ (ε E).left → x' = x ≫ εA E := by
  intro g n F W R _ P ε u' hS K _ yK
  let A : PolAV (Sp K) := by
    open GlobalTheory GlobalTheory.Ex GlobalTheory.ModelData GlobalTheory.DegPull in
      exact {
        A := (Over.pullback (spMap yK)).obj P.A
        isAb := TLinPf.isAb_pullback (spMap yK) P.A P.isAb
        g := P.g
        smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
          (isGrpPullback_pullback P.A (spMap yK)).1 P.smoothDim
        L := P.L.pull (pullback.fst P.A.hom (spMap yK))
        isLB := pull_isLB P.isLB _
        rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A (spMap yK)) P.rigid
        sym := PolBaseChange.sym_pull (isGrpPullback_pullback P.A (spMap yK)) P.sym
        ample := by
          haveI := P.isAb.proper
          exact AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom (spMap yK))
        ktriv := by
          obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom (spMap yK)))
          exact kTriv_pull (isGrpPullback_pullback P.A (spMap yK)) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  let φ : A.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap yK)
  have hφ : IsGrpPullback A.A P.A (spMap yK) φ := isGrpPullback_pullback P.A (spMap yK)
  have hL : LBIso A.L (P.L.pull φ) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ A.isLB
  have w : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = A.A.hom ≫ spMap yK := fun E => by
    rw [Category.assoc, Over.w, hφ.1.w]
  let εA : Matrix (Fin 8) (Fin 8) ℤ → (A.A ⟶ A.A) := fun E =>
    Over.homMk (hφ.1.lift (φ ≫ (ε E).left) A.A.hom (w E)) (hφ.1.lift_snd _ _ _)
  have hεA : ∀ E, (εA E).left ≫ φ = φ ≫ (ε E).left := fun E => hφ.1.lift_fst _ _ _
  refine ⟨A, φ, hφ, hL, εA, isDiagEnd_pull F W P A u' (spMap yK) φ ε εA hS hφ hL hεA, fun Y x x' E h => ?_⟩
  refine Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  rw [h, Over.comp_left, Category.assoc, hεA]

end GlobalTheory.Poinc.DiagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutFaithfullyFlat
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_pushout_faithfullyFlat : ∀ (R : Type) [CommRing R] (D D' E : Type) [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E] (ψ : D →ₐ[R] D') (φ : D →ₐ[R] E), (ψ : D →+* D').FaithfullyFlat → ∃ (E' : Type) (_ : CommRing E') (_ : Algebra R E') (ψ' : E →ₐ[R] E') (φ' : D' →ₐ[R] E'), (ψ' : E →+* E').FaithfullyFlat ∧ ψ'.comp φ = φ'.comp ψ := by
  intro R _ D D' E _ _ _ _ _ _ ψ φ hψ
  letI : Algebra D E := φ.toRingHom.toAlgebra
  letI : Algebra D D' := ψ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat D D' := hψ
  let f : E →+* TensorProduct D E D' := Algebra.TensorProduct.includeLeftRingHom
  let g : D' →+* TensorProduct D E D' := (Algebra.TensorProduct.includeRight : D' →ₐ[D] _).toRingHom
  have hfg : f.comp (algebraMap D E) = g.comp (algebraMap D D') :=
    RingHom.ext fun d => by
      change (algebraMap D E d) ⊗ₜ[D] (1 : D') = (1 : E) ⊗ₜ[D] algebraMap D D' d
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  letI iR : Algebra R (TensorProduct D E D') := (f.comp (algebraMap R E)).toAlgebra
  have hf : f.FaithfullyFlat := by
    have : Module.FaithfullyFlat E (TensorProduct D E D') := inferInstance
    exact (RingHom.faithfullyFlat_algebraMap_iff).2 this
  refine ⟨TensorProduct D E D', inferInstance, iR,
    { f with commutes' := fun r => rfl },
    { g with commutes' := fun r => ?_ }, hf, ?_⟩
  · change g (algebraMap R D' r) = f (algebraMap R E r)
    rw [← ψ.commutes r, ← φ.commutes r]
    exact (congrArg (fun h => h (algebraMap R D r)) hfg).symm
  · ext d
    exact congrArg (fun h => h d) hfg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens) (U : X.Opens), (∀ j, W j ≤ U) → U ≤ ⨆ j, W j → ∀ F : PtFn s, (∀ j, IsNat (W j) F) → ∃ f : Γ(X, U), ∀ (j : J) (P : Pt s), P.In (W j) → F P = valR P.x U f := by
  first | exact @GlobalTheory.CechKS.exists_sec_of_isNat | exact GlobalTheory.CechKS.exists_sec_of_isNat | (intros; apply GlobalTheory.CechKS.exists_sec_of_isNat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'], IsAdicComplete (maximalIdeal R') R' → ∀ (ρ : R →+* R') (U : Over (Sp R)), Smooth U.hom → ∀ (x₀ : Sp (ResidueField R') ⟶ U.left), x₀ ≫ U.hom = spMap ((residue R').comp ρ) → ∀ O : U.left.Opens, Set.range x₀ ⊆ O → ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.HenselLift.exists_lift_mem_open | exact GlobalTheory.HenselLift.exists_lift_mem_open | (intros; apply GlobalTheory.HenselLift.exists_lift_mem_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPosStatement
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
end

