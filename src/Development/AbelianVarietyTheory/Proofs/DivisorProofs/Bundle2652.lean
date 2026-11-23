module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.DualAbelianSchemes.TrivLocusFlat
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem pull_inv_cls {R : Type} [CommRing R] [IsLocalRing R] (P : PolAV (Sp R)) :
    pull (GrpObj.inv : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  obtain ⟨U, hU, t, ht⟩ := P.sym (IsLocalRing.closedPoint R)
  obtain rfl : U = ⊤ := DVR.eq_top_of_closedPoint_mem U hU
  have h := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 ⟨t, ht⟩
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul, pull_comp] at h
  obtain ⟨m, hm⟩ : ∃ m : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme, m ≫ (P.A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ :=
    ⟨P.A.left.topIso.inv, P.A.left.topIso.inv_hom_id⟩
  have h' := congrArg (pull m) h
  rw [map_add (f := _), map_neg, map_zero, ← pull_comp m, ← pull_comp m, hm, pull_id, pull_id, add_neg_eq_zero] at h'
  exact h'

theorem pull_one_eq_zero {R : Type} [CommRing R] [IsLocalRing R] {G Y : Over (Sp R)} [GrpObj G] (d : Pic G.left) :
    pull (1 : Y ⟶ G).left d = 0 := by
  have e : (1 : Y ⟶ G) = toUnit Y ≫ η[G] := rfl
  rw [e, Over.comp_left, pull_comp, GlobalTheory.DualOpen.pic_sp_local_eq_zero R (pull η[G].left d), map_zero]

theorem exists_translate_of_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D₀ D : DegPre R)
  (β : D₀.P.A ≅ D.P.A), IsMonHom β.hom →
  (∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
      ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
    wΛ.IsGen) →
  ∃ b : 𝟙_ (Over (Sp R)) ⟶ D.P.A, padd D.P.A b b = η[D.P.A] ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β.hom b) GlobalTheory.MumCmp.twε), w.IsGen := by
  intro R _ _ _ _ D₀ D β hβ hw
  have := D.P.isAb.comm
  have := D₀.P.isAb.comm
  have hL₀ := D₀.P.isLB
  have hL := D.P.isLB
  set c₀ := cls D₀.P.L hL₀ with hc₀
  set c := cls D.P.L hL with hc
  have hd : IsDual D.P.A D.P.A (abelian₂ D.P.A D.P.L) :=
    CompanionTheory.PfDual.kTrivDual R D.P.A D.P.g D.P.isAb D.P.smoothDim D.P.L hL D.P.ktriv
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := hd.isLB
  have e : ∀ (Y : Over (Sp R)) (a t : Y ⟶ D.P.A), evc hΛ a t = lam c a t := fun Y a t ↦ by
    rw [evc, show cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) from
      cls_cube_two hL _ _ hΛ, pull_lam, lift_fst, lift_snd]
  have l₁ : ∀ (Y : Over (Sp R)) (a a' t : Y ⟶ D.P.A), lam c (a * a') t = lam c a t + lam c a' t :=
    fun Y a a' t ↦ by
      rw [← e, ← e, ← e]
      exact (isAdditive_iff hΛ).1 hd.additive Y a a' t
  have l₂ : ∀ (Y : Over (Sp R)) (a t t' : Y ⟶ D.P.A), lam c a (t * t') = lam c a t + lam c a t' :=
    fun Y a t t' ↦ by rw [lam_comm, l₁, lam_comm _ t, lam_comm _ t']

  obtain ⟨wΛ, hwΛ⟩ := hw
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := LB.isLB_linComb hL₀ _ _
  have eΛ : lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) =
      lam c (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) := by
    have h := (cls_eq_iff hΛ₀ (pull_isLB hΛ _)).2 ⟨wΛ, hwΛ⟩
    have h₁ : cls _ hΛ₀ = lam c₀ (fst D₀.P.A D₀.P.A) (snd D₀.P.A D₀.P.A) := cls_cube_two hL₀ _ _ hΛ₀
    have h₂ : cls _ hΛ = lam c (fst D.P.A D.P.A) (snd D.P.A D.P.A) := cls_cube_two hL _ _ hΛ
    rw [← h₁, h, cls_pull hΛ, h₂, pull_lam, lift_fst, lift_snd]
  have s₁ : ∀ (Y : Over (Sp R)) (u v : Y ⟶ D₀.P.A), lam c₀ u v = lam c (u ≫ β.hom) (v ≫ β.hom) := fun Y u v ↦ by
    have h := congrArg (pull (lift u v).left) eΛ
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h

  have Fadd : ∀ (Y : Over (Sp R)) (a a' : Y ⟶ D.P.A),
      pull ((a * a') ≫ β.inv).left c₀ - pull (a * a').left c =
        (pull (a ≫ β.inv).left c₀ - pull a.left c) + (pull (a' ≫ β.inv).left c₀ - pull a'.left c) := by
    intro Y a a'
    have h := s₁ Y (a ≫ β.inv) (a' ≫ β.inv)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, lam, pull_one_eq_zero, add_zero] at h
    rw [MonObj.mul_comp, ← sub_eq_zero]
    have h' := sub_eq_zero.2 h
    convert h' using 1
    abel
  let N : LB (D.P.A ⊗ 𝟙_ (Over (Sp R))).left :=
    tens (D₀.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left)
      (dual (D.P.L.pull (fst D.P.A (𝟙_ (Over (Sp R)))).left))
  have hN : N.IsLB := isLB_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _))
  have clsN : cls N hN = pull (fst D.P.A (𝟙_ (Over (Sp R))) ≫ β.inv).left c₀ -
      pull (fst D.P.A (𝟙_ (Over (Sp R)))).left c := by
    rw [show cls N hN = _ from cls_tens (pull_isLB hL₀ _) (isLB_dual (pull_isLB hL _)) hN,
      cls_dual (pull_isLB hL _), cls_pull hL₀, cls_pull hL, sub_eq_add_neg]
  have evN : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A) (t : Y ⟶ 𝟙_ (Over (Sp R))),
      evc hN a t = pull (a ≫ β.inv).left c₀ - pull a.left c := by
    intro Y a t
    rw [evc, clsN, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, lift_fst_assoc, lift_fst]
  have hadd : IsAdditive N := (isAdditive_iff hN).2 fun Y a a' t ↦ by rw [evN, evN, evN, Fadd]
  obtain ⟨b, hb, -⟩ := hd.univ _ N hN hadd
  have eb := (cls_eq_iff hN (pull_isLB hΛ _)).2 hb
  have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A),
      pull (a ≫ β.inv).left c₀ - pull a.left c = lam c a (toUnit Y ≫ b) := by
    intro Y a
    have h : evc hN a (toUnit Y) = evc hΛ a (toUnit Y ≫ b) := by
      have h := congrArg (pull (lift a (toUnit Y)).left) eb
      rw [cls_pull hΛ] at h
      change evc hN a (toUnit Y) = pull (lift a (toUnit Y)).left
        (evc hΛ (fst D.P.A (𝟙_ (Over (Sp R)))) (snd D.P.A (𝟙_ (Over (Sp R))) ≫ b)) at h
      rw [pull_evc, lift_fst, lift_snd_assoc] at h
      exact h
    rw [← evN Y a (toUnit Y), h, e]
  refine ⟨b, ?_, ?_⟩
  ·
    have sym₀ : pull (GrpObj.inv : D₀.P.A ⟶ D₀.P.A).left c₀ = c₀ := pull_inv_cls D₀.P
    have sym : pull (GrpObj.inv : D.P.A ⟶ D.P.A).left c = c := pull_inv_cls D.P
    have odd : ∀ (Y : Over (Sp R)) (a : Y ⟶ D.P.A), lam c a (toUnit Y ≫ b) + lam c a (toUnit Y ≫ b) = 0 := by
      intro Y a
      have ia : a⁻¹ = a ≫ GrpObj.inv := rfl
      have ia' : (a ≫ β.inv)⁻¹ = (a ≫ β.inv) ≫ GrpObj.inv := rfl
      have h₁ : lam c a⁻¹ (toUnit Y ≫ b) = lam c a (toUnit Y ≫ b) := by
        rw [← key, ← key, GrpObj.inv_comp, ia, ia']
        simp only [Over.comp_left, pull_comp, sym₀, sym]
      have h₂ : lam c (a⁻¹ * a) (toUnit Y ≫ b) = 0 := by rw [inv_mul_cancel, lam_one_left]
      rw [l₁, h₁] at h₂
      exact h₂
    have two : b * b = 1 := by
      refine hd.eq_one (b * b) ((triv_ev_iff hΛ _ _).2 ?_)
      have hs : snd D.P.A (𝟙_ (Over (Sp R))) = toUnit _ := toUnit_unique _ _
      rw [e, hs, MonObj.comp_mul, l₂, odd]
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = η[D.P.A] := by
      rw [show (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A) = toUnit _ ≫ η[D.P.A] from rfl,
        toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    exact two.trans e₁
  ·
    have hC : (LB.LinComb D.P.L (twφ D₀ D β.hom b) twε).IsLB := LB.isLB_linComb hL _ _
    refine (cls_eq_iff hL₀ hC).1 ?_
    have h := key D₀.P.A β.hom
    rw [Iso.hom_inv_id, Over.id_left, pull_id, sub_eq_iff_eq_add] at h
    have e₁ : padd D.P.A β.hom (toUnit D₀.P.A ≫ b) = β.hom * (toUnit D₀.P.A ≫ b) := rfl
    have e₂ : toUnit D₀.P.A ≫ η[D.P.A] = 1 := rfl
    rw [cls_linComb hL, Fin.sum_univ_three]
    simp only [twφ, twε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, one_smul, neg_smul, e₁, e₂]
    rw [← hc, ← hc₀, h, lam]
    abel

end GlobalTheory.MumCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProduct
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem fam_mul_Oinv {H : Type} [CommGroup H] (Ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → H)
    (α : D.toPre.X) :
    (∏ a, Ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, Ω (Oφl U e α a) ^ Oinvε a =
      Ω (pGl U e) ^ k := by
  have a₀ : (pGl U e) ≫ D.toPre.famφB α 0 = (pGl U e) := Category.comp_id _
  have a₁ : (pGl U e) ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : (pGl U e) ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : (pGl U e) ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = (pGl U e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

theorem sval_eq_sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) :
    sval σ q z N = sv U k σ q z (N q) :=
  sval_of σ q z N (fun _ => N q) (fun _ => congrArg N (Category.comp_id _))

end

theorem exp_alg {A X X₁ X₂ : Type} [CommRing A] (k : ℕ) (E : X ≃ X₁ × X₂) (S₁ : Finset X₁) (S₂ : Finset X₂)
    {oM oL W W₁ W₂ : Aˣ} {s s₁ s₂ : A} {f : X → A} {f₁ : X₁ → A} {f₂ : X₂ → A} {t a b : X → Aˣ} {t₁ : X₁ → Aˣ}
    {t₂ : X₂ → Aˣ} (hW : oM * W = W₁ * W₂ * oL) (hs : (oL ^ k).val * s = s₁ * s₂)
    (hf : ∀ x, (a x).val * f x = f₁ (E x).1 * f₂ (E x).2) (ht : ∀ x, b x * t x = t₁ (E x).1 * t₂ (E x).2)
    (ho : ∀ x, a x * b x = oM ^ k) (H₁ : (W₁ ^ k).val * s₁ = ∑ x ∈ S₁, f₁ x * (t₁ x).val)
    (H₂ : (W₂ ^ k).val * s₂ = ∑ x ∈ S₂, f₂ x * (t₂ x).val) :
    (W ^ k).val * s = ∑ x ∈ (S₁ ×ˢ S₂).map E.symm.toEmbedding, f x * (t x).val := by
  refine (oM ^ k).mul_right_inj.1 ?_
  rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul, _root_.mul_assoc, hs, mul_pow,
    Units.val_mul, _root_.mul_mul_mul_comm, H₁, H₂, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_map,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨y, rfl⟩ := E.surjective x
  have e₀ : E.symm.toEmbedding (E y) = y := E.symm_apply_apply y
  rw [e₀, _root_.mul_mul_mul_comm, ← hf, ← Units.val_mul, ← ht, ← ho y, Units.val_mul, Units.val_mul,
    _root_.mul_mul_mul_comm]


set_option maxHeartbeats 1600000 in
theorem expandsAt_boxProd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ A U hq wM wL e k hp₁ hp₂ hT hW σ σ₁ σ₂ f f₁ f₂ hσ hf
    hE₁ hE₂
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U₁ e k σ₁ f₁ hE₁
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U₂ e k σ₂ f₂ hE₂
  have hg₁ := thick_fstG I e (fst G₁ G₂)
  have hg₂ := thick_fstG I e (snd G₁ G₂)
  revert hp₁ hp₂ hT hW hg₁ hg₂
  generalize ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left = ρ₁
  generalize ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left = ρ₂
  intro hp₁ hp₂ hT hW hg₁ hg₂
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₁).left at ρ₁
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₂).left at ρ₂
  change pGl U e ≫ p₁.left = ρ₁ ≫ pGl U₁ e at hp₁
  change pGl U e ≫ p₂.left = ρ₂ ≫ pGl U₂ e at hp₂
  change fGl I (G₁ ⊗ G₂) e ≫ (fst G₁ G₂).left = ρ₁ ≫ fGl I G₁ e at hg₁
  change fGl I (G₁ ⊗ G₂) e ≫ (snd G₁ G₂).left = ρ₂ ≫ fGl I G₂ e at hg₂
  let E : D.toPre.X ≃ D₁.toPre.X × D₂.toPre.X := Equiv.ofBijective _ hq
  refine expandsAt_of_val U e k σ f ((S₁ ×ˢ S₂).map E.symm.toEmbedding) fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.toPre.P.isLB y
  have hF : ∀ α, (∏ a, om wM y J₁ J₂ J (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a).val *
      sval (f α) (pGl U e) y J =
      sval (f₁ (E α).1) (ρ₁ ≫ pGl U₁ e) y J₁ * sval (f₂ (E α).2) (ρ₂ ≫ pGl U₂ e) y J₂ := fun α => by
    rw [← hp₁, ← hp₂]
    exact hf α _ (pGl U e) y J₁ J₂ J hJ₁ hJ₂ hJ
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · refine (Units.mul_right_eq_zero _).1 ((hF α).trans ?_)
    by_cases h₁ : (E α).1 ∈ S₁
    · have h₂ : (E α).2 ∉ S₂ := fun h₂ =>
        hα (Finset.mem_map.2 ⟨E α, Finset.mem_product.2 ⟨h₁, h₂⟩, E.symm_apply_apply α⟩)
      rw [(hS₂ _ ρ₂ y J₂ hJ₂).1 _ h₂, mul_zero]
    · rw [(hS₁ _ ρ₁ y J₁ hJ₁).1 _ h₁, zero_mul]
  · obtain ⟨N, hN, eN⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit) (fun _ => fGl I (G₁ ⊗ G₂) e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : N (fGl I (G₁ ⊗ G₂) e) = jL := eN ⟨⟩
    obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at U₁.LG.isLB y
    obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at U₂.LG.isLB y
    have hT' : ∀ α, (∏ a, om wM y J₁ J₂ J (Oφl U e α a) ^ Oinvε a) * val (tG U e α) (𝟙 _) y J =
        val (tG U₁ e (E α).1) ρ₁ y J₁ * val (tG U₂ e (E α).2) ρ₂ y J₂ := fun α => by
      have := hT α _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
      simp only [Category.id_comp] at this
      exact this
    have hW' : om wM y J₁ J₂ J (pGl U e) * wv U e (𝟙 _) y (J (pGl U e)) (N (fGl I (G₁ ⊗ G₂) e)) =
        wv U₁ e ρ₁ y (J₁ (ρ₁ ≫ pGl U₁ e)) (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          wv U₂ e ρ₂ y (J₂ (ρ₂ ≫ pGl U₂ e)) (N₂ (ρ₂ ≫ fGl I G₂ e)) * om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) := by
      have := hW _ (𝟙 _) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at this
      rw [← hp₁, ← hp₂, ← hg₁, ← hg₂]
      exact this
    have hσ' : (om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) ^ k).val *
        sv U k σ (fGl I (G₁ ⊗ G₂) e) y (N (fGl I (G₁ ⊗ G₂) e)) =
        sv U₁ k σ₁ (ρ₁ ≫ fGl I G₁ e) y (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          sv U₂ k σ₂ (ρ₂ ≫ fGl I G₂ e) y (N₂ (ρ₂ ≫ fGl I G₂ e)) := by
      have := hσ _ (fGl I (G₁ ⊗ G₂) e) y N₁ N₂ N hN₁ hN₂ hN
      rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast] at this
      rw [← sval_eq_sv, ← sval_eq_sv, ← sval_eq_sv, ← hg₁, ← hg₂]
      exact this
    exact exp_alg k E S₁ S₂ hW' hσ' hF hT' (fun α => fam_mul_Oinv U e k (om wM y J₁ J₂ J) α)
      ((hS₁ _ ρ₁ y J₁ hJ₁).2 _ (hN₁ (ρ₁ ≫ fGl I G₁ e))) ((hS₂ _ ρ₂ y J₂ hJ₂).2 _ (hN₂ (ρ₂ ≫ fGl I G₂ e)))

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCardLeDegreeAmpleSemiPositive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hamp hsp J _ e x he hx hbox
  have hxb := (_root_.GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField k X p D hX).2 x hx
  have hmono := (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0)).1
  have hb : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ P.Bl 1 0 (Real.exp u) := fun c =>
    _root_.GlobalTheory.HSNef.bounded_norm k X p D hX P 1 0 _ (hbox c)
  choose u hu0 hu using hb
  have hall : ∀ c, boxFam e x c ∈ P.Bl 1 0 (Real.exp (∑ c, u c)) := fun c =>
    hmono _ _ (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c))) (hu c)
  apply _root_.GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep hAr hHS k X p D hX P 1 0 P.L (GlobalTheory.VolBr.Pair.rep_base k X p P).1 hamp hsp
    (Fintype.card J) (∑ c, u c)
  intro m hm
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
  · have h0 : Fintype.card J = 0 := Fintype.card_eq_zero
    haveI : IsEmpty (Fin (Fintype.card J * m ^ D)) := by rw [h0, zero_mul]; exact Fin.isEmpty'
    exact ⟨isEmptyElim, linearIndependent_empty_type, isEmptyElim⟩
  · haveI : CharZero X.functionField := charZero_of_inj_zero fun n hn => by
      have h := he.smul_left_injective j (a₁ := (n : ℤ)) (a₂ := 0) (by simp [hn])
      exact_mod_cast h
    obtain ⟨v, hv, hvs⟩ := _root_.GlobalTheory.many_independent_products_in_function_field X.functionField D x hxb J e he m hm
    refine ⟨v, hv, fun s => ?_⟩
    obtain ⟨w, n, hn, hvs'⟩ := hvs s
    rw [hvs']
    have h := _root_.GlobalTheory.HSNef.BoxProd.prod_mem_Bl k X p P D J e x 1 0 (Real.exp (∑ c, u c)) (Real.exp_pos _).le hall m w n hn
    rw [← Real.exp_nat_mul, mul_comm (m : ℝ)] at h
    exact h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamDimOfExpBij
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem famDim_of_expBij : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → U.ExpBij k → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g := by
  intro R _ _ I D A G _ _ U k hk hbij
  obtain ⟨b, hex, huniq⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin : ∀ (c : Fin (k ^ A.g) → FractionRing R) (s : U.SecK k),
      (∀ j, s.f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) →
      U.Expands k s (∑ i, c i • F i) := fun c s hs =>
    GlobalTheory.UnifPowAdm.expands_comb U k (s := b) hF (fun j => hs j)
  let φ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hφ : ∀ c, φ c = ∑ i, c i • F i := fun c => rfl
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 := hlin c s hs
    have h2 := hlin c' s' hs'
    rw [← hφ] at h1 h2
    rw [← h] at h2
    have e : s = s' := (hbij.2 (φ c)).unique h1 h2
    subst e
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreThetaConstantsAlgebraicOverCompleteAlgClose
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.FibreTheta

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport GlobalTheory.ValuesPullIso GlobalTheory.LabTrans

theorem isThetaPt_of_homMk {S X : Scheme.{0}} {P : PolAV S} {k : ℕ} {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) {I : Type}
    (x : I → (Over.mk h₁ ⟶ P.A)) {v : I → Γ(X, ⊤)}
    (H : IsThetaPt P k (fun i => (Over.homMk (x i).left ((Over.w (x i)).trans e) : Over.mk h₂ ⟶ P.A)) v) :
    IsThetaPt P k x v := by
  subst e
  exact H

theorem pow_homMk {S X : Scheme.{0}} {A : Over S} [GrpObj A] {h₁ h₂ : X ⟶ S} (e : h₁ = h₂) (x : Over.mk h₁ ⟶ A)
    {k : ℕ} (hx : x ^ k = 1) : (Over.homMk x.left ((Over.w x).trans e) : Over.mk h₂ ⟶ A) ^ k = 1 := by
  subst e
  exact hx

theorem theta_consts_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (n : ℕ), n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → ∀ (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → ∀ (B : PolAV (Sp (Kb W))) (b : B.A.left ⟶ A'.A.left), IsGrpPullback B.A A'.A (spMap (algebraMap (FractionRing W) (Kb W))) b → LBIso B.L (A'.L.pull b) → ∀ j : ℕ, 1 ≤ j → ∃ (C : Type) (_ : Field C) (jC : Kb W →+* C) (Ix : Type) (x : Ix → (baseOver (Sp (Kb W)) ⟶ B.A)) (v : Ix → Kb R), (∀ z : baseOver (Sp (Kb W)) ⟶ B.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ (∀ i, x i ^ ((n ^ j) ^ 2) = 1) ∧ IsThetaPt B (n ^ j) (fun i => (Over.homMk (spMap jC) (Category.comp_id _) : Over.mk (spMap jC) ⟶ baseOver (Sp (Kb W))) ≫ x i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (jC (e₀ (v i)))) := by
  intro R _ _ _ hR D n _ ho hnR W _ _ _ hW φ iφ lφ D' G' _ _ A' hD hG hU e₀ he₀ B b hb hLB j _
  obtain ⟨hD⟩ := hD
  obtain ⟨U'⟩ := hU
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  haveI := lφ
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have b₀ : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hm : Odd (n ^ j) := ho.pow
  have hmR : IsUnit (((n ^ j : ℕ)) : R) := by rw [Nat.cast_pow]; exact hnR.pow j
  have hk : 1 ≤ (n ^ j) ^ 2 := pow_pos hm.pos 2
  generalize n ^ j = m at *
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((gam.comp e₀).comp (algebraMap (FractionRing R) (Kb R))).toAlgebra
  let em : Kb R →ₐ[FractionRing R] C := { toRingHom := gam.comp e₀, commutes' := fun _ => rfl }
  have cC : Compat φ C := fun r => (congrArg gam (he₀ r)).trans (hgam _)
  have hCR : CExt R (maximalIdeal R) C :=
    ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
  obtain ⟨N, ν, -⟩ := ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
  obtain ⟨N', ν', -⟩ := ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even hB' C ⊤ fun _ => trivial
  obtain ⟨J, hJX, hJ⟩ := OneTraitTheta.exists_values_iso hL hD cC ν ν'
  obtain ⟨f, hf, -⟩ := GlobalTheory.TorsionIso.torsion_clause W _ b₀ D' A' G' hG U' C (m ^ 2) hk
  let f₀ := spMap (algebraMap (FractionRing W) (Kb W))
  let T : Over (Sp (Kb W)) := Over.mk (spMap gam)
  let ιC : T ⟶ baseOver (Sp (Kb W)) := Over.homMk (spMap gam) (Category.comp_id _)
  obtain ⟨e, he⟩ : ∃ e : (T ⟶ B.A) ≃* (Over.mk (T.hom ≫ f₀) ⟶ A'.A), ∀ y, (e y).left = y.left ≫ b :=
    LiePull.exists_pushEquiv hb T _ rfl
  have heq : spMap gam ≫ f₀ = jFK (R := W) C := by
    rw [← Geo.Tor.spMap_comp]
    exact congrArg spMap (RingHom.ext hgam)
  let Ix := {z : baseOver (Sp (Kb W)) ⟶ B.A // z ^ (m ^ 2) = 1}
  have tz : ∀ i : Ix, (ιC ≫ i.1) ^ (m ^ 2) = 1 := fun i => by rw [← MonObj.comp_pow, i.2, MonObj.comp_one]
  let x₀ : Ix → (Over.mk (T.hom ≫ f₀) ⟶ A'.A) := fun i => e (ιC ≫ i.1)
  have tx₀ : ∀ i, x₀ i ^ (m ^ 2) = 1 := fun i => by
    show e (ιC ≫ i.1) ^ (m ^ 2) = 1
    rw [← map_pow, tz, map_one]
  let x' : Ix → (TFK (R := W) C ⟶ A'.A) := fun i => Over.homMk (x₀ i).left ((Over.w (x₀ i)).trans heq)
  have hx' : ∀ i, x' i ^ (m ^ 2) = 1 := fun i => pow_homMk heq _ (tx₀ i)
  choose p' hp' using fun i => hf.2.1 (x' i) (hx' i)
  choose p₁ e₂ using fun i => qkPullExists hGF R W φ D.toPre D'.toPre hD C cC (m ^ 2) (p' i)
  have hQ := _root_.GlobalTheory.Mum.qkPt_algClosure_bijective R D.toPre C em (m ^ 2) hk
  choose p hp using fun i => (hQ.2 (p₁ i)).exists
  have hGt := _root_.GlobalTheory.Ex.GtValues.points_correspond
  choose q hq using fun i => (((hGt R D.toPre D.psi_even hB C N ν).2.2.2.2 _).1 (p₁ i)).exists
  choose q' hq' using fun i => (((hGt W D'.toPre D'.psi_even hB' C N' ν').2.2.2.2 _).1 (p' i)).exists
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.Mum.ThetaSer.theta_series_algebraic R hR D m hm hmR Ix p
  obtain ⟨s, hs⟩ := hv C hCR em N ν p₁ q hp hq
  have e₅ : ∀ i, QkToAkU U'.toUnifPre C (m ^ 2) (p' i) (x' i) := fun i => (hf.1 _ _).2 (hp' i).symm
  have Q := _root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV hGt (_root_.GlobalTheory.Ex.brFam hL hL₂) W _ hW rfl D' A' G' hG U' C hC N' ν' m hm _ p' q' x' e₅ hq'
  have hval : ∀ i, em (v i) = ((s * J.lam : Cˣ) : C) * N'.tx m (q' i) := fun i => by
    have e := (RelabelCoords.series_iso J hm (p := q' i) (p' := q i) (ν.eX.injective (by
      rw [hJX, (hq i).1, (hq' i).1, (e₂ i).1, AddEquiv.apply_symm_apply])) (hJ _ _ _ _ (hq i).2 (hq' i).2 (e₂ i).2)).1
    rw [e, Units.val_mul, _root_.mul_assoc, Units.mul_inv_cancel_left]
    exact hs i
  have Q₁ : IsThetaPt A' m x' (fun i => fnOf (em (v i))) :=
    GenericObject.isThetaPt_unit_mul A' m x' _ _ (fnOf ((s * J.lam : Cˣ) : C))
      ((Units.isUnit (s * J.lam)).map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (fun i => by rw [hval i]; exact map_mul _ _ _) Q
  have Q₂ : IsThetaPt A' m x₀ (fun i => fnOf (em (v i))) := isThetaPt_of_homMk heq x₀ Q₁
  have Q₃ := (ThetaPtUp.isThetaPt_iff hb hLB (x := fun i : Ix => ιC ≫ i.1) (x₀ := x₀) (fun i => he _) tz _).2 Q₂
  exact ⟨C, inferInstance, gam, Ix, Subtype.val, v, fun z hz => ⟨⟨z, hz⟩, rfl⟩, fun i => i.2, Q₃⟩

end GlobalTheory.Mum.FibreTheta
end
end

