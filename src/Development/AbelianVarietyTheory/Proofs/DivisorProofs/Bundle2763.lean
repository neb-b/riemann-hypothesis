module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2741
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2638
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSelfZeroAbelianH1
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pO1_comp {R : Type} [CommRing R] {Z Y A : Over (Sp R)} (i : Z ⟶ Y) (f : Y ⟶ A) (x : HO1 A.hom) :
    pO1 i (pO1 f x) = pO1 (i ≫ f) x :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).1 _ _ _ _ _ _ _ _ (ovw f) _ _ _ _ _ (ovw i) _ _ (ovw (i ≫ f)) (Over.comp_left _ _ _ _ _)
    (fun _ ↦ rfl)).1 x

theorem pO1_id {R : Type} [CommRing R] {A : Over (Sp R)} (x : HO1 A.hom) : pO1 (𝟙 A) x = x :=
  ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).2.2 R A).1 x

theorem pO1_unit_eq_zero {R : Type} [CommRing R] (x : HO1 (𝟙_ (Over (Sp R))).hom) : x = 0 := by
  have : IsAffine (𝟙_ (Over (Sp R))).left := by
    change IsAffine (Sp R); infer_instance
  exact (GlobalTheory.Obs.sq_abelian_and_affine_H1 R).2 _ _ x

theorem pO1_toUnit_comp {R : Type} [CommRing R] {Y A : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (x : HO1 A.hom) :
    pO1 (toUnit Y ≫ f) x = 0 := by
  rw [← pO1_comp, pO1_unit_eq_zero (pO1 f x), map_zero]

theorem primO1_of_axesO1 {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : AxesVanishingStructureSheafDegOne A) : StructureSheafH1Primitive A := by
  intro x
  rw [← sub_eq_zero, sub_add_eq_sub_sub]
  apply h
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_right, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp
  · rw [map_sub, map_sub, pO1_comp, pO1_comp, pO1_comp, lift_comp_one_left, lift_fst, lift_snd,
      pO1_toUnit_comp, pO1_id]
    simp

theorem cup_add_cup_swap {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : CatCoh.H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [GlobalTheory.CatCoh.cup_mk, GlobalTheory.CatCoh.cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [GlobalTheory.CatCoh.d1_apply, Submodule.coe_add, Pi.add_apply, GlobalTheory.CatCoh.cupZ_apply, GlobalTheory.CatCoh.Z1.comp a,
    GlobalTheory.CatCoh.Z1.comp b, map_mul, map_neg]
  ring

theorem cup_self_eq_zero_of_prim {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hP : StructureSheafH1Primitive A)
    (hN : NoPrimitiveStructureSheafH2 A) (x : HO1 A.hom) : cup _ x x = 0 := by
  have key : ∀ f : A ⊗ A ⟶ A, structureSheafH2Pullback f (cup _ x x) = cup _ (pO1 f x) (pO1 f x) := fun f ↦
    ((_root_.GlobalTheory.AbCoh.pull_comp_cup_id).2.1 _ _ _ _ _ _ _ _ (ovw f)).1 x x
  apply hN
  rw [key, key, key, hP x]
  simp only [map_add (f := _), LinearMap.add_apply]
  have := cup_add_cup_swap (OAff (A ⊗ A).hom) (pO1 (fst A A) x) (pO1 (snd A A) x)
  linear_combination (norm := module) this

theorem cup_self_eq_zero_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R))
    [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ x : HO1 A.hom, cup _ x x = 0 := by
  intro R _ _ A _ g hA hg x
  exact cup_self_eq_zero_of_prim A (primO1_of_axesO1 A (_root_.GlobalTheory.AbCoh.AxesSq.axesO1_of_isAbelianScheme R A g hA hg)) (_root_.GlobalTheory.AbCoh.NoPrimNoeth.noPrimO2_of_isNoetherianRing R A g hA hg) x

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenominatorFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop

namespace GlobalTheory.BigTop.Fun

theorem halfRank_eq_sqRank_div (D : D7) (ij : Sq D) :
    GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 = sqRank D ij / 2 := by
  unfold GlobalTheory.FunObj.SqNum.halfRank sqRank
  congr 1
  simp only [GlobalTheory.ChiGrid.rankV]
  ring

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledPrimeToP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.KerPowDescent

theorem pow_eq_one_of_lift {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S} [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A')
    [IsMonHom ψ] (m : ℕ) {P' : LB (G2 A').left} (hP' : P'.IsLB)
    (hiso : LBIso (Hecke.lbPow o.P m) (P'.pull (sq2 ψ))) {e₀ : ℕ}
    (hker : ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e₀ = 1)
    {T T' : Over S} (π' : T' ⟶ T) (y : T' ⟶ o.A) (x : T ⟶ A') (hy : y ≫ ψ = π' ≫ x)
    (h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0) : y ^ (m * e₀) = 1 := by
  have hP := o.isLB
  have hPm : (Hecke.lbPow o.P m).IsLB := LB.isLB_linComb hP _ _
  have hc : GlobalTheory.CechPic.cls _ hPm = m • GlobalTheory.CechPic.cls o.P hP := by
    refine (GlobalTheory.CechPic.cls_linComb hP (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1) hPm).trans ?_
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hc' : GlobalTheory.CechPic.cls _ hPm = GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP') :=
    (GlobalTheory.CechPic.cls_eq_iff hPm (pull_isLB hP' _)).2 hiso
  have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst o.A T' ≫ ψ) (snd o.A T' ≫ π')).left) h0
  rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst, Category.assoc, ← hy] at h1
  have e2 : GlobalTheory.AbDual.evc hP' (snd o.A T' ≫ y ≫ ψ) (fst o.A T' ≫ ψ) =
      GlobalTheory.CechPic.pull (lift (snd o.A T' ≫ y) (fst o.A T')).left
        (GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls P' hP')) := by
    rw [← GlobalTheory.CechPic.pull_comp, GlobalTheory.AbDual.evc, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc,
      Category.assoc]
  rw [e2, ← hc', hc, map_nsmul] at h1
  have h3 : GlobalTheory.AbDual.evc hP (snd o.A T' ≫ y ^ m) (fst o.A T') = 0 := by
    rw [comp_pow, Hecke.evc_pow_left o.ab hP o.rig₁ o.rig₂]
    exact h1
  have h4 := hker T' (y ^ m) ((GlobalTheory.AbDual.triv_ev_iff hP _ _).2 h3)
  rwa [← pow_mul] at h4

theorem kernel_primePower_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (c : ℕ), (∃ e : ℕ, c = p ^ e) → IsUnit ((p : ℕ) : R) → ∀ (H : Subgroup (𝟙_ (Over S) ⟶ o.A)) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover H (fun h => (transl h.1).left) ψ.left → (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (g : Over.mk x ⟶ o.A), g ^ c = 1 → (∀ h ∈ H, Out.WeilIs (G2 o.A) (Hecke.lbPow o.P c) 1 (lift g 1 : Over.mk x ⟶ G2 o.A) (lift 1 (toUnit (Over.mk x) ≫ h)) 1) → ∃ h ∈ H, g = toUnit (Over.mk x) ≫ h) → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (Hecke.lbPow o.P c) (P'.pull (sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N S s o c hc hpu H A' _ _ ψ hA' hψ hG hH P' hP' r₁ r₂ hiso
  haveI := hψ
  obtain ⟨e₀, he₀, hker⟩ := o.kerP
  obtain ⟨e, rfl⟩ := hc
  refine ⟨e₀, he₀, ?_⟩
  intro T x hx
  have h0 : GlobalTheory.AbDual.evc hP' (snd A' T ≫ x) (fst A' T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).1 hx
  have := hG.etale
  have := hG.fin
  have := hG.onto

  have hxc : x ^ (p ^ e * e₀) = 1 := by
    let T' : Over S := Over.mk (pullback.fst x.left ψ.left ≫ T.hom)
    let π' : T' ⟶ T := Over.homMk (pullback.fst x.left ψ.left) rfl
    let y : T' ⟶ o.A := Over.homMk (pullback.snd x.left ψ.left) (by
      show pullback.snd x.left ψ.left ≫ o.A.hom = pullback.fst x.left ψ.left ≫ T.hom
      rw [← Over.w ψ, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w x])
    have hy : y ≫ ψ = π' ≫ x := Over.OverMorphism.ext (by
      show pullback.snd x.left ψ.left ≫ ψ.left = pullback.fst x.left ψ.left ≫ x.left
      exact pullback.condition.symm)
    have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker π' y x hy h0
    have h5 : π' ≫ x ^ (p ^ e * e₀) = π' ≫ 1 := by
      rw [comp_pow, ← hy, ← GlobalTheory.SS.FrobTorsion.pow_comp' ψ y, h4, MonObj.one_comp, MonObj.comp_one]
    apply Over.OverMorphism.ext
    have h6 := congrArg (fun f => f.left) h5
    simp only [Over.comp_left] at h6
    exact (cancel_epi (pullback.fst x.left ψ.left)).1 h6
  have hu : IsUnit (((p ^ e : ℕ) : Γ(S, ⊤))) := by
    have := (hpu.pow e).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    simpa using this
  refine GlobalTheory.TorsionRigid.eq_one_of_pow_eq_one_of_geometric S A' hA' (p ^ e)
    (pow_pos (Fact.out : p.Prime).pos e) hu T (x ^ e₀) (by rw [← pow_mul, mul_comm]; exact hxc) ?_
  intro κ _ _ q
  let Tq : Over S := Over.mk (q ≫ T.hom)
  let πq : Tq ⟶ T := Over.homMk q rfl
  obtain ⟨pt, hpt⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left (q ≫ x.left)
  let y : Tq ⟶ o.A := Over.homMk pt (by
    show pt ≫ o.A.hom = q ≫ T.hom
    rw [← Over.w ψ, ← Category.assoc, ← hpt, Category.assoc, Over.w x])
  have hy : y ≫ ψ = πq ≫ x := Over.OverMorphism.ext (by
    show pt ≫ ψ.left = q ≫ x.left
    exact hpt.symm)
  have h4 := pow_eq_one_of_lift o ψ (p ^ e) hP' hiso hker πq y x hy h0
  have hg : (y ^ e₀) ^ (p ^ e) = 1 := by rw [← pow_mul, mul_comm]; exact h4
  have hgψ : (y ^ e₀) ≫ ψ = (πq ≫ x) ^ e₀ := by rw [GlobalTheory.SS.FrobTorsion.pow_comp', hy]

  have hz : GlobalTheory.AbDual.evc hP' (snd A' Tq ≫ (y ^ e₀) ≫ ψ) (fst A' Tq) = 0 := by
    have h1 := congrArg (GlobalTheory.CechPic.pull (lift (fst A' Tq) (snd A' Tq ≫ πq)).left) h0
    rw [GlobalTheory.AbDual.pull_evc, map_zero, lift_snd_assoc, lift_fst] at h1
    simp only [Category.assoc] at h1
    rw [hgψ, comp_pow, Hecke.evc_pow_left hA' hP' r₁ r₂, h1, smul_zero]
  have hG0 := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 A') := AbelianSchemeGerms.isAbelianScheme_tensor A' A' hA' hA'
  have hAo2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have s₁ : GlobalTheory.CechPic.pull (lift (1 : A' ⟶ A') (𝟙 A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₁
  have s₂ : GlobalTheory.CechPic.pull (lift (𝟙 A') (1 : A' ⟶ A')).left (GlobalTheory.CechPic.cls P' hP') = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP' _)).2 r₂
  have hK : GlobalTheory.MemKL (G2 A') P' (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') :=
    GlobalTheory.DualCon.TwistDescent.memKL_of_lam_eq_zero hP' _
      (GlobalTheory.KernelPointPairing.lam_eq_zero hP' hA' s₁ s₂ ((y ^ e₀) ≫ ψ) hz)
  have w₀ : Out.WeilIs (G2 A') P' 1 (lift ((y ^ e₀) ≫ ψ) 1 : Tq ⟶ G2 A') 1 1 :=
    GlobalTheory.DescendedPrincipal.weilIs_one_right hG0 hA2 hP' fun pp => by
      obtain ⟨V, hV, c, hc⟩ := hK pp
      exact ⟨V, hV, GlobalTheory.DescendedPrincipal.exists_theta_of_translDiff hP' _ V c hc⟩
  have hPc : (Hecke.lbPow o.P (p ^ e)).IsLB := LB.isLB_linComb o.isLB _ _
  let ψ2 : G2 o.A ⟶ G2 A' := lift (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
  haveI : IsMonHom ψ2 := inferInstance
  have hw : LBIso (Geo.Tor.lbPow (Hecke.lbPow o.P (p ^ e)) 1) (P'.pull ψ2.left) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hPc 1) hPc (pull_isLB hP' _) (GlobalTheory.lbIso_lbPow_one hPc) hiso
  have hHψ : ∀ h ∈ H, h ≫ ψ = 1 := fun h hh => comp_eq_one_of_transl ψ h (hG.inv ⟨h, hh⟩)
  obtain ⟨h, hh, hgh⟩ := hH κ (q ≫ T.hom) (y ^ e₀) hg fun h hh => by
    have e1 : (lift (y ^ e₀) 1 : Tq ⟶ G2 o.A) ≫ ψ2 = lift ((y ^ e₀) ≫ ψ) 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    have e2 : (lift 1 (toUnit Tq ≫ h) : Tq ⟶ G2 o.A) ≫ ψ2 = 1 := by
      rw [comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp, Category.assoc, hHψ h hh, MonObj.comp_one]
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG0 hAo2 hPc hP' ψ2 hw (n := 1) (x := lift (y ^ e₀) 1)
      (y := lift 1 (toUnit Tq ≫ h)) (c := 1) (by rw [e1, e2]; exact w₀)
    simpa using this
  show πq ≫ x ^ e₀ = 1
  rw [comp_pow, ← hgψ, hgh, Category.assoc, hHψ h hh, MonObj.comp_one]

end GlobalTheory.UPel.HT.ES.KerPowDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFrobeniusTwistBijectiveRelFrobenius
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

theorem wittMap_frobRing_bijective (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] : Function.Bijective (WittVector.map (p := p) (frobRing (p_eq_zero p k))) := by
  have hb : Function.Bijective (frobRing (p_eq_zero p k)) := by
    have e : ⇑(frobRing (p_eq_zero p k)) = ⇑(frobenius k p) :=
      funext fun r => by rw [frobRing_apply, frobenius_def]
    rw [e]
    exact bijective_frobenius k p
  exact ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩

theorem bijective_of_basis {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Bijective σ) (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = σ a • f m) {ι : Type} [Fintype ι] (b : Module.Basis ι R M)
    (b' : Module.Basis ι R' M') (hb : ∀ i, b' i = f (b i)) : Function.Bijective f := by
  have key : ∀ c : ι → R, f (∑ i, c i • b i) = ∑ i, σ (c i) • b' i := fun c => by
    rw [map_sum f]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hb]
  refine ⟨(injective_iff_map_eq_zero f).2 fun m hm => ?_, fun x => ?_⟩
  · rw [← b.sum_repr m, key] at hm
    have : ∀ i, b.repr m i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.1 b'.linearIndependent _ hm i
      exact hσ.1 (this.trans (map_zero σ).symm)
    rw [← b.sum_repr m]
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : ι → R, ∀ i, σ (c i) = b'.repr x i :=
      ⟨fun i => Function.surjInv hσ.2 (b'.repr x i), fun i => Function.surjInv_eq hσ.2 _⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [key]
    simp only [hc]
    exact b'.sum_repr x

theorem frobTwist_module (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True)
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) :
    Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧
    (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧
    ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n =
      B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  have h2 : ∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m := fun m =>
    (B.smap_comp trivial trivial trivial (frobProj (p_eq_zero p k) G)
      (SemiHom.ofHom (relFrob (p_eq_zero p k) G)) (absFrob (p_eq_zero p k) G)
      (fun n a => by rw [SemiHom.ofHom_app, relFrob_app_frobProj, absFrob_app]) m).symm
  refine ⟨?_, h2, fun m n e => ?_⟩
  · haveI := B.free G trivial
    haveI := B.finite G trivial
    letI := (frobRing (p_eq_zero p k)).toAlgebra
    obtain ⟨b', hb'⟩ := _root_.GlobalTheory.Dieu.Base.smap_toBase_basis p (fun _ _ _ => True) B k k G trivial trivial _
      (Module.Free.chooseBasis (WittVector p k) (B.M G trivial))
    exact bijective_of_basis _ (wittMap_frobRing_bijective p k) _
      (fun a m => B.smap_smul trivial trivial _ a m) _ b' hb'
  · obtain ⟨-, hc, -⟩ := _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) B k G
      (frobTwist (p_eq_zero p k) G) G trivial trivial trivial
    obtain ⟨hid, -, -, -, hp, -⟩ := _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) B k G G G trivial trivial trivial
    rw [← h2, e, ← LinearMap.comp_apply, ← hc, relFrob_comp_verschiebung, ← pow_one (p : ℤ_[p]), hp,
      pow_one, hid, LinearMap.id_apply]

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.EighthTorsion
open MonObj

def postcomp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f] :
    (T ⟶ G) →* (T ⟶ H) where
  toFun g := g ≫ f
  map_one' := by simp
  map_mul' a b := by simp [MonObj.mul_comp]

theorem prod_comp {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (l : List (T ⟶ G)) : l.prod ≫ f = (l.map (· ≫ f)).prod :=
  (map_list_prod (postcomp (T := T) f) l)

theorem zpow_comp' {S : Scheme.{0}} {T G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
    (g : T ⟶ G) (n : ℤ) : (g ^ n) ≫ f = (g ≫ f) ^ n :=
  map_zpow (postcomp (T := T) f) g n

theorem ident_pow {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε)
    (A8 : PolAV (Sp (FractionRing T.V))) (pA : IsPowPolAV A8 T.A 8) :
    ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ φ.hom ≫ pA.pr a = ((List.finRange 8).map fun b => (φ.hom ≫ pA.pr b) ^ E a b).prod := by
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL, hε⟩ := hD
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  have hφp' : ∀ a, φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp
  refine ⟨φ, hφ, ?_, ?_⟩
  · have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
      rw [hφp' a, Over.comp_left, Category.assoc, hee]
    have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
    obtain ⟨w', hw'⟩ := T.lb
    have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
      (fun ab => W ab.1 ab.2)
    have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
      (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
    have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
        fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
      funext fun ab => GlobalTheory.Poinc.SharpIdent.lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
    rw [hm] at i₁
    exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
      (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)
  · intro E a
    haveI := he
    rw [hφp' a, ← Category.assoc, hε E a, prod_comp, List.map_map]
    congr 1
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, hφp' b]
    exact zpow_comp' e.hom (pr b) (E a b)

theorem exists_proj {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (hD : IsDiagEnd F W P T.y ε) :
    ∃ pr : Fin 8 → (P.A ⟶ T.A.A), (∀ a, IsMonHom (pr a)) ∧
      (∀ (T' : Over (Sp (FractionRing T.V))) (y : Fin 8 → (T' ⟶ T.A.A)), ∃! z : T' ⟶ P.A, ∀ a, z ≫ pr a = y a) ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) ∧
      ∀ E a, ε E ≫ pr a = (List.ofFn fun b => pr b ^ E a b).prod := by
  obtain ⟨A8, pA, -⟩ := GlobalTheory.exists_powPolAV _ T.A 8
  obtain ⟨φ, hφ, hL, hε⟩ := ident_pow F W T P ε hD A8 pA
  refine ⟨fun a => φ.hom ≫ pA.pr a, fun a => by have := pA.hom a; infer_instance, fun T' y => ?_, hL,
    fun E a => by rw [List.ofFn_eq_map]; exact hε E a⟩
  refine ⟨pA.lim.lift (Fan.mk T' y) ≫ φ.inv, fun a => ?_, fun z hz => ?_⟩
  · rw [Category.assoc, φ.inv_hom_id_assoc]
    exact pA.lim.fac (Fan.mk T' y) ⟨a⟩
  · rw [Iso.eq_comp_inv]
    exact pA.lim.uniq (Fan.mk T' y) _ fun a => (Category.assoc _ _ _).trans (hz a.as)

theorem tau_coord {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (a b' : T.D.toPre.X)
    (x : (FractionRing T.V)ˣ) (hx : GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord T.D.toPre a b' x) :
    ∃ u : T.Vˣ, (x : FractionRing T.V) =
      algebraMap T.V (FractionRing T.V) (u : T.V) * algebraMap T.V (FractionRing T.V) T.ϖ ^ (T.β a b') := by
  obtain ⟨x₁, h₁⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre (a + b')
  obtain ⟨x₂, h₂⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre a
  obtain ⟨x₃, h₃⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.exists_isPsiCoord T.D.toPre b'
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.TauCoordQuot.main T.V T.D.toPre a b' x x₁ x₂ x₃ hx h₁ h₂ h₃
  obtain ⟨r₁, c₁, e₁⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₁
  obtain ⟨r₂, c₂, e₂⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₂
  obtain ⟨r₃, c₃, e₃⟩ :=
    GlobalTheory.PeriodFormCompare.exists_psiCoord_of_isPsiCoord (GlobalTheory.PeriodFormCompare.psiIn_top T.D _) h₃
  obtain ⟨u, hu⟩ := T.mono.tau (fun i y z => by fin_cases i; exact T.symm y z)
    (Fin.forall_fin_one.2 T.irr.ne_zero) c₂ c₃ c₁
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hu
  refine ⟨u₀ * u, ?_⟩
  have key : algebraMap T.V (FractionRing T.V) (u₀ : T.V) * algebraMap T.V (FractionRing T.V) r₁ *
      (algebraMap T.V (FractionRing T.V) r₂)⁻¹ * (algebraMap T.V (FractionRing T.V) r₃)⁻¹ =
      algebraMap T.V (FractionRing T.V) (u₀ : T.V) * (algebraMap T.V (FractionRing T.V) r₁ /
        (algebraMap T.V (FractionRing T.V) r₂ * algebraMap T.V (FractionRing T.V) r₃)) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [hu₀, e₁, e₂, e₃, key, hu]
  simp only [Units.val_mul, map_mul]
  ring

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW T P ε hD
  have hCN : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩
  have hB : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, T.char⟩
  have hS : SharpOver F W P T.y := by
    obtain ⟨c, hc, pr, h₁, h₂, h₃, -⟩ := hD
    exact ⟨c, hc, pr, h₁, h₂, h₃⟩
  haveI : IsCommMonObj (powObj T.G 8) := GlobalTheory.PowerExamples.comm_of_pow (powIsPowGrp T.G 8)
  have hG' : IsSemiAbelian (powObj T.G 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ T.G 8 (powIsPowGrp T.G 8) T.semi
  obtain ⟨D', ⟨U'⟩⟩ := GlobalTheory.PowE8.exists_unif_pow8 g n _ _ F W hW T.V hCN T.D T.G T.A T.U T.y T.α T.α₂ T.semi T.cart
    T.sq T.lb P hS
  obtain ⟨pr, hpr, huniv, hL, hε⟩ := exists_proj F W T P ε hD
  obtain ⟨pG, c, e, hpG, hgen, hc, he⟩ := GlobalTheory.T.eighthPower_projections_extend_uniformisedGroups T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr
    huniv hL
  have hnn : ∀ a, 0 ≤ T.β a a := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (GlobalTheory.Poinc.Trait.beta_pos g n _ _ F T a ha).le
  refine ⟨powObj T.G 8, inferInstance, inferInstance, hG', D', U', e, fun y => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff _ y).2 (GlobalTheory.PeriodFormCompare.psiIn_top D' y)
    obtain ⟨-, h⟩ := GlobalTheory.T.eighthPower_psiOrders_projectionLatticeCoordinates T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc
      e he T.ϖ T.β T.symm hnn (tau_coord T) y r hr
    obtain ⟨v, hv⟩ := h.symm
    exact ⟨v, by rw [mul_comm, hv]; exact hr⟩
  · rintro K _ _ _ m pk pk' x x' E hm h h' rfl
    exact GlobalTheory.T.matrix_acts_on_torsion_labels_alt T.V hB T.dvr T.G T.semi T.D T.A T.U _ hG' D' P U' W hW pr hpr huniv hL pG hpG hgen c hc e he E (ε E)
      (hε E) K m pk pk' x hm h h'

end GlobalTheory.EighthTorsion
end
end

