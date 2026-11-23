module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PreboxExpansionWeight
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BoxExpPre

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pG : IsPowGrp G' G j}
  {U' : UnifPre I D' A' G'} {U : UnifPre I D A G} {wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)}


variable (pD pG U' U) in
def TPr : Prop := (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i)))))


variable (pD pG U' U wL) in
def WPr : Prop := (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL'))))

theorem prebox_q (PT : TPr pD pG U' U) (e : ℕ) (i : Fin j) :
    pGl U' e ≫ (pD.pw.pr i).left = rhoE I pG e i ≫ pGl U e := (PT e 0).choose i 2

set_option maxHeartbeats 800000 in
theorem prebox_F (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {k : ℕ} {f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α}
    {f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'} (hf' : IsBoxFamB pD k f' f) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e) y J' =
      ∏ i, sval (f i (pD.xe α' i)) (rhoE I pG e i ≫ (pGl U e)) y J := by
  obtain ⟨hφ, H⟩ := hf' α'
  have := box_sec_val pD.w hφ (f' α') (fun i => f i (pD.xe α' i)) _ H (pGl U' e) y hJ hJ'
  simp only [prebox_q PT] at this
  exact this

set_option maxHeartbeats 800000 in
theorem prebox_expansion_torus (PT : TPr pD pG U' U) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a) * val (tG U' e α') (𝟙 _) y J' =
      ∏ i, val (tG U e (pD.xe α' i)) (rhoE I pG e i) y J := by
  obtain ⟨hψ, H⟩ := PT e α'
  exact box_gen_val pD.w hψ _ (fun i => tG U e (pD.xe α' i)) H y hJ hJ'

theorem prebox_om {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι} (k : ℕ) (α' : D'.toPre.X) :
    (∏ a, omB pD y J J' ((pGl U' e) ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a) * ∏ a, omB pD y J J' (Oφl U' e α' a) ^ Oinvε a =
      omB pD y J J' (pGl U' e) ^ k := by
  have a₀ : (pGl U' e) ≫ D'.toPre.famφB α' 0 = (pGl U' e) := Category.comp_id _
  have a₁ : (pGl U' e) ≫ D'.toPre.famφB α' 1 = Oφl U' e α' 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U'.gt e).pG (𝟙 _) (cP D'.toPre _ α')).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D'.toPre _ α')))
  have a₂ : (pGl U' e) ≫ D'.toPre.famφB α' 2 = Oφl U' e α' 1 :=
    congrArg (fun z => z.left) (comp_cP D'.toPre (U'.gt e).pG α')
  have a₃ : (pGl U' e) ≫ D'.toPre.famφB α' 3 = Oφl U' e α' 3 :=
    congrArg (fun z : _ ⟶ D'.toPre.P.A => z.left) (MonObj.comp_one (M := D'.toPre.P.A) (U'.gt e).pG)
  have a₄ : Oφl U' e α' 2 = (pGl U' e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

set_option maxHeartbeats 800000 in
theorem prebox_expansion_weight (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) {e : ℕ} {y : (thickObj R I e G').left} {J : ((thickObj R I e G').left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : ((thickObj R I e G').left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L y J) (hJ' : Good D'.toPre.P.L y J') {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    omB pD y J J' (pGl U' e) * wv U' e (𝟙 _) y (J' (pGl U' e)) jL' =
        (∏ i, wv U e (rhoE I pG e i) y (J ((pGl U' e) ≫ (pD.pw.pr i).left)) (jL i)) *
          gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have hq := prebox_q PT e
  have mM : (pGl U' e) y ∈ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) :=
    ⟨Set.mem_iInter.2 fun i => hJ ((pGl U' e) ≫ (pD.pw.pr i).left), hJ' (pGl U' e)⟩
  have mW : ∀ i, rhoE I pG e i y ∈ (D.toPre.P.L.pull (pGl U e)).U (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left)) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL i) := fun i =>
    ⟨mem_pull.2 ((congrArg (fun g => g y ∈ D.toPre.P.L.U (J ((pGl U' e) ≫ (pD.pw.pr i).left))) (hq i)).mp (hJ _)),
      mem_pull.2 (hL₁ i)⟩
  have hm : (𝟙 _ : (thickObj R I e G').left ⟶ _) y ∈ (pGl U' e) ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U
      (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left), J' (pGl U' e)) ⊓
      (LB.div (D'.toPre.P.L.pull (pGl U' e)) (U'.LG.L.pull (fGl I G' e))).U (fun _ => J' (pGl U' e), fun _ => jL') ⊓
      (⨅ i, rhoE I pG e i ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (pGl U e)) (U.LG.L.pull (fGl I G e))).U
        (fun _ => J ((pGl U' e) ≫ (pD.pw.pr i).left), fun _ => jL i)) ⊓
      (fGl I G' e) ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') :=
    ⟨⟨⟨mM, mem_pull.2 (hJ' (pGl U' e)), mem_pull.2 hL'⟩, by
      rw [← Finset.inf_univ_eq_iInf]; exact mem_finf _ _ _ fun i _ => mW i⟩, mL⟩
  have W := congrArg (gm (𝟙 _) y _) (PW e (fun i => J ((pGl U' e) ≫ (pD.pw.pr i).left)) (J' (pGl U' e)) jL' jL)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ (pGl U' e) y _ _ _ hm _) (gm_res (𝟙 _) y _ hm _))).symm.trans (W.trans
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ =>
          gm_rp₁ (rhoE I pG e i) y _ _ _ hm _)) (gm_rp₁ (fGl I G' e) y _ _ _ hm _))))

set_option maxHeartbeats 800000 in
theorem prebox_S {e k : ℕ} {y : (thickObj R I e G').left} {σ : Fin j → H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    (hσ' : IsBoxSecG pG wL k σ' σ) {jL : Fin j → U.LG.L.ι} {jL' : U'.LG.L.ι}
    (hL : ∀ i, (pG.pr i).left (fGl I G' e y) ∈ U.LG.L.U (jL i)) (hL' : fGl I G' e y ∈ U'.LG.L.U jL') :
    (gm (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL')) (wL.s (jL, jL')) ^ k).val *
        sv U' k σ' (fGl I G' e) y jL' = ∏ i, sv U k (σ i) (rhoE I pG e i ≫ fGl I G e) y (jL i) := by
  have hρ : ∀ i, rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left := fun i => pullback.lift_fst _ _ _
  have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
    (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (hρ i)).mpr (hL i)
  have mL : fGl I G' e y ∈ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL') := ⟨Set.mem_iInter.2 hL, hL'⟩
  have Sg := congrArg (gs (fGl I G' e) y ((LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jL, jL'))) (hσ' jL jL')
  rw [gs_mul _ y _ mL, gs_unit _ y _ mL, map_pow] at Sg
  refine (congrArg₂ (· * ·) rfl (gs_res (fGl I G' e) y (boxG_le_b pG jL jL') mL _).symm).trans
    (Sg.trans ((gs_prod _ y _ mL _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]
  exact (gs_res (fGl I G' e) y (boxG_le_c pG jL jL' i) mL _).trans
    (gs_pull (fGl I G' e) (pG.pr i).left y _ (boxG_le_c pG jL jL' i mL) _)

theorem expandsAt_prebox (PT : TPr pD pG U' U) (PW : WPr pD pG U' U wL) (k e : ℕ) (σ : Fin j → H0 U.LG.L k)
    (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ i, U.ExpandsAt e k (σ i) (f i))
    (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α')
    (hσ' : IsBoxSecG pG wL k σ' σ) (hf' : IsBoxFamB pD k f' f) :
    U'.ExpandsAt e k σ' f' := by
  classical
  choose S hS using fun i => expandsAt_val U e k (σ i) (f i) (hE i)
  refine expandsAt_of_val U' e k σ' f' ((Fintype.piFinset S).map pD.xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R I e G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hF := prebox_F PT hJ hJ' hf'
  have hT := prebox_expansion_torus PT hJ hJ'
  have hω := prebox_om (pD := pD) (U' := U') (y := y) (J := J) (J' := J') k
  have hq := prebox_q PT e
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, pD.xe α' i ∉ S i := by
      by_contra hc
      exact hα (Finset.mem_map.2 ⟨pD.xe α', Fintype.mem_piFinset.2 fun i => by_contra fun h => hc ⟨i, h⟩,
        pD.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').trans (Finset.prod_eq_zero (Finset.mem_univ i)
      ((hS i _ (rhoE I pG e i) y J hJ).1 _ hi)))
  · choose jL hL using fun i => exists_chart U.LG.isLB ((pG.pr i).left ((fGl I G' e) y))
    have hL₁ : ∀ i, fGl I G e (rhoE I pG e i y) ∈ U.LG.L.U (jL i) := fun i =>
      (congrArg (fun g => g y ∈ U.LG.L.U (jL i)) (pullback.lift_fst _ _ _ :
        rhoE I pG e i ≫ fGl I G e = fGl I G' e ≫ (pG.pr i).left)).mpr (hL i)
    have W' := prebox_expansion_weight PT PW hJ hJ' hL hL'
    have Sg' := prebox_S hσ' hL hL'
    refine (omB pD y J J' (pGl U' e) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, Sg', ← Finset.prod_pow,
      Units.coe_prod, ← Finset.prod_mul_distrib, Finset.sum_map, Finset.mul_sum]
    refine (Finset.prod_congr rfl fun i _ => ?_).trans ((Finset.prod_univ_sum S fun i α =>
      sval (f i α) (rhoE I pG e i ≫ (pGl U e)) y J * (val (tG U e α) (rhoE I pG e i) y J).val).trans
      (Finset.sum_congr rfl fun x _ => ?_))
    · rw [hq]; exact (hS i _ (rhoE I pG e i) y J hJ).2 (jL i) (hL₁ i)
    · obtain ⟨α', rfl⟩ := pD.xe.surjective x
      have e₀ : pD.xe.symm.toEquiv.toEmbedding (pD.xe α') = α' := pD.xe.symm_apply_apply α'
      rw [e₀, Finset.prod_mul_distrib, ← hF α', ← Units.coe_prod, ← hT α', ← hω α', Units.val_mul, Units.val_mul,
        _root_.mul_mul_mul_comm]

theorem expandsAt_box_unifPre : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : UnifPre I D' A' G') (U : UnifPre I D A G) (wL : LB.Iso U'.LG.L (boxLB U.LG.L pG.pr)), (∀ i, U'.gen.hom ≫ pA.pr i = (Over.pullback (jK R)).map (pG.pr i) ≫ U.gen.hom) ∧ wL.IsGen ∧ (∃ b : LB.Gen (LB.LinComb U.LG.L (K := Fin j) (fun i => eSec G' ≫ (pG.pr i).left) (fun _ => 1)), GeneratorPullback.MapsAt U.LG.L U'.LG.L (fun i => (pG.pr i).left) wL (eSec G') 1 U'.LG.rig b ∧ LB.Gen.Corr U.LG.L _ _ _ _ b (GeneratorPullback.finProdGen U.LG.L (J := Fin j) (fun _ _ => eSec G) (fun _ _ => 1) (fun _ => U.LG.rig))) ∧ (∀ (e : ℕ) (i : Fin j), (U'.gt e).q ≫ (Over.pullback (thick R I e)).map (pD.pw.pr i) = (Over.pullback (thick R I e)).map (pG.pr i) ≫ (U.gt e).q) ∧ (∀ (e : ℕ) (x : D'.toPre.X), ∃ hψ : ∀ (i : Fin j) (k : Fin 4), D'.toPre.Oφ ((Over.map (thick R I e)).map (U'.gt e).q ≫ D'.toPre.prBe I e) x k ≫ (pD.pw.pr i).left = ((Over.pullback (thick R I e)).map (pG.pr i)).left ≫ D.toPre.Oφ ((Over.map (thick R I e)).map (U.gt e).q ≫ D.toPre.prBe I e) (pD.xe x i) k, LB.Gen.Maps (LB.linCombIso pD.w _ Oinvε) ((U'.gt e).t x) (GeneratorPullback.boxGen D.toPre.P.L (fun i => (pD.pw.pr i).left) _ Oinvε (fun i => GeneratorPullback.pullAlong D.toPre.P.L (pD.pw.pr i).left ((Over.pullback (thick R I e)).map (pG.pr i)).left _ Oinvε _ (hψ i) ((U.gt e).t (pD.xe x i))))) ∧ (∀ (e : ℕ) (jNM : Fin j → D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL' : U'.LG.L.ι) (jNL : Fin j → U.LG.L.ι), res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_left) : (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM') ⊓ (LB.div (D'.toPre.P.L.pull (U'.gt e).pG.left) (U'.LG.L.pull (fstG I e G').left)).U (fun _ => jM', fun _ => jL') ⊓ (⨅ i, ((Over.pullback (thick R I e)).map (pG.pr i)).left ⁻¹ᵁ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U (fun _ => jNM i, fun _ => jNL i)) ⊓ (fstG I e G').left ⁻¹ᵁ (LB.div (boxLB U.LG.L pG.pr) U'.LG.L).U (jNL, jL') ≤ (U'.gt e).pG.left ⁻¹ᵁ (LB.div (boxLB D.toPre.P.L pD.pw.pr) D'.toPre.P.L).U (jNM, jM')) (pullU (U'.gt e).pG.left _ (pD.w.s (jNM, jM'))) * res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_left.trans inf_le_right)) ((U'.w e).s (fun _ => jM', fun _ => jL')) = (∏ i, res (X := (thickObj R I e G').left) (inf_le_left.trans (inf_le_right.trans (iInf_le _ i))) (pullU ((Over.pullback (thick R I e)).map (pG.pr i)).left _ ((U.w e).s (fun _ => jNM i, fun _ => jNL i)))) * res (X := (thickObj R I e G').left) inf_le_right (pullU (Y := (thickObj R I e G').left) (fstG I e G').left _ (wL.s (jNL, jL')))) → ∀ (k e : ℕ) (σ : Fin j → H0 U.LG.L k) (f : Fin j → ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → ∀ (σ' : H0 U'.LG.L k) (f' : ∀ α' : D'.toPre.X, D'.toPre.SecB k α'), IsBoxSecG pG wL k σ' σ → IsBoxFamB pD k f' f → U'.ExpandsAt e k σ' f' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U wL h k e σ f hE σ' f' hσ hf
  exact expandsAt_prebox h.2.2.2.2.1 h.2.2.2.2.2 k e σ f hE σ' f' hσ hf

end GlobalTheory.BoxExpPre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiWZeroProd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem four_comm {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (p : A' ⟶ A) [IsMonHom p] (f : A ⟶ A) (f' : A' ⟶ A') (h : f' ≫ p = p ≫ f) (k : Fin 4) :
    (![(padd A' (𝟙 _) f').left, 𝟙 A'.left, f'.left, (toUnit A' ≫ η[A']).left] : Fin 4 → _) k ≫ p.left =
      p.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) k := by
  fin_cases k
  · show (padd A' (𝟙 _) f').left ≫ p.left = p.left ≫ (padd A (𝟙 _) f).left
    rw [← Over.comp_left, ← Over.comp_left]
    unfold padd
    congr 1
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, Category.id_comp, h, ← Category.assoc, comp_lift,
      Category.comp_id]
  · show 𝟙 A'.left ≫ p.left = p.left ≫ 𝟙 A.left
    simp
  · show f'.left ≫ p.left = p.left ≫ f.left
    rw [← Over.comp_left, ← Over.comp_left, h]
  · show (toUnit A' ≫ η[A']).left ≫ p.left = p.left ≫ (toUnit A ≫ η[A]).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Category.assoc, IsMonHom.one_hom, ← Category.assoc, toUnit_unique (p ≫ toUnit A) (toUnit A')]

set_option maxHeartbeats 1000000 in
theorem psi_weight_zero_product (pD : IsPowDeg D' D j) {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (hx : ∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) (oa : D.OAct O) (oa' : D'.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (w0 : O) (h : TraceFormTwistIso D oa w0) :
    TraceFormTwistIso D' oa' w0 := by
  obtain ⟨u, hu, h0, hy⟩ := h
  have := oa'.onB.hom w0
  have : ∀ i, IsMonHom (pD.pw.pr i) := pD.pw.hom
  obtain ⟨u', hu', hval⟩ := exists_boxPull_gen pD.w pD.w_gen D.P.isLB D'.P.isLB
    (φ' := ![(padd D'.P.A (𝟙 _) (oa'.onB.act w0)).left, 𝟙 D'.P.A.left, (oa'.onB.act w0).left, (toUnit D'.P.A ≫ η[D'.P.A]).left])
    (φ := fun _ => ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left])
    (ε := ![1, -2, -1, 2])
    (fun i => (pD.pw.pr i).left) (fun i k => four_comm (pD.pw.pr i) _ _ (hact w0 i) k) (fun _ => u) (fun _ => hu)
  have hη : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨u', hu', ?_, ?_⟩
  · apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    rw [val_pull hJ', val_one]
    have e1 := hval _ (𝟙 _ ≫ eSec D'.P.A) z J J' hJ hJ'
    have e2 : ∀ i, val u ((𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left) z J = 1 := by
      intro i
      have hc : (𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ eSec D.P.A := by
        simp only [Category.id_comp, eSec, ← Over.comp_left, IsMonHom.one_hom]
      rw [hc, ← val_pull hJ, val_corr hJ h0, val_one]
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (η[D'.P.A]) (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    simp only [← hη] at e3
    rw [Finset.prod_eq_one (fun i _ => e2 i)] at e1
    simp only [Category.assoc] at e1
    have e4 : ∀ m : D'.P.A.left ⟶ D'.P.A.left, eSec D'.P.A ≫ m = (η[D'.P.A]).left ≫ m := fun m => rfl
    have h1f : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ oa'.onB.act w0 = 1 := by
      rw [hη, IsMonHom.one_hom]
    simp only [e4, ← hη, e3, h1f] at e1
    have alg : ∀ {G : Type} [CommGroup G] (a v : G), a * (a ^ 2)⁻¹ * a⁻¹ * a ^ 2 * v = v := by
      intros
      group
    have h11 : ((1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) * 1) = 1 := mul_one _
    erw [h11] at e1
    rwa [alg] at e1
  · intro y
    apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    have hD : ∀ x : D.X, val (D.psi (x + w0 • x)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
        (val (D.psi (w0 • x)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (𝟙 _ ≫ D.xK x) z J =
        val (D.psi x) (𝟙 _) z J * val D.rigK (𝟙 _) z J := by
      intro x
      have hc := val_corr hJ (hy x) (𝟙 _)
      simp only [DegPre.tau, val_mul hJ, val_inv, val_pull hJ] at hc
      exact hc
    rw [val_mul hJ', val_mul hJ', val_pull hJ']
    simp only [DegPre.tau, val_mul hJ', val_inv]
    have P := fun x => psi_val pD hJ hJ' x (𝟙 _)
    have Rg := rig_val pD hJ hJ' (𝟙 _)
    have U := hval _ (𝟙 _ ≫ D'.xK y) z J J' hJ hJ'
    have hpr : ∀ i, (𝟙 _ ≫ D'.xK y) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ D.xK (pD.xe y i) := by
      intro i
      simp only [Category.id_comp, DegPre.xK, ptK, ← Over.comp_left, Category.assoc, pD.c_pr]
    simp only [hpr] at U
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (toUnit (TK R) ≫ D'.c y)
      (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    have e6 : (toUnit (TK R) ≫ D'.c y) ≫ oa'.onB.act w0 = toUnit (TK R) ≫ D'.c (w0 • y) := by
      rw [Category.assoc, ← oa'.c_lin]
    have e7 : (toUnit (TK R) ≫ D'.c y) * (toUnit (TK R) ≫ D'.c (w0 • y)) = toUnit (TK R) ≫ D'.c (y + w0 • y) := by
      rw [D'.c_add]
      unfold padd
      rw [← Category.assoc, comp_lift, Hom.mul_def]
    have e8 : ∀ x, (toUnit (TK R) ≫ D'.c x).left = D'.xK x := fun _ => rfl
    have e9 : (toUnit (TK R) ≫ η[D'.P.A]).left = (toUnit (TK R)).left ≫ eSec D'.P.A := rfl
    rw [e6, e7, Hom.one_def] at e3
    simp only [e8, e9] at e3
    simp only [Category.id_comp] at P Rg U e3 hD ⊢
    rw [e3] at U
    have hxe1 : ∀ i, pD.xe (y + w0 • y) i = pD.xe y i + w0 • pD.xe y i := by
      intro i
      rw [map_add (f := _), hx]
      rfl
    have hxe2 : ∀ i, pD.xe (w0 • y) i = w0 • pD.xe y i := by
      intro i
      rw [hx]
      rfl
    have Py := inv_mul_eq_iff_eq_mul.mp (P y)
    have Ps := inv_mul_eq_iff_eq_mul.mp (P (y + w0 • y))
    have Pw := inv_mul_eq_iff_eq_mul.mp (P (w0 • y))
    have key := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => (by rw [hxe1 i, hxe2 i]; exact hD (pD.xe y i) :
      val (D.psi (pD.xe (y + w0 • y) i)) (𝟙 _) z J * (val (D.psi (pD.xe y i)) (𝟙 _) z J)⁻¹ *
        (val (D.psi (pD.xe (w0 • y) i)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (D.xK (pD.xe y i)) z J =
        val (D.psi (pD.xe y i)) (𝟙 _) z J * val D.rigK (𝟙 _) z J))
    simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
    rw [Py, Ps, Pw, eq_inv_mul_of_mul_eq Rg, eq_inv_mul_of_mul_eq U, eq_inv_mul_of_mul_eq key]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ (oa : D.OAct O) (oa' : D'.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ w0 : O, Geo.Tor.TraceFormTwistIso D oa w0 → Geo.Tor.TraceFormTwistIso D' oa' w0 := by
  intro R _ _ j D D' pD O _ _ _ _ hx oa oa' hact w0 h
  exact psi_weight_zero_product pD hx oa oa' hact w0 h

end GlobalTheory.PsiWZeroProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlExtensionFieldOfFraction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullBaseChange

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section

variable (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F]

theorem jFK_self : jFK (R := V) (FractionRing V) = 𝟙 _ := by
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = 𝟙 _
  exact Spec.map_id _

def specFrac : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of (FractionRing V)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F))

theorem specFrac_jFK : specFrac V F ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  (congrArg (fun q => specFrac V F ≫ q) (jFK_self V)).trans (Category.comp_id _)

def toFrac : TF (R := V) F ⟶ TF (R := V) (FractionRing V) :=
  Over.homMk (specFrac V F) ((Category.assoc (specFrac V F) (jFK (R := V) (FractionRing V)) (jK V)).symm.trans
    (congrArg (fun q => q ≫ jK V) (specFrac_jFK V F)))

theorem toFrac_jFK : (toFrac V F).left ≫ jFK (R := V) (FractionRing V) = jFK (R := V) F :=
  specFrac_jFK V F

variable {V} (D : DegPre V)

def bc : DegPre.BF D F ⟶ DegPre.BF D (FractionRing V) := toFrac V F ▷ D.P.A

theorem bc_prB : bc F D ≫ DegPre.prB D (FractionRing V) = DegPre.prB D F := whiskerRight_snd _ _

theorem bc_prB_left : (bc F D).left ≫ (DegPre.prB D (FractionRing V)).left = (DegPre.prB D F).left :=
  congrArg (fun q => q.left) (bc_prB F D)

theorem zF_bc : DegPre.zF D F ≫ bc F D = toFrac V F ≫ DegPre.zF D (FractionRing V) := by
  unfold DegPre.zF bc
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, whiskerRight_snd, lift_snd]
    rw [← Category.assoc, comp_toUnit]

theorem bc_famφ (α : D.X) (i : Fin 4) :
    (bc F D).left ≫ DegPre.famφ D (FractionRing V) α i = DegPre.famφ D F α i := by
  rw [GC.famφ_eq, GC.famφ_eq, ← Category.assoc, bc_prB_left]

end

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (F : Type) [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_bc (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ bc F D.toPre = bc F D.toPre ≫ aF D (FractionRing V) oa a := by
  unfold aF
  apply CartesianMonoidalCategory.hom_ext
  · simp [bc]
  · simp only [Category.assoc, lift_snd]
    rw [← Category.assoc (bc F D.toPre), bc_prB]
    exact lift_snd _ _

theorem aF_bc_left (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (bc F D.toPre).left = (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left :=
  congrArg (fun q => q.left) (aF_bc D F oa a)

theorem bc_pullφ (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) (i : Fin 4 ⊕ Fin 4) :
    (bc F D.toPre).left ≫ pullφ D (FractionRing V) oa a χ i = pullφ D F oa a χ i := by
  rcases i with i | i
  · exact bc_famφ F D.toPre _ i
  · show (bc F D.toPre).left ≫ (aF D (FractionRing V) oa a).left ≫ _ = (aF D F oa a).left ≫ _
    rw [← Category.assoc, ← aF_bc_left, Category.assoc, bc_famφ]

theorem sval_bc {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))}
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))} {g : D.toPre.SecB k α}
    (hs : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre (FractionRing V)).left 1)
    (ht : GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) t (D.toPre.famφB α)
      (DegPre.famε k) g (DegPre.prB D.toPre F).left 1)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) :
    sval t r z J = sval s (r ≫ (bc F D.toPre).left) z J := by
  rw [← SectionScalarValuation.secScal_sval ht r z hJ, ← SectionScalarValuation.secScal_sval hs _ z hJ, Category.assoc, bc_prB_left]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (E : Fam D.toPre (FractionRing V) k) (E' : Fam D.toPre (FractionRing V) (k * N)) (g : ∀ α, D.toPre.SecB k α) (g' : ∀ α, D.toPre.SecB (k * N) α) (θ : Fam D.toPre F k) (θ' : Fam D.toPre F (k * N)), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε (k * N)) (E'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre (FractionRing V)).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (θ.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre F).left 1) → (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε (k * N)) (θ'.s α) (D.toPre.famφB α) (DegPre.famε (k * N)) (g' α) (DegPre.prB D.toPre F).left 1) → PullAl D (FractionRing V) oa a k N E E' → PullAl D F oa a k N θ θ' := by
  intro V _ _ _ D F _ _ O _ _ _ oa a k N E E' g g' θ θ' hE hE' hθ hθ' hP
  have hL := D.toPre.P.isLB
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hrel⟩ := hP.1 χ
    obtain ⟨u', hu', vu⟩ := exists_gen hL (φ' := pullφ D F oa a χ) (ε' := pullε k N)
      (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [bc_pullφ])
      (LB.pullGen D.toPre.P.L _ _ u (bc F D.toPre).left) (pullGen_isGen _ _ _ _ hu _)
    refine ⟨u', hu', corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ u').2 fun y J hJ => ?_⟩
    · have e := val_corr hJ hc (toFrac V F).left
      rw [val_pull hJ, val_pull hJ, toFrac_jFK] at e
      have z₁ : (DegPre.zF D.toPre F).left ≫ (bc F D.toPre).left =
          (toFrac V F).left ≫ (DegPre.zF D.toPre (FractionRing V)).left :=
        congrArg (fun q => q.left) (zF_bc F D.toPre)
      rw [val_pull hJ, val_pull hJ, vu _ _ y J hJ, val_pull hJ, Category.id_comp, Category.id_comp, z₁]
      exact e
    · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (bc F D.toPre).left y J hJ
      rw [sval_bc D F (hE' _) (hθ' _) _ y hJ, sval_bc D F (hE _) (hθ _) _ y hJ, vu _ _ y J hJ, val_pull hJ,
        Category.id_comp, Category.id_comp, aF_bc_left]
      exact e
  · refine fn_ext (V := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F β) j) fun y hy => ?_
    choose I hI using fun ψ : (DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left => exists_chart hL (ψ y)
    have hI' : Good D.toPre.P.L y I := hI
    have e : sval (θ'.s β) (𝟙 _) y I = 0 := by
      rw [sval_bc D F (hE' β) (hθ' β) _ y hI']
      exact (congrArg (gs _ y _) (hP.2 β hβ _)).trans (gs_zero _ y _ (hI'.mem _ _))
    refine (sec_trans (θ'.s β) (𝟙 _) y hy (hI'.mem _ _)).trans ?_
    exact (congrArg _ e).trans ((mul_zero _).trans (gs_zero _ y _ hy).symm)

end GlobalTheory.PullBaseChange
end
end

