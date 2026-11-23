module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LinOfSval
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.NuBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Generic

variable {X Y Y' Z : Scheme.{0}}

theorem lin_of_sval {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {s : LB.Sec (LB.LinComb L φ ε)} {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) J, Good L y J → sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J)
    (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  unfold resTop
  dsimp only
  refine fn_ext fun y hy0 => ?_
  have hy : (𝟙 Y) y ∈ LB.wchart L φ j := hy0
  show gs (𝟙 Y) y (LB.wchart L φ j) (s.f j) = gs (𝟙 Y) y (LB.wchart L φ j) _
  obtain ⟨J, hJ, hs⟩ := sval_trans hL s y j hy
  have hy' := hJ.mem φ (𝟙 Y)
  have e : ∀ i, gs (𝟙 Y) y (LB.wchart L φ j) ((t i).f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval (t i) (𝟙 Y) y J := fun i =>
    (sec_trans (t i) (𝟙 Y) y hy hy').trans (congrArg _ (sval_of (t i) (𝟙 Y) y J _ fun _ => rfl).symm)
  rw [hs, H y J hJ, Finset.mul_sum, gs_fsum _ _ _ hy]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ (gs_mul (𝟙 Y) y (LB.wchart L φ j) hy _ ((t i).f j)).symm
  rw [gs_res (𝟙 Y) y le_top hy (b i), e i]
  ring

theorem gs_one (r : Z ⟶ Y) (z : Z) : gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq r z ⊤ trivial, map_one, map_one]

end Generic

theorem le_val_prod {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {T : Type} (S : Finset T)
    (a : T → F) (q : T → ℚ) (h : ∀ i, ((q i : ℚ) : WithTop ℚ) ≤ v (a i)) :
    ((∑ i ∈ S, q i : ℚ) : WithTop ℚ) ≤ v (∏ i ∈ S, a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, v.map_mul, WithTop.coe_add]
    exact add_le_add (h x) ih


set_option maxHeartbeats 1600000 in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (k : ℕ) (Fs : Fin j → Fam D.toPre F k) (F' : Fam D'.toPre F k), IsBoxFam pD F k F' Fs → ∀ r : Fin j → ℚ, (∀ i, NuGe D Q F v k (Fs i) (r i)) → NuGe D' (fun x => ∑ i, Q (pD.xe x i)) F v k F' (∑ i, r i) := by
  intro V _ _ _ ϖ hϖ j D D' pD Q hQ F _ _ v k Fs F' hB r hr
  unfold IsBoxFam at hB
  unfold NuGe at hr ⊢
  intro α'
  have hBα := hB α'
  clear hB
  obtain ⟨hφ, hB⟩ := hBα
  unfold VGe at hr ⊢
  choose n a σ σF hsc hv he using fun i => hr i (pD.xe α' i)
  clear hr
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB

  choose σB hσB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφB α') (DegPre.famε k)
      (fun i => (pD.pw.pr i).left) (fun i => D.toPre.famφB (pD.xe α' i)) (famφB_pr pD α')
      (fun i => σ i (m i))

  choose σFB hσFB using fun m : (∀ i, Fin (n i)) =>
    exists_boxSec_val hM hM' pD.w pD.w_gen (D'.toPre.famφ F α') (DegPre.famε k)
      (prB pD F) (fun i => D.toPre.famφ F (pD.xe α' i)) hφ (fun i => σF i (m i))
  have hpr : ∀ i, (DegPre.prB D'.toPre F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D.toPre F).left := by
    intro i
    unfold prB
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    unfold DegPre.prB
    simp
  have hsc' : ∀ m : (∀ i, Fin (n i)), GeneratorPullback.SecScal D'.toPre.P.L (D'.toPre.famφ F α') (DegPre.famε k) (σFB m)
      (D'.toPre.famφB α') (DegPre.famε k) (σB m) (DegPre.prB D'.toPre F).left 1 := fun m =>
    BoxFamScalar.secScal_box hM hM' pD.w (GC.famφ_eq D'.toPre F α') hpr (σFB m) (fun i => σF i (m i)) (σB m)
      (fun i => σ i (m i))
      (fun y J J' hJ hJ' => hσFB m _ (𝟙 _) y J J' hJ hJ')
      (fun y J J' hJ hJ' => hσB m _ (DegPre.prB D'.toPre F).left y J J' hJ hJ')
      (fun _ => 1) 1 (fun y => by rw [Finset.prod_eq_one fun i _ => gs_one _ _, gs_one])
      (fun i => hsc i (m i))
  let e := Fintype.equivFin (∀ i, Fin (n i))
  refine ⟨Fintype.card (∀ i, Fin (n i)), fun l => ∏ i, a i (e.symm l i), fun l => σB (e.symm l),
    fun l => σFB (e.symm l), fun l => hsc' _, fun l => ?_, fun jM => ?_⟩
  · refine le_trans (le_of_eq ?_) (le_val_prod v Finset.univ _ _ fun i => hv i (e.symm l i))
    congr 1
    simp only [Finset.sum_add_distrib, Finset.sum_div, Int.cast_sum]
  ·
    have H : ∀ (y : (D'.toPre.BF F).left) (J' : ((D'.toPre.BF F).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι),
        Good D'.toPre.P.L y J' → sval (F'.s α') (𝟙 _) y J' =
          ∑ l, gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (e.symm l i)))) * sval (σFB (e.symm l)) (𝟙 _) y J' := by
      intro y J' hJ'
      obtain ⟨J, hJ, -⟩ := exists_good _ hM y (K := Empty) Empty.elim Empty.elim (fun x => x.elim)
        (fun x => x.elim)
      have hle : ∀ (jN : Fin 4 → Fin j → D.toPre.P.L.ι) (jM : Fin 4 → D'.toPre.P.L.ι) (i : Fin j),
          LB.wchart (LB.LinComb D.toPre.P.L (fun i => (pD.pw.pr i).left) (fun _ => 1)) (D'.toPre.famφ F α') jN ⊓
            LB.wchart D'.toPre.P.L (D'.toPre.famφ F α') jM ≤
              prB pD F i ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφ F (pD.xe α' i)) (fun a => jN a i) :=
        fun jN jM i => inf_le_left.trans (box_le_of_comp D.toPre.P.L (fun i => (pD.pw.pr i).left)
          (D'.toPre.famφ F α') (D.toPre.famφ F (pD.xe α' i)) (prB pD F i) i (hφ i) jN)
      have hF := BoxFamScalar.box_sval pD.w hφ (F'.s α') (fun i => (Fs i).s (pD.xe α' i)) hle hB (𝟙 _) y hJ hJ'
      have hfac : ∀ i, sval ((Fs i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J =
          ∑ l, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i l))) * sval (σF i l) (𝟙 _ ≫ prB pD F i) y J := by
        intro i
        have hm := hJ.mem (D.toPre.famφ F (pD.xe α' i)) (𝟙 _ ≫ prB pD F i)
        unfold sval
        refine (congrArg (gs (𝟙 _ ≫ prB pD F i) y _) (he i _)).trans ?_
        refine (gs_fsum _ y _ hm _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
        refine (gs_mul _ y _ hm _ _).trans ?_
        unfold DegPre.constBF
        exact congrArg (· * _) (gs_res _ y le_top hm _)
      have hcst : ∀ m : (∀ i, Fin (n i)), ∏ i, gs (𝟙 _ ≫ prB pD F i) y ⊤ (((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i (m i)))) =
          gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) := by
        intro m
        refine BoxFamScalar.gs_scal_prod (fst (TF (R := V) F) D.toPre.P.A).left
          (fst (TF (R := V) F) D'.toPre.P.A).left (prB pD F) (fun i => ?_) y (fun i => a i (m i))
        unfold prB
        rw [← Over.comp_left]
        simp
      refine (Units.mul_right_inj (∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a)).1 ?_
      refine hF.trans ?_
      rw [Finset.mul_sum]
      simp only [hfac]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      rw [Equiv.sum_comp e.symm (fun m => ((∏ a, bw pD.w (𝟙 _ ≫ D'.toPre.famφ F α' a) y (fun i => J ((𝟙 _ ≫ D'.toPre.famφ F α' a) ≫ (pD.pw.pr i).left)) (J' (𝟙 _ ≫ D'.toPre.famφ F α' a)) ^ DegPre.famε k a) : _) * (gs (𝟙 _) y ⊤ (((fst (TF (R := V) F) D'.toPre.P.A).left.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (∏ i, a i (m i)))) * sval (σFB m) (𝟙 _) y J'))]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.prod_mul_distrib, hcst m, ← hσFB m _ (𝟙 _) y J J' hJ hJ']
      ring
    have key := lin_of_sval hM' _ (fun l => σFB (e.symm l)) H jM
    unfold resTop at key
    unfold DegPre.constBF
    exact key

end GlobalTheory.NuBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowGrp

theorem nonempty_torusExtension_of_isPowGrp : ∀ (K : Type) [Field K] (G' G : Over (Spec (CommRingCat.of K))) [GrpObj G'] [GrpObj G] (j : ℕ), IsPowGrp G' G j → Nonempty (TorusExtension G) → Nonempty (TorusExtension G') := by
  intro K _ G' G _ _ j p hT
  obtain ⟨T⟩ := hT
  cases T with
  | mk X B hB q hqm0 hqf0 hqs0 hqc0 i him0 hker =>
    have pB := ReciprocityTheory.ChartRestriction.G.Out.powIsPowGrp B j
    have pT := GlobalTheory.SplitTorusPow.isPowGrp (Spec (CommRingCat.of K)) (AddEquiv.refl (Fin j → X))
    obtain ⟨q', hq, hqm, hqf, hqs, hqc, -⟩ := GlobalTheory.PowMap.main _ G' G _ B j p pB q
    obtain ⟨i', hi, him, -⟩ := GlobalTheory.PowMap.main _ _ _ G' G j pT p i
    exact ⟨{ X := Fin j → X
             addCommGroup := inferInstance
             free := inferInstance
             finite := inferInstance
             B := ReciprocityTheory.ChartRestriction.G.Out.powObj B j
             grpB := inferInstance
             isAbelian := (GlobalTheory.PowGrp.powers _ _ _ j pB).2.2.2.1 hB
             q := q'
             q_hom := hqm hqm0
             q_flat := hqf hqf0
             q_surjective := hqs hqs0
             q_quasiCompact := hqc hqc0
             i := i'
             i_hom := him him0
             isKernel := GlobalTheory.PowKernel.main _ _ _ G' G _ _ j pT p pB i q i' q' hi hq hker }⟩

theorem isSemiAbelian_pow : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j : ℕ) (p : IsPowGrp G' G j), IsSemiAbelian G → IsSemiAbelian G' := by
  intro S G' G _ _ _ _ j p' hG
  obtain ⟨_, hs, hsep, hqc, hgc, hf⟩ := hG
  have hpow := GlobalTheory.PowGrp.powers S G' G j p'
  have hqg := GlobalTheory.PowGrp.quasiCompact_geomConnected_pow S G' G j p'
  refine ⟨inferInstance, hpow.1 hs, hpow.2.1 hsep, hqg.1 hqc, hqg.2 hs hgc, ?_⟩
  intro Ω _ _ x
  obtain ⟨px, -⟩ := GlobalTheory.isPowGrp_baseChange S _ x G' G j p'
  exact nonempty_torusExtension_of_isPowGrp Ω _ _ j px (hf Ω x)

end GlobalTheory.PowGrp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfPowEqOne
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaNu

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem units_mul_eq_mul_of_eq_mul {R : Type*} [CommRing R] (a b c : Rˣ) (x y : R) (h : x = y * c) :
    (a : R) * x = ((a * b⁻¹ * c : Rˣ) : R) * ((b : R) * y) := by
  rw [h, Units.val_mul, Units.val_mul]
  have hb : ((b⁻¹ : Rˣ) : R) * b = 1 := Units.inv_mul b
  linear_combination (-((a : R) * c * y)) * hb

theorem isActOf_of_sval {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T}
    {s s' : LB.Sec (LPow A L k T)}
    (h : ∀ y J, Good L y J → sval (L := L) s' (𝟙 _) y J =
      sval (L := L) s (𝟙 _ ≫ (translT A θ.pt).left) y J * (val (L := L) θ.φ (𝟙 _) y J).val) :
    IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  intro j
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := exists_good L hL x (K := Empty) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim)
  have hx0 : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0) :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hx 0
  have hx1 : (𝟙 _ ≫ (translT A θ.pt).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1) := by
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 := Set.mem_iInter.1 hx 1
    simpa [← hcomp] using h1
  have e1 := sec_trans s' (𝟙 _) x hx0 (hJ.mem _ (𝟙 _))
  have e2 := sec_trans s (𝟙 _ ≫ (translT A θ.pt).left) x hx1 (hJ.mem _ _)
  have e3 := gen_trans θ.isGen (𝟙 _) x hx (hJ.mem _ (𝟙 _))
  have key := h x J hJ
  unfold sval val at key
  refine (gs_res (𝟙 _) x _ hx _).trans (e1.trans ?_)
  refine Eq.trans ?_ (gs_mul (𝟙 _) x _ hx _ _).symm
  refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_unit (𝟙 _) x _ hx _)
    ((gs_res (𝟙 _) x _ hx _).trans (gs_pull _ _ x _ hx1 _))).symm
  rw [e2, e3]
  have htr : trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) x j
        (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) =
      trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) x (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) *
        (trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) x (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)))⁻¹ := by
    simp only [trF, Fin.prod_univ_two, Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      zpow_neg, Category.assoc, hcomp]
    rw [show J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left) = J (𝟙 _ ≫ (translPt A θ.pt).left) by
      rw [Category.assoc, hcomp]]
    rfl
  rw [htr]
  exact units_mul_eq_mul_of_eq_mul _ _ _ _ _ key

theorem exists_isActOf {L : LB A.left} (hL : L.IsLB) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  have hcomp : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    simp
  have hform : FormEq (Sum.elim (fun _ : Fin 1 => (translT A θ.pt).left ≫ (snd T A).left)
      ![(snd T A).left, (translPt A θ.pt).left]) (Sum.elim (fun _ => k) ![k, -k])
      (fun _ : Fin 1 => (snd T A).left) (fun _ => k) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl, Sum.elim_inr,
      Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, hcomp]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨s₁, hs₁⟩ := exists_sec hL hform (pullMulSec s (translT A θ.pt).left θ.φ θ.isGen)
  refine ⟨s₁, isActOf_of_sval hL fun y J hJ => ?_⟩
  rw [hs₁ _ _ y J hJ]
  exact sval_pullMulSec _ _ _ _ _ _ hJ

end GlobalTheory.ThetaNu

namespace GlobalTheory


open ThetaNu in
theorem nuGe_iff_of_isActOf_of_pow_eq_one : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t₀ : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t₀), P.TorsionIso → Geo.Tor.ExpBijF P.U.toUnifPre → ∀ (Q : P.D.toPre.X → ℤ), QForm.IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (P.A.L.pull P.U.gen.hom.left) (P.U.LG.L.pull (pullback.fst t₀.G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp P.A.A P.A.L (k : ℤ) (TFK (R := V) F)) (n : ℕ), 1 ≤ n → θ.pt ^ k = 1 → θ.pt ^ n = 1 → LB.Gen.Corr P.A.L _ _ _ _ (Out.powGen P.A.A P.A.L (k : ℤ) θ n) (LB.oneGen P.A.L) → ∀ (t t' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam P.D.toPre F k), P.U.ExpandsF F k w t s → P.U.ExpandsF F k w t' s' → IsActOf P.A.A P.A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe P.D Q F v k s r ↔ NuGe P.D Q F v k s' r := by
  intro hLaws hTW V _ _ _ ϖ hϖ E _ _ _ H t₀ P hTI hEB Q hQ F _ _ _ v hv k hk w hw θ n hn hθk hθn hc t t' s s' hs hs'
    hact r

  obtain ⟨f, hf, hsurj, -⟩ := hTI F k hk
  obtain ⟨p, hp⟩ := hsurj θ.pt hθk
  have hpt := (hf p θ.pt).2 hp.symm
  unfold Geo.Tor.PELUnif.ToA QkToAkU QkToAk at hpt
  obtain ⟨w₁, hw₁, hΦ⟩ := (hpt w hw).2 θ rfl

  obtain ⟨c, hTWc⟩ := hTW V ϖ hϖ P.D Q hQ F v hv k hk p w₁ hw₁ 1 one_ne_zero
  have step : ∀ (u u' : LB.Sec (LPow P.A.A P.A.L (k : ℤ) (TFK (R := V) F))) (e e' : Fam P.D.toPre F k),
      P.U.ExpandsF F k w u e → P.U.ExpandsF F k w u' e' → IsActOf P.A.A P.A.L (k : ℤ) θ u u' →
      ∀ q : ℚ, NuGe P.D Q F v k e q ↔ NuGe P.D Q F v k e' (q + c) := fun u u' e e' he he' ha q =>
    hTWc e e' e' (hΦ u u' e e' he he' ha) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff 1 e' e').2 (one_smul F e').symm) q

  have hL : P.A.L.IsLB := P.A.isLB
  choose g hg using fun u => exists_isActOf hL θ u
  have horb : ∀ m : ℕ, IsActOf P.A.A P.A.L (k : ℤ) θ (g^[m] t) (g^[m + 1] t) := fun m => by
    rw [Function.iterate_succ_apply']
    exact hg _
  have hexp := hEB F k hk w hw
  choose e he using fun m : ℕ => (hexp.1 (g^[m] t)).exists
  have hshift : ∀ (m : ℕ) (q : ℚ), NuGe P.D Q F v k (e 0) q ↔ NuGe P.D Q F v k (e m) (q + m * c) := by
    intro m
    induction m with
    | zero => intro q; simp
    | succ m ih =>
      intro q
      rw [ih q, step _ _ _ _ (he m) (he (m + 1)) (horb m)]
      push_cast
      ring_nf

  have hback : g^[n] t = t := by
    have hf := thetaGrp_act_iterate_eq_of_pow_eq_one _ P.A.A P.A.L hL (k : ℤ) (TFK (R := V) F) θ n hθn hc
      (fun i => g^[i] t) (fun i => by simpa using horb i)
    generalize hu : g^[n] t = u at hf
    simp only [Fin.val_last, Fin.val_zero, hu, Function.iterate_zero, id] at hf
    obtain ⟨uf, uc⟩ := u
    obtain ⟨tf, tc⟩ := t
    obtain rfl : uf = tf := funext hf
    rfl
  have he0 : e 0 = s := (hexp.1 t).unique (he 0) hs
  have hen : e n = s := (hexp.1 t).unique (by rw [← hback]; exact he n) hs
  have hper : ∀ q : ℚ, NuGe P.D Q F v k s q ↔ NuGe P.D Q F v k s (q + n * c) := by
    intro q
    rw [← he0, hshift n q, he0, hen]

  have hmono : ∀ q q' : ℚ, q' ≤ q → NuGe P.D Q F v k s q → NuGe P.D Q F v k s q' := by
    intro q q' hqq h χ
    obtain ⟨m, a, σ, σF, h1, h2, h3⟩ := h χ
    exact ⟨m, a, σ, σF, h1, fun i => le_trans (WithTop.coe_le_coe.2 (by linarith)) (h2 i), h3⟩
  have hs's : NuGe P.D Q F v k s (r - c) ↔ NuGe P.D Q F v k s' r := by
    simpa using step t t' s s' hs hs' hact (r - c)
  rw [← hs's]
  by_cases hc0 : c = 0
  · simp [hc0]
  · have hd : (n : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) hc0
    exact ⟨fun h => PeriodicValuation.all_of_periodic hmono hd hper r _ h, fun h => PeriodicValuation.all_of_periodic hmono hd hper _ r h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NuGeIffOfIsActOfOfQkToAkU
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem nuGe_iff_of_isActOf_of_qkToAkU : Laws → TWStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G), Geo.Tor.ExpBijF U.toUnifPre → ∀ (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK V)))), w.IsGen → ∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := V) F)) (p : QkPt D.toPre F k), QkToAkU U.toUnifPre F k p θ.pt → ∀ (n : ℕ), 1 ≤ n → θ.pt ^ n = 1 → LB.Gen.Corr A.L _ _ _ _ (Out.powGen A.A A.L (k : ℤ) θ n) (LB.oneGen A.L) → ∀ (t t' : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F))) (s s' : Fam D.toPre F k), U.ExpandsF F k w t s → U.ExpandsF F k w t' s' → IsActOf A.A A.L (k : ℤ) θ t t' → ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' r := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U hB Q hQ F _ _ v hv k hk w hw θ p hp n hn hx hc t t' s s' hs hs' hact r
  obtain ⟨w₀, hw₀, hΦθ⟩ := (hp w hw).2 θ rfl
  obtain ⟨hB₁, hB₂⟩ := hB F k hk w hw
  obtain ⟨Φ, hΦ⟩ := phiFun_of hL V (maximalIdeal V) D F k hk p w₀ hw₀
  choose act hact' using fun x : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)) =>
    (VVRank.exists_isTwistPull A.A A.isLB θ.isGen x : ∃ y, IsActOf A.A A.L (k : ℤ) θ x y)
  have hfin : FinOrd D F k p w₀ 1 := by
    refine ⟨n, hn, fun ss ts hss => ?_⟩
    obtain ⟨t₀, ht₀, -⟩ := hB₂ (ss 0)
    have key : ∀ (i : ℕ) (hi : i < n + 1), U.ExpandsF F k w (act^[i] t₀) (ss ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero => exact fun _ => ht₀
      | succ i ih =>
        intro hi
        obtain ⟨s₁, hs₁, -⟩ := hB₁ (act^[i + 1] t₀)
        have h₁ := (hΦ _ _).1 (hΦθ _ _ _ _ (ih (by omega)) hs₁
          (by rw [Function.iterate_succ_apply']; exact hact' _))
        obtain ⟨h₂, h₃⟩ := hss ⟨i, by omega⟩
        have h₄ : ss ⟨i + 1, hi⟩ = s₁ :=
          ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).1 h₃).trans
            ((one_smul F _).trans (((hΦ _ _).1 h₂).trans h₁.symm))
        rw [h₄]; exact hs₁
    have hcyc := thetaGrp_act_iterate_eq_of_pow_eq_one _ A.A A.L A.isLB (k : ℤ) _ θ n hx hc
      (fun i => act^[i.val] t₀) (fun i => by
        show IsActOf _ _ _ θ (act^[i.val] t₀) (act^[i.val + 1] t₀)
        rw [Function.iterate_succ_apply']; exact hact' _)
    have he : act^[n] t₀ = t₀ := by
      have ext : ∀ a b : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := V) F)), (∀ j, a.f j = b.f j) → a = b := by
        rintro ⟨a, _⟩ ⟨b, _⟩ h
        obtain rfl : a = b := funext h
        rfl
      exact ext _ _ hcyc
    have h₅ := key n (Nat.lt_succ_self n)
    rw [he] at h₅
    have h₆ : ss (Fin.last n) = ss 0 := (hB₁ t₀).unique h₅ ht₀
    intro α j
    rw [h₆]
  exact galois_fixed_adelic_matrices_descend hL hTW V ϖ hϖ D Q hQ F v hv k hk p w₀ hw₀ 1 one_ne_zero hfin s s' s'
    (hΦθ t t' s s' hs hs' hact) ((ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff _ _ _).2 (one_smul F _).symm) r

end GlobalTheory
end

