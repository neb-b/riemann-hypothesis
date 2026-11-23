module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem fam_sum_f {k : ℕ} {Ix : Type} [Fintype Ix] (c : Ix → F) (s : Ix → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i, c i • s i).s α).f j = ∑ i, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
  classical
  have key : ∀ t : Finset Ix, ((∑ i ∈ t, c i • s i).s α).f j =
      ∑ i ∈ t, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_f, smul_f, ih]
  exact key Finset.univ

theorem fam_eq_zero (hG : GlobalFnsSt) {k : ℕ} (P : D.toPre.X → Prop) (hP : ∀ χ, ∃ α mu, P α ∧ α + k • mu = χ)
    (s : Fam D.toPre F k) (h0 : ∀ α, P α → ∀ j, (s.s α).f j = 0) : s = 0 := by
  have hL := D.toPre.P.isLB
  refine DVR.fam_ext fun χ j => ?_
  obtain ⟨α, mu, hα, rfl⟩ := hP χ
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG k mu α
  have hrel := s.fe mu α u hu hc
  refine sec_ext_val hL (s' := (0 : Fam D.toPre F k).s (α + k • mu)) (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, sval_zero_of (h0 α hα) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul, sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)]

theorem vge_coords {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c : Fin m → F}
    (hc : RepF bF t c) {r : ℚ} (ht : VGe D F v k ρ t r) : ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := ht
  have hσ : ∀ l, ∃ c' : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c' i)) ∧ RepF bF (σF l) c' := fun l =>
    coordsO hϖ hv b hb bF hbF (σ l) (σF l) fun y J hJ => by
      rw [← secScal_sval (hscal l) (𝟙 _) y hJ, Category.id_comp]
  choose c' hc'v hc' using hσ
  have hrep : RepF bF t (fun i => ∑ l, a l * c' l i) := fun y J hJ => by
    rw [sval_lin (fun l => gF D.toPre F (a l)) σF (fun j => hsum j) (𝟙 _) y hJ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, gs_sum _ y ⊤ trivial, gs_mul _ y ⊤ trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc' l y J hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e := repF_unique hU hc hrep
  intro i
  rw [e]
  refine AddValuation.map_le_sum v fun l _ => ?_
  rw [AddValuation.map_mul]
  calc ((r : ℚ) : WithTop ℚ) = (r : WithTop ℚ) + 0 := (add_zero _).symm
    _ ≤ v (a l) + v (c' l i) := add_le_add (hva l) (hc'v l i)

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm

theorem qAl_of (hLaws : Laws) : QAlStatement := by
  unfold QAlStatement
  intro V _ _ _ ϖ hϖ D Q hQ O _ _ _ oa a N h1 _ χ

  have hb : bOf D.toPre Q (star a • χ) (star a • χ) = bOf D.toPre Q χ ((N : O) • χ) := by
    rw [bOf_balance hϖ D hLaws oa hQ (star a) χ (star a • χ), star_star, smul_smul, h1]
  have hN : ((N : O) • χ) = N • χ := Nat.cast_smul_eq_nsmul O N χ

  have hlin (n : ℕ) : bOf D.toPre Q χ (n • χ) = n * bOf D.toPre Q χ χ := by
    rw [bOf_comm D (Q := Q) χ (n • χ)]
    induction n with
    | zero =>
      have h := bOf_add_left hϖ D hQ (0 : D.toPre.X) 0 χ
      simp only [zero_add] at h
      simpa using (show bOf D.toPre Q 0 χ = 0 by linarith)
    | succ n ih =>
      rw [succ_nsmul, bOf_add_left hϖ D hQ, ih, Nat.cast_succ, add_mul, one_mul]
  have e1 := two_Q_eq hϖ D hQ (star a • χ)
  have e2 := two_Q_eq hϖ D hQ χ
  rw [hb, hN, hlin N, ← e2] at e1
  linarith

end ReciprocityTheory.ChartRestriction.G.DVR.QuadraticAlgebraValuation
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
section
set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out

theorem vRatioGt : VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

theorem tw_of_laws (hL : Laws) (hT : TwistBaseChangeStatement) : TWStatement :=
  tw_of hL.globalFns (twistBCSpan_of hT) vRatioGt

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFam
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section FEGen

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_fe_gen (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (k : ℕ)
    (mu α : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (DegPre.famMult D.toPre F k mu α) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ :=
    ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have face1 (x y' : TF (R := V) F ⟶ D.toPre.P.A) : cubV D.toPre.cub y J 1 x y' = 1 := by
      have H := val_corr hJ (D.toPre.cub.face 0) (lift x y').left
      rw [val_one] at H
      refine Eq.trans ?_ H
      refine Eq.trans ?_ (val_cub D.toPre.cub (lift x y') hJ (pzero D.toPre.P.A _) (x2 D.toPre.P.A 0) (x2 D.toPre.P.A 1)).symm
      congr 1 <;> simp [x2, pzero, Hom.one_def]
    have face2 (x y' : TF (R := V) F ⟶ D.toPre.P.A) : cubV D.toPre.cub y J x 1 y' = 1 := by
      have H := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_first (lift x (lift 1 y')).left).trans
        (val_cub D.toPre.cub (lift x (lift 1 y')) hJ _ _ _)
      have E : cubV D.toPre.cub y J x 1 y' = cubV D.toPre.cub y J 1 x y' := by
        refine Eq.trans H ?_
        congr 1 <;> simp [x3]
      rw [E, face1]
    have N_one (k : ℕ) (a m : TF (R := V) F ⟶ D.toPre.P.A) : cubN (cubV D.toPre.cub y J) k a m 1 = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have H := (val_corr hJ D.toPre.cub.cubeSymmetric_swap_last (lift (a * m ^ i) (lift m 1)).left).trans
        (val_cub D.toPre.cub (lift (a * m ^ i) (lift m 1)) hJ _ _ _)
      have E : cubV D.toPre.cub y J (a * m ^ i) m 1 = cubV D.toPre.cub y J (a * m ^ i) 1 m := by
        refine Eq.trans H ?_
        congr 1 <;> simp [x3]
      rw [E, face2]
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, N_one, face2, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  exact ⟨u, hu, hcorr⟩

theorem fam_eq_zero (hϖ : Irreducible ϖ) (G : Fam D.toPre F 1)
    (h0 : ∀ j : Fin 4 → D.toPre.P.L.ι, (G.s 0).f j = 0) :
    ∀ (mu : D.toPre.X) (j : Fin 4 → D.toPre.P.L.ι), (G.s mu).f j = 0 := by
  classical
  choose Q hQ using QForm.exists_QVal hϖ D
  intro mu j
  obtain ⟨u, hu, hc⟩ := exists_fe_gen (F := F) hϖ (Q := Q) hQ 1 mu 0
  have hrel := G.fe mu 0 u hu hc
  have e01 : (0 : D.toPre.X) + 1 • mu = mu := by simp
  rw [e01] at hrel
  have hL := D.toPre.P.isLB
  refine TopCat.Presheaf.section_ext (DegPre.BF D.toPre F).left.sheaf _ _ 0 fun y hy => ?_
  choose ch hch using WeightPf.exists_chart D.toPre.P.L hL
  let j₁ : Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.famφ D.toPre F mu k).base y)
  let j₂ : Fin 4 → D.toPre.P.L.ι := fun k => ch (((DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k).base y)
  let j₃ : Fin 4 ⊕ Fin 4 → D.toPre.P.L.ι := fun k => ch ((DegPre.deltaφ D.toPre F 1 0 mu k).base y)
  have hcoh : LB.Coh D.toPre.P.L (Sum.elim (DegPre.famφ D.toPre F mu)
      (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
        (DegPre.deltaφ D.toPre F 1 0 mu))) (Sum.elim j₁ (Sum.elim j₂ j₃)) := by
    have key : ∀ z, (Sum.elim j₁ (Sum.elim j₂ j₃)) z = ch (((Sum.elim (DegPre.famφ D.toPre F mu)
        (Sum.elim (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k)
          (DegPre.deltaφ D.toPre F 1 0 mu))) z).base y) := by
      rintro (z | z | z) <;> rfl
    intro a b hab
    rw [key a, key b, hab]
  have E := hrel j₁ j₂ j₃ hcoh
  have hy1 : y ∈ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ := Set.mem_iInter.2 fun k => hch _
  have hy2 : y ∈ LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ :=
    Set.mem_iInter.2 fun k => hch _
  have hy3 : y ∈ LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ := Set.mem_iInter.2 fun k => hch _

  have hz : ((DegPre.BF D.toPre F).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_left :
      LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
        LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃ ≤ _)).op).hom ((G.s mu).f j₁) = 0 := by
    erw [E, h0 j₂, map_zero, map_zero, zero_mul]

  let W := LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓
    (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (DegPre.trF D.toPre F mu).left ≫ DegPre.famφ D.toPre F 0 k) j₂ ⊓
      LB.wchart D.toPre.P.L (DegPre.deltaφ D.toPre F 1 0 mu) j₃)
  have hyW : y ∈ W := ⟨hy, ⟨⟨hy1, hy2⟩, hy3⟩⟩
  have hW1 : W ≤ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F mu) j₁ :=
    le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_left))
  have hc1 := congrArg (rs hW1) ((G.s mu).compat j j₁)
  have hWz : rs (inf_le_left : W ≤ _) ((G.s mu).f j) = 0 := by
    erw [rs_rs, rs_mul, rs_rs] at hc1
    erw [hc1]
    have := congrArg (rs (inf_le_right : W ≤ _)) hz
    erw [rs_rs] at this
    erw [this]
    exact (congrArg _ (map_zero _)).trans (mul_zero _)
  show (DegPre.BF D.toPre F).left.presheaf.germ _ y hy ((G.s mu).f j) = (DegPre.BF D.toPre F).left.presheaf.germ _ y hy 0
  erw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left : W ≤ _)) y hyW]
  exact (congrArg _ hWz).trans ((map_zero _).trans (map_zero _).symm)

end FEGen

section Local

end Local

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

