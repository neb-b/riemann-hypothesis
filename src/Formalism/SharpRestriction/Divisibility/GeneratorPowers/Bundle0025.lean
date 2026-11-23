module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETSpan
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem etSpan_holds : ETSpanStatement := by
  intro E _ _ Y _ _ _ R' hR' r y z hgen a
  set X : Submodule (𝓞 E) Y := Submodule.span (𝓞 E) (Set.range fun b => y b + R' • z b) with hX

  have hdec : ∀ a : Y, ∃ x ∈ X, ∃ t : Y, a = x + R' • t := by
    intro a
    obtain ⟨u, hu, t, rfl⟩ := hgen a
    have hspan : Submodule.span (𝓞 E) (Set.range y) ≤
        X ⊔ LinearMap.range (R' • LinearMap.id : Y →ₗ[𝓞 E] Y) := by
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_sup]
      refine ⟨y b + R' • z b, Submodule.subset_span ⟨b, rfl⟩, R' • (-z b), ⟨-z b, rfl⟩, ?_⟩
      rw [smul_neg, add_neg_cancel_right]
    obtain ⟨x, hx, w, ⟨t', rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hspan hu)
    refine ⟨x, hx, t' + t, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add, add_assoc]

  let Xz : Submodule ℤ Y := X.restrictScalars ℤ
  let I : Ideal ℤ := Ideal.span {(R' : ℤ)}
  have hfg : (⊤ : Submodule ℤ (Y ⧸ Xz)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule ℤ (Y ⧸ Xz)) ≤ I • ⊤ := by
    intro m _
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective Xz m
    obtain ⟨x, hx, t, rfl⟩ := hdec b
    have hx' : Submodule.Quotient.mk (p := Xz) x = 0 :=
      (Submodule.Quotient.mk_eq_zero Xz).2 ((Submodule.restrictScalars_mem ℤ X x).2 hx)
    rw [Submodule.Quotient.mk_add, hx', zero_add, Submodule.Quotient.mk_smul, ← Nat.cast_smul_eq_nsmul ℤ]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨s, hs1, hs⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hfg hle
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.mem_span_singleton, zero_sub, dvd_neg] at hs1
    have h1 : ((R' : ℤ)) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg R') hs1
    omega
  have hsa : s • a ∈ X := by
    have h0 : s • Submodule.Quotient.mk (p := Xz) a = 0 := hs _ Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.restrictScalars_mem ℤ X _).1 h0
  refine ⟨s.natAbs, Int.natAbs_pos.2 hs0, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rcases Int.natAbs_eq s with h | h
  · rw [← h]
    exact hsa
  · have : ((s.natAbs : ℤ)) = -s := by omega
    rw [this, neg_smul]
    exact X.neg_mem hsa

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGOPf
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory


set_option maxHeartbeats 800000 in
theorem bqOrigin : BqOriginSt := by
  unfold BqOriginSt
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C a wLa hLa wLb hLb Z r z J hJ

  have hA : ∀ e : 𝓞 E, (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act e = 1 := by
    intro e
    haveI := Xo.univ.t.act.hom e
    first
      | (simp; done)
      | (show (toUnit _ ≫ η[Xo.univ.t.G]) ≫ _ = toUnit _ ≫ η[Xo.univ.t.G]
         rw [Category.assoc, IsMonHom.one_hom])

  have hF : lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 = lift 1 (lift 1 1) := by
    first
      | (rw [show faceMap Xo.univ.t.G 2 = lift (x2 Xo.univ.t.G 0)
              (lift (x2 Xo.univ.t.G 1) (pzero Xo.univ.t.G (G2 Xo.univ.t.G))) from rfl,
            comp_lift, comp_lift,
            show x2 Xo.univ.t.G 0 = fst _ _ from rfl, show x2 Xo.univ.t.G 1 = snd _ _ from rfl,
            lift_fst, lift_snd,
            show pzero Xo.univ.t.G (G2 Xo.univ.t.G) = (1 : G2 Xo.univ.t.G ⟶ Xo.univ.t.G) from rfl,
            ExpGD.comp_one'])
      | (simp [faceMap, x2, pzero]; done)

  have hR : val C.wP (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J =
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    rw [← val_corr hJ C.prim.2 (r ≫ (toUnit (overAt y.x S)).left), val_pull hJ, Category.assoc]
    all_goals first | rfl | exact hJ
  have hP : ∀ e : 𝓞 E, val C.wP ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (Xo.univ.t.act.act e).left) z J = val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    intro e
    rw [Category.assoc, ← Over.comp_left, hA, hR]

  have hC : ∀ e₁ e₂ e₃ : 𝓞 E, val Xo.univ.t.cub.t ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃))).left) z J = 1 := by
    intro e₁ e₂ e₃
    have hm : (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫
        lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 := by
      rw [hF, comp_lift, comp_lift, hA, hA, hA]
    rw [Category.assoc, ← Over.comp_left, hm, Over.comp_left, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (Xo.univ.t.cub.face 2) _).trans ?_)
    first | exact val_one _ | exact val_one hJ _ | (simp [val_one, hJ]; done)

  have hLa0 : val wLa ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C a wLa hLa r z J hJ
  have hLb0 : val wLb ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C (H.bar a) wLb hLb r z J hJ

  have hCB : val (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left)))
      (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 := by
    refine (val_mul hJ _ _ _).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    refine (congrArg _ (val_mul hJ _ _ _)).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _),
      show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    simp

  change val (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (1 + a * H.bar a)).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ C.wP)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (a * H.bar a)).left))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act 1))).left)
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act (a * H.bar a)))).left)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left)))))
    (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1
  simp only [val_mul hJ, val_inv, val_pull hJ, hP, hR, hC, hLa0, hLb0, hJ]
  rw [hCB]
  clear hA hF hR hP hC hLa0 hLb0 hstar hLa hLb hCB
  generalize val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J = R
  group

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.HasSubstActPS
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

open MvPowerSeries NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S] (c : Coeff l) [Algebra c.F S]

theorem const_actPS (a : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) : constantCoeff (actPS (Dw := Dw) (S := S) c a q) = 0 := by
  simp [actPS]

theorem hasSubst_actPS (a : 𝓞 E) : HasSubst (actPS (Dw := Dw) (S := S) c a) :=
  hasSubst_of_constantCoeff_zero (fun q => const_actPS c a q)

theorem actPS_comp (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    subst (actPS (Dw := Dw) (S := S) c v) (actPS (Dw := Dw) (S := S) c u q) = actPS (Dw := Dw) (S := S) c (u * v) q := by
  have hv := hasSubst_actPS (Dw := Dw) (S := S) c v
  have e : actPS (Dw := Dw) (S := S) c u q =
      algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 u) • MvPowerSeries.X q := rfl
  rw [e, subst_smul hv, subst_X hv]
  simp only [actPS, smul_smul, map_mul]

theorem φa_mul {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (u v : 𝓞 E) (j : Fin d) :
    subst (actPS (Dw := Dw) c v) (φa c φ u j) = φa c φ (u * v) j := by
  simp only [φa]
  rw [subst_comp_subst_apply (hasSubst_actPS c u) (hasSubst_actPS c v)]
  congr 1
  funext q
  exact actPS_comp c u v q

theorem φa_one {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : φa c φ 1 = φ := by
  have e : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  funext j
  simp only [φa, e, subst_self, id]

theorem actPS_add (u v : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    actPS (Dw := Dw) (S := S) c u q + actPS (Dw := Dw) (S := S) c v q = actPS (Dw := Dw) (S := S) c (u + v) q := by
  simp only [actPS, map_add (f := _), add_smul]

theorem const_φa {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (u : 𝓞 E) (j : Fin d) : constantCoeff (φa c φ u j) = 0 :=
  ExpGF.const_substPS _ (fun q => const_actPS c u q) _ (hφ j)

theorem law_φa {d : ℕ} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {uvec : Lt1 Dw → Fin d → S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : IsExpOf F uvec φ) (u v : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 2 × Fin d => φa c φ (![u, v] p.1) p.2) (F j) = φa c φ (u + v) j := by
  let b : Fin 2 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
    fun p => actPS (Dw := Dw) (S := S) c (![u, v] p.1) ((0 : Fin 1), p.2)
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (fun p => const_actPS c _ _)
  have hX : ∀ i : Fin 2, HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X (i, q.2) : MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    fun i => hasSubst_of_constantCoeff_zero (fun q => by simp)
  have hA : HasSubst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) :=
    hasSubst_of_constantCoeff_zero (fun p => ExpGF.const_substPS _ (fun q => by simp) _ (hφ.const p.2))
  have hS : HasSubst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) :=
    hasSubst_of_constantCoeff_zero (fun q => by simp)
  have key := congrArg (MvPowerSeries.subst b) (hφ.hom j)
  rw [subst_comp_subst_apply hA hb, subst_comp_subst_apply hS hb] at key
  have e1 : (fun p : Fin 2 × Fin d => MvPowerSeries.subst b (atPt p.1 (φ p.2))) =
      fun p => φa c φ (![u, v] p.1) p.2 := by
    funext ⟨i, k⟩
    simp only [atPt, φa]
    rw [subst_comp_subst_apply (hX i) hb]
    congr 1
    funext ⟨q1, q2⟩
    rw [subst_X hb]
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rfl
  have e2 : (fun q : Fin 1 × Fin (dL Dw) => MvPowerSeries.subst b
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) = actPS (Dw := Dw) (S := S) c (u + v) := by
    funext ⟨q1, q2⟩
    have h1 : q1 = 0 := Subsingleton.elim _ _
    subst h1
    rw [subst_add hb, subst_X hb, subst_X hb]
    exact actPS_add c u v _
  rw [e1, e2] at key
  exact key

theorem act_φa {d : ℕ} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
    {φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S} (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hact : ∀ a j, subst (fun p : Fin 1 × Fin d => φ p.2) (act a j) = subst (actPS (Dw := Dw) c a) (φ j))
    (a u : 𝓞 E) (j : Fin d) :
    subst (fun p : Fin 1 × Fin d => φa c φ u p.2) (act a j) = φa c φ (a * u) j := by
  have hP : HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    hasSubst_of_constantCoeff_zero (fun p => hφ p.2)
  have h := subst_comp_subst_apply hP (hasSubst_actPS (Dw := Dw) (S := S) c u) (act a j)
  rw [hact a j] at h
  exact h.symm.trans (φa_mul c φ a u j)

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG
end
end

