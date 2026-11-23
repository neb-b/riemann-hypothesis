module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhOneValSt

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGJAd
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

attribute [local instance] Over.cartesianMonoidalCategory

section Help

variable {S : Type} [CommRing S] {d n : ℕ}

private theorem subst_rename_lemma {σ τ υ R : Type} [CommRing R] [Finite σ] [Finite τ]
    (a : σ → MvPowerSeries υ R) (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ)
    (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by
  have h1 : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  have h2 : MvPowerSeries.HasSubst (fun t => a (ρ t)) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun t => by rw [ha (ρ t)]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2]
  erw [MvPowerSeries.substAlgHom_coe, MvPowerSeries.substAlgHom_coe, MvPolynomial.aeval_rename]
  rfl

theorem cc_psIn (m : ℕ) (i : Fin n) (g : MvPowerSeries (Fin 1 × Fin d) S) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPolynomial.constantCoeff (psIn d m ![i] g) = 0 := by
  simp only [psIn, MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', hg]

theorem psJet_subst_psIn {ι' : Type} [Fintype ι'] [DecidableEq ι'] (m : ℕ) (i : Fin n)
    (Q : Fin n × Fin d → MvPowerSeries ι' S) (hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0)
    (g : MvPowerSeries (Fin 1 × Fin d) S) :
    psJet m (MvPowerSeries.subst Q ((psIn d m ![i] g : MvPolynomial (Fin n × Fin d) S) : MvPowerSeries (Fin n × Fin d) S)) =
      psJet m (MvPowerSeries.subst (fun p : Fin 1 × Fin d => Q (i, p.2)) g) := by
  simp only [psIn]
  rw [subst_rename_lemma Q hQ, ExpGF.psJet_subst_trunc m _ (fun _ => hQ _) g]
  congr 1
  congr 1
  funext p
  simp

end Help

set_option maxHeartbeats 800000 in
theorem adVal : AdValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ hx hact a' wL hrel m u0 u1 z J hJ
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hφ.const
  obtain ⟨u, hu, hc⟩ := hrel m
  let P : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := ![φa c φ u0, φa c φ u1]
  have hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 u0 j, fun j => const_φa c φ hφ0 u1 j⟩
  let Q : Fin 2 × Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := fun p => P p.1 p.2
  have hQ : ∀ p, MvPowerSeries.constantCoeff (Q p) = 0 := fun p => hP p.1 p.2
  have hQs : MvPowerSeries.HasSubst Q := MvPowerSeries.hasSubst_of_constantCoeff_zero hQ
  have hQ0 : ∀ j, Q ((0 : Fin 2), j) = φa c φ u0 j := fun j => rfl
  have hQ1 : ∀ j, Q ((1 : Fin 2), j) = φa c φ u1 j := fun j => rfl

  have hpt : (ptm C P m).left ≫ (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left =
      (xExp y C φ m).left ≫ (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left := by
    have hPe : (fun k => φa c φ ((![u0, u1] : Fin 2 → 𝓞 E) k)) = P := by
      funext k
      refine Fin.cases rfl (fun k' => ?_) k
      rw [Fin.fin_one_eq_zero k']
      rfl
    have e0 := ptm_jpt C φ hφ0 hx m ![u0, u1] 0
    have e1 := ptm_jpt C φ hφ0 hx m ![u0, u1] 1
    rw [hPe] at e0 e1
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, e0, e1]
    rfl

  let σa : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  let σb : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S := fun p =>
    (![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)] :
      Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2
  have ea0 : ∀ j, σa ((0 : Fin 2), j) = psIn C.d m ![0] (C.B.A.act a' j) := fun j => rfl
  have ea1 : ∀ j, σa ((1 : Fin 2), j) = MvPolynomial.X ((1 : Fin 2), j) := fun j => rfl
  have eb0 : ∀ j, σb ((0 : Fin 2), j) = MvPolynomial.X ((0 : Fin 2), j) := fun j => rfl
  have eb1 : ∀ j, σb ((1 : Fin 2), j) = psIn C.d m ![1] (C.B.A.act (H.bar a') j) := fun j => rfl
  have hσa : ∀ k, MvPolynomial.constantCoeff (σa k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [ea0]; exact cc_psIn m 0 _ (C.B.A.const a' j), fun j => by rw [ea1]; simp⟩
  have hσb : ∀ k, MvPolynomial.constantCoeff (σb k) = 0 := by
    rintro ⟨i, j⟩
    revert j
    revert i
    rw [Fin.forall_fin_two]
    exact ⟨fun j => by rw [eb0]; simp, fun j => by rw [eb1]; exact cc_psIn m 1 _ (C.B.A.const (H.bar a') j)⟩
  have hcc : ∀ (σ : Fin 2 × Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S), (∀ k, MvPolynomial.constantCoeff (σ k) = 0) →
      ∀ i j, MvPowerSeries.constantCoeff (MvPowerSeries.subst Q ((σ (i, j) : MvPolynomial _ S) :
        MvPowerSeries (Fin 2 × Fin C.d) S)) = 0 := by
    intro σ hσ i j
    refine const_substPS Q hQ _ ?_
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    exact hσ (i, j)
  have hPa : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ (a' * u0), φa c φ u1] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hPb : ∀ i j, MvPowerSeries.constantCoeff
      ((![φa c φ u0, φa c φ (H.bar a' * u1)] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
    rw [Fin.forall_fin_two]
    exact ⟨fun j => const_φa c φ hφ0 _ j, fun j => const_φa c φ hφ0 _ j⟩
  have hma : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left = (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σa hσa]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σa hσa) hPa m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [ea0, psJet_subst_psIn m 0 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact a' u0 j)
    · rw [ea1, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ1]
      rfl
  have hmb : (ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left =
      (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left := by
    rw [← Over.comp_left, ptm_subst C P hP m σb hσb]
    refine congrArg Over.Hom.left (ptm_congr C (hcc σb hσb) hPb m ?_)
    rw [Fin.forall_fin_two]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [eb0, MvPolynomial.coe_X, MvPowerSeries.subst_X hQs, hQ0]
      rfl
    · rw [eb1, psJet_subst_psIn m 1 Q hQ]
      exact congrArg (psJet m) (act_φa c hφ0 hact (H.bar a') u1 j)
  have va : val (pe y C.d C.x C.e m ![fun j => psIn C.d m ![0] (C.B.A.act a' j), fun j => MvPolynomial.X ((1 : Fin 2), j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ (a' * u0), φa c φ u1] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σa)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hma)
  have vb : val (pe y C.d C.x C.e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a') j)])
      (ptm C P m).left z J = val (C.e m) (ptm C ![φa c φ u0, φa c φ (H.bar a' * u1)] m).left z J :=
    (show _ = val (C.e m) ((ptm C P m).left ≫ (homAt y.x (jetSubstP m σb)).left) z J from val_pull hJ _ _ _).trans
      (congrArg (fun r => val (C.e m) r z J) hmb)
  have vw : val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y C.d C.x m (0 : Fin 2)) (jpt y C.d C.x m (1 : Fin 2))).left)
      (ptm C P m).left z J =
      val (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1)).left)
        (xExp y C φ m).left z J := by
    rw [val_pull hJ, val_pull hJ, hpt]
  have hg : gm (ptm C P m).left z ⊤ (unitΓ u) =
      gm (𝟙 _) z ⊤ (unitΓ (Units.map (jetSubstPS (m := m) Q).toMonoidHom u)) :=
    ExpGI.gm_homAt _ z u
  have h1 := val_corr hJ hc (ptm C P m).left
  rw [val_mul hJ, ExpGD.val_scale' _ _ _ _ _ z J hJ, va, vb, vw, hg] at h1
  refine ⟨Units.map (jetSubstPS (m := m) Q).toMonoidHom u, ?_, ?_⟩
  · show jetSubstPS (m := m) Q (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (atP P (C.B.ad a'))
    rw [hu, jetSubstPS_psJet m Q hQ]
    rfl
  · rw [← _root_.mul_assoc, eq_mul_inv_iff_mul_eq]
    exact h1

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJ
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpSActPS
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem expS_actPS {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (g : MvPowerSeries (Fin 1 × Fin d) S)
    (hg : MvPowerSeries.constantCoeff g = 0) (k : 𝓞 E) :
    MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (Germ.FB.expS S (-(compL φ g))) =
      Germ.FB.expS S (-(compL (φa c φ k) g)) := by
  have hb : MvPowerSeries.HasSubst (actPS (Dw := Dw) (S := S) c k) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by simp [actPS]
  have ha : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => φ p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => hφ p.2
  have h0 : MvPowerSeries.constantCoeff (-(compL φ g)) = 0 := by
    rw [map_neg, ExpGB.const_compL φ hφ g, hg, neg_zero]
  have hcomp : MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c k) (-(compL φ g)) =
      -(compL (φa c φ k) g) := by
    rw [← MvPowerSeries.coe_substAlgHom hb, map_neg, MvPowerSeries.coe_substAlgHom hb]
    unfold compL φa
    rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  unfold Germ.FB.expS PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0).const hb]
  simp only [hcomp]

theorem val_e (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hact : ∀ a j, MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j))
    (τ : ∀ m, LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)))
    (u : ∀ m, (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ)
    (hτc : ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (τ m) (eL y C.d C.x C.B.A.act C.e C.wP m))
    (m : ℕ) (z : (jO y (dL Dw) m 1).left)
    (J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι) (hJ : Good Xo.univ.t.PP.L z J) :
    val (ExpGA.eG C φ τ u m) (𝟙 _) z J =
      gm (𝟙 _) z ⊤ (unitΓ (u m)) *
        (val C.wP ((ptm C ![φ] m).left ≫ (C.x m).left) z J *
          val (C.e m) (ptm C ![φ, φa c φ H.w0] m).left z J) := by
  have hX : actP (Dw := Dw) (S := S) c 1 = fun p => MvPolynomial.X p := by
    funext p
    simp [actP]
  have hid : jetSubstP m (actP (Dw := Dw) (S := S) c 1) = AlgHom.id S _ := by
    rw [hX]
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp [jetSubstP, jetMap, liftJet, Ideal.Quotient.lift_mk] <;> rfl
  have hP : actPS (Dw := Dw) (S := S) c 1 = MvPowerSeries.X := by
    funext q
    simp [actPS]
  have hφ1 : φa c φ 1 = φ := by
    funext j
    simp only [φa, hP]
    exact congrFun MvPowerSeries.subst_self (φ j)
  have hu : Units.map (AlgHom.id S (Jet S (Fin 1 × Fin (dL Dw)) m)).toMonoidHom (u m) = u m :=
    Units.ext rfl
  have h1 := val_eAt C φ hφ hact τ u hτc m 1 z J hJ
  rw [hφ1, _root_.mul_one] at h1
  unfold eAt at h1
  rw [val_pull, hid, homAt_id, Over.id_left, Category.comp_id, hu] at h1
  exact h1
  exact hJ

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGK
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.SubstCoeRename
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
  Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGI

attribute [local instance] Over.cartesianMonoidalCategory

theorem subst_coe_rename {σ τ υ : Type} {R : Type} [CommRing R] [Finite σ] [Finite τ] (a : σ → MvPowerSeries υ R)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ρ : τ → σ) (q : MvPolynomial τ R) :
    MvPowerSeries.subst a ((MvPolynomial.rename ρ q : MvPolynomial σ R) : MvPowerSeries σ R) =
      MvPowerSeries.subst (fun t => a (ρ t)) (q : MvPowerSeries τ R) := by
  have h1 : MvPowerSeries.HasSubst a := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
  have h2 : MvPowerSeries.HasSubst (fun t => a (ρ t)) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => ha (ρ t))
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [(fun t => ha (ρ t)) s]; exact IsNilpotent.zero)
  rw [← MvPowerSeries.coe_substAlgHom h1, ← MvPowerSeries.coe_substAlgHom h2]
  erw [MvPowerSeries.substAlgHom_coe, MvPowerSeries.substAlgHom_coe, MvPolynomial.aeval_rename]
  rfl

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

theorem val_pe_pair (C : ChartAt Xo c y) (m : ℕ) (P3 : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP3c : ∀ i j, MvPowerSeries.constantCoeff (P3 i j) = 0)
    (σ : Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) (hσ : ∀ i j, MvPolynomial.constantCoeff (σ i j) = 0)
    (Q : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hQ : ∀ i j, MvPowerSeries.constantCoeff (Q i j) = 0)
    (hs : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
      ((σ i j : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) = psJet m (Q i j))
    {z : (jO y (dL Dw) m 1).left} {J : ((jO y (dL Dw) m 1).left ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι}
    (hJ : Good Xo.univ.t.PP.L z J) :
    val (pe y C.d C.x C.e m σ) (ptm C P3 m).left z J = val (C.e m) (ptm C Q m).left z J := by
  refine (show val (pe y C.d C.x C.e m σ) (ptm C P3 m).left z J = val (C.e m)
      ((ptm C P3 m).left ≫ (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d => σ p.1 p.2)).left) z J from
    val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, ptm_subst C P3 hP3c m (fun p : Fin 2 × Fin C.d => σ p.1 p.2) (fun p => hσ p.1 p.2)]
  rw [ptm_congr C (fun i j => const_substPS (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2) _ (by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]; exact hσ i j)) hQ m hs]

end Pair

set_option maxHeartbeats 1000000 in
theorem phOneVal_holds : ExpGJ.PhOneValSt := by
  intro E _ _ _ H Dw l Xo c _ S _ _ _ y C φ hφ hx m u0 u1 u2 z J hJ
  have hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0 := hφ.const
  set us : Fin 3 → 𝓞 E := ![u0, u1, u2] with hus
  set P3 : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S := fun k => φa c φ (us k) with hP3
  have hP3c : ∀ i j, MvPowerSeries.constantCoeff (P3 i j) = 0 := fun i j => const_φa c φ hφ0 (us i) j
  have hP3e : (![φa c φ u0, φa c φ u1, φa c φ u2] : Fin 3 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) = P3 := by
    refine funext fun k => ?_
    fin_cases k <;> rfl
  refine (C.frame.ph1 m).elim fun u huc => ?_
  have hu := huc.1
  have hcorr := huc.2
  refine ⟨Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)).toMonoidHom u, ?_, ?_⟩
  · show jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (u : Jet S (Fin 3 × Fin C.d) m) = _
    rw [hu, jetSubstPS_psJet m (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2), hP3e]
    rfl
  · have hv := val_corr hJ hcorr (ptm C P3 m).left

    have hmor : ptm C P3 m ≫ lift (jpt y C.d C.x m (0 : Fin 3)) (lift (jpt y C.d C.x m (1 : Fin 3)) (jpt y C.d C.x m (2 : Fin 3))) =
        xExp y C φ m ≫ lift (Xo.univ.t.act.act u0) (lift (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2)) := by
      rw [comp_lift, comp_lift, comp_lift, comp_lift, ptm_jpt C φ hφ0 hx m us 0, ptm_jpt C φ hφ0 hx m us 1,
        ptm_jpt C φ hφ0 hx m us 2]
      rfl
    have hL : val (ExpGC.cubAt (Xo.univ.t.act.act u0) (Xo.univ.t.act.act u1) (Xo.univ.t.act.act u2))
        (xExp y C φ m).left z J =
        val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
          (lift (jpt y C.d C.x m (0 : Fin 3)) (lift (jpt y C.d C.x m (1 : Fin 3)) (jpt y C.d C.x m (2 : Fin 3)))).left)
          (ptm C P3 m).left z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [← Over.comp_left, ← Over.comp_left, hmor]
    rw [hL, hv]

    rw [ExpGD.val_scale' _ _ _ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_inv]
    have hg : gm (ptm C P3 m).left z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤
        (unitΓ (Units.map (jetSubstPS (m := m) (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)).toMonoidHom u)) :=
      gm_homAt _ z u
    rw [hg]
    have hX : ∀ (b : Fin 3) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin C.d) S) : MvPowerSeries (Fin 3 × Fin C.d) S) = P3 b j := by
      intro b j
      rw [MvPolynomial.coe_X, MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero
        (fun p : Fin 3 × Fin C.d => hP3c p.1 p.2))]
    have hF : ∀ j : Fin C.d, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m (φa c φ (u0 + u1) j) := by
      intro j
      unfold psIn
      rw [subst_coe_rename (fun p : Fin 3 × Fin C.d => P3 p.1 p.2) (fun p => hP3c p.1 p.2)]
      beta_reduce
      rw [psJet_subst_trunc m (fun t : Fin 2 × Fin C.d => P3 ((![0, 1] : Fin 2 → Fin 3) t.1) t.2)
        (fun t => hP3c _ t.2), ← law_φa c hφ u0 u1 j]
      congr 2
      funext p
      obtain ⟨b, i⟩ := p
      fin_cases b <;> rfl
    have hcX : ∀ (b : Fin 3) (j : Fin C.d), MvPolynomial.constantCoeff (MvPolynomial.X (b, j) : MvPolynomial (Fin 3 × Fin C.d) S) = 0 :=
      fun b j => by simp
    have hcF : ∀ j : Fin C.d, MvPolynomial.constantCoeff (psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j)) = 0 := by
      intro j
      unfold psIn
      rw [MvPolynomial.constantCoeff_rename, ExpGB.cc_psTrunc', C.B.G.const]
    have hsA : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ (u0 + u1), φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · simpa using hF j
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hsB : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ u0, φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((0 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u0 j)
        rw [hX]
        rfl
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hsC : ∀ i j, psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
        ((((![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) i j : MvPolynomial _ S)) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
        psJet m ((![φa c φ u1, φa c φ u2] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) := by
      intro i j
      fin_cases i
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((1 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u1 j)
        rw [hX]
        rfl
      · show psJet m (MvPowerSeries.subst (fun p : Fin 3 × Fin C.d => P3 p.1 p.2)
          ((MvPolynomial.X ((2 : Fin 3), j) : MvPolynomial _ S) : MvPowerSeries (Fin 3 × Fin C.d) S)) =
          psJet m (φa c φ u2 j)
        rw [hX]
        rfl
    have hQc : ∀ (a b : 𝓞 E) (i : Fin 2) (j : Fin C.d), MvPowerSeries.constantCoeff
        ((![φa c φ a, φa c φ b] : Fin 2 → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) i j) = 0 := by
      intro a b i j
      fin_cases i
      · exact const_φa c φ hφ0 a j
      · exact const_φa c φ hφ0 b j
    rw [val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcF j, hcX 2 j]) _ (hQc _ _) hsA hJ,
      val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcX 0 j, hcX 2 j]) _ (hQc _ _) hsB hJ,
      val_pe_pair C m P3 hP3c _ (fun i j => by fin_cases i; exacts [hcX 1 j, hcX 2 j]) _ (hQc _ _) hsC hJ,
      _root_.mul_assoc]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGJPh1
end
end

