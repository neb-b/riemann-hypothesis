module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldStatementPf
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

theorem densF_meas {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) : Measurable fun w => ENNReal.ofReal (densF X x w) := by
  have hm : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ :=
    fun τ i => (OntoB.cd_dmin (X := X) (x0 := x) (τ := τ) (i := i.castSucc)).continuous.norm.measurable
  have hf : ∀ (τ : X.Ψ) (i : Fin r), Measurable fun w => ‖dmin X.Gm (cpt X x w) τ i.castSucc‖ ^ (-2 : ℤ) := by
    intro τ i
    simp only [zpow_neg, zpow_ofNat]
    exact ((hm τ i).pow_const 2).inv
  have hp : Measurable fun w => densF X x w := by
    unfold densF
    exact Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => hf τ i
  exact ENNReal.measurable_ofReal.comp hp

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := by
  intro r X x0 ho hPD FF hFF x1 hx1
  classical
  obtain ⟨x1', ho', b1, hb1, rfl⟩ := ortho_holds r X x1 hx1
  obtain ⟨D⟩ := ExtFPf.luData_of hLU X x1' ho'
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  obtain ⟨ρ1, hρ1, hball1⟩ := exists_ball X b1 D ho' hb1
  obtain ⟨ρ2, hρ2, hball2⟩ := Metric.isOpen_iff.mp (ExF.isOpen_OmF X x1') 0 (IW.zero_mem_OmF X x1' ho')
  set ρ0 : ℝ := min ρ1 ρ2 / 2 with hρ0def
  have hρ0 : 0 < ρ0 := by positivity
  have hρ01 : ρ0 < ρ1 := by have := min_le_left ρ1 ρ2; linarith
  have hρ02 : ρ0 < ρ2 := by have := min_le_right ρ1 ρ2; linarith
  have hcl : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D := fun z hz =>
    hball1 z (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ01))
  have hclO : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ OmF X x1' := fun z hz =>
    hball2 (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hρ02))
  obtain ⟨Kj, hKj⟩ := jac_bound X b1 D hcl
  obtain ⟨Kd, hKd⟩ := dens_bound X b1 D hcl
  refine ⟨ρ0, hρ0, fun ρ hρ hρle => ?_⟩
  have hbcl : Metric.ball (0 : V (nd X)) ρ ⊆ Metric.closedBall 0 ρ0 := fun z hz =>
    Metric.ball_subset_closedBall (Metric.ball_subset_ball hρle hz)
  have hbU : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D := hbcl.trans hcl
  have hbO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1' := hbcl.trans hclO
  have hopen := isOpen_sat D ho' hb1 hbO
  refine ⟨hopen, ENNReal.ofReal (max Kd 0 * max Kj 0), ENNReal.ofReal_lt_top, fun G hG hGB hGΓ => ?_⟩
  set x1 := rmul x1' b1 with hx1def
  set T := Tset X x1 ρ with hTdef
  have hT : MeasurableSet T := meas_Tset X b1 D ho' hbU hx1
  have hTeq : T = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := Tset_eq X b1 D hbU
  have hTB : ∀ y b, b ∈ Bor X.Ψ r → (rmul y b ∈ T ↔ y ∈ T) := fun y b hb => by
    rw [hTeq]; exact KU.rmul_mem_S X hb
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1').measurable
  have hae0 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  set Sat : Set (V (nd X)) := {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
    cpt X x0 z = lact γ (rmul (cpt X x1 z') b)} with hSatdef
  have hSat : MeasurableSet Sat := (hopen.preimage (KU.cont_cpt X x0)).measurableSet

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * T.indicator 1 (lact γ.1⁻¹ y) * G y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    ((measurable_one.indicator hS).mul ((measurable_one.indicator hT).comp (KU.cont_lact X γ.1⁻¹).measurable)).mul hG
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x hx b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : lact γ.1⁻¹ (rmul x b) ∈ T ↔ lact γ.1⁻¹ x ∈ T := by rw [KU.lact_rmul']; exact hTB _ _ hb
    simp only [H, Set.indicator_apply, e1, e2, hGB x hx b hb, Pi.one_apply]

  have stepA : ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0 ≤ ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine le_trans (setLIntegral_mono' (hFF.1.inter hSat) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
    obtain ⟨hzF, γ, hγ, b, hb, z', hz', he⟩ := hz
    have hT1 : lact γ⁻¹ (cpt X x0 z) ∈ T := by
      rw [he, KU.lact_lact, inv_mul_cancel, KU.lact_one]
      exact ⟨⟨z', b⟩, ⟨hz', hb⟩, rfl⟩
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    simp only [H, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hzF), Set.indicator_of_mem hT1,
      Pi.one_apply, one_mul]
  have stepB : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have stepC : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, (KU.Sset X x0 FF).indicator 1
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x0) ho (KU.isOrth_lact X γ.2 ho) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr_ae (hae0.mono fun z hz => ?_)
    show H γ (cpt X (lact γ.1 x0) z) = _
    rw [KU.cpt_lact]
    simp only [H, KU.lact_lact, inv_mul_cancel, KU.lact_one, hGΓ γ.1 γ.2 _ hz]
    ring
  have hIm : ∀ γ : X.Γ, Measurable fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x0 z)) * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x0)).measurable).mul
      (((measurable_one.indicator hT).comp hcpt0).mul (hG.comp hcpt0))
  have stepD : ∑' γ : X.Γ, ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (lact γ.1 (cpt X x0 z)) *
      (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) ∂muF X x0 ≤
      ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hIm γ).aemeasurable]
    refine lintegral_mono fun z => ?_
    rw [ENNReal.tsum_mul_right]
    calc (∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x0 z))) *
          (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z))
        ≤ 1 * (T.indicator 1 (cpt X x0 z) * G (cpt X x0 z)) := by
          gcongr; exact FSM.atMostOnce X ho hFF _
      _ = _ := one_mul _
  have hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, (fun y => T.indicator (1 : Frame X.Ψ r → ℝ≥0∞) y * G y) (rmul x b) =
      (fun y => T.indicator 1 y * G y) x := by
    intro x hx b hb
    simp only [Set.indicator_apply, hTB x b hb, hGB x hx b hb, Pi.one_apply]
  have stepE : ∫⁻ z, T.indicator 1 (cpt X x0 z) * G (cpt X x0 z) ∂muF X x0 =
      ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' :=
    hM r X x0 x1' ho ho' (fun y => T.indicator 1 y * G y) ((measurable_one.indicator hT).mul hG) hφB
  have hA : MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := meas_image X b1 D hbU hx1
  have stepF : ∫⁻ w, T.indicator 1 (cpt X x1' w) * G (cpt X x1' w) ∂muF X x1' =
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' := by
    rw [← lintegral_indicator hA]
    refine lintegral_congr fun w => ?_
    have e : cpt X x1' w ∈ T ↔ w ∈ Φ X b1 D '' Metric.ball 0 ρ := by rw [hTeq]; exact KU.cpt_mem_S X ho' w
    by_cases hw : w ∈ Φ X b1 D '' Metric.ball 0 ρ
    · rw [Set.indicator_of_mem (e.mpr hw), Set.indicator_of_mem hw, Pi.one_apply, one_mul]
    · rw [Set.indicator_of_notMem (fun h => hw (e.mp h)), Set.indicator_of_notMem hw, zero_mul]
  have stepG : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, G (cpt X x1' w) ∂muF X x1' ≤
      ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) := by
    unfold muF
    rw [restrict_withDensity hA]
    refine (lintegral_withDensity_le_lintegral_mul _ (densF_meas X x1') _).trans ?_
    refine lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self) (fun w => le_rfl)
  have hder : ∀ z ∈ Metric.ball (0 : V (nd X)) ρ,
      HasFDerivWithinAt (Φ X b1 D) (fderiv ℝ (Φ X b1 D) z) (Metric.ball 0 ρ) z := fun z hz =>
    ((((Φ_diffOn X b1 D) z (hbU hz)).differentiableAt ((isOpen_Uc X b1 D).mem_nhds (hbU hz))).restrictScalars ℝ
      ).hasFDerivAt.hasFDerivWithinAt
  have stepH : ∫⁻ w in Φ X b1 D '' Metric.ball 0 ρ, ENNReal.ofReal (densF X x1' w) * G (cpt X x1' w) =
      ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) :=
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hder
      ((Φ_injOn X b1 D hx1).mono hbU) _
  have stepI : ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ (Φ X b1 D) z).det| *
        (ENNReal.ofReal (densF X x1' (Φ X b1 D z)) * G (cpt X x1' (Φ X b1 D z))) ≤
      ENNReal.ofReal (max Kd 0 * max Kj 0) * ∫⁻ z in Metric.ball 0 ρ, G (cpt X x1 z) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨hΦO, hβ, e⟩ := split X b1 D (hbU hz)
    have hG1 : G (cpt X x1' (Φ X b1 D z)) = G (cpt X x1 z) := by
      rw [e, hGB _ (by exact hΦO) _ hβ]
    rw [hG1, ← mul_assoc]
    gcongr
    rw [ENNReal.ofReal_mul (le_max_right _ _), mul_comm]
    gcongr
    · exact (hKd z (hbcl hz)).trans (le_max_left _ _)
    · exact (hKj z (hbcl hz)).trans (le_max_left _ _)
  calc ∫⁻ z in FF ∩ Sat, G (cpt X x0 z) ∂muF X x0
      ≤ _ := stepA
    _ = _ := stepB
    _ = _ := tsum_congr stepC
    _ ≤ _ := stepD
    _ = _ := stepE
    _ = _ := stepF
    _ ≤ _ := stepG
    _ = _ := stepH
    _ ≤ _ := stepI

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem localUnfoldB_of {E : Type} [Field E] [NumberField E] [IsCMField E] (hLU : LUStatement (E := E)) :
    LocalUnfoldBStatement (E := E) := LUB.localUnfoldB_of hLU

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfI
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

theorem sq_add_le (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem lint_add_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℂ} {k : α → ℝ}
    (hk : ∀ x, 0 < k x) {om : α → ℝ≥0∞}
    (ha : AEMeasurable (fun x => ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) μ) :
    ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
  calc ∫⁻ x, ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x ∂μ
      ≤ ∫⁻ x, (2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
          2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x)) ∂μ := by
        refine lintegral_mono fun x => ?_
        have hk' := hk x
        have hA : 0 ≤ ‖a x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have hB : 0 ≤ ‖b x‖ ^ 2 / k x := div_nonneg (sq_nonneg _) hk'.le
        have h1 : ‖a x + b x‖ ^ 2 / k x ≤ 2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x) := by
          rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
          exact div_le_div_of_nonneg_right (sq_add_le _ _) hk'.le
        calc ENNReal.ofReal (‖a x + b x‖ ^ 2 / k x) * om x
            ≤ ENNReal.ofReal (2 * (‖a x‖ ^ 2 / k x) + 2 * (‖b x‖ ^ 2 / k x)) * om x := by
              gcongr
          _ = 2 * (ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x) +
                2 * (ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x) := by
              rw [ENNReal.ofReal_add (mul_nonneg zero_le_two hA) (mul_nonneg zero_le_two hB),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2),
                ENNReal.ofReal_mul (zero_le_two : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
              ring
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2 / k x) * om x ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖b x‖ ^ 2 / k x) * om x ∂μ := by
        rw [lintegral_add_left' (ha.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

theorem pnorm_sub_le (la : Wt X.Ψ r) (f g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (fun y => f y - g y) x ≤ X.pnorm la f x + X.pnorm la g x := by
  unfold Data.pnorm
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _)
    (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)

theorem bdd_sub {la : Wt X.Ψ r} {f g : Frame X.Ψ r → ℂ} (hf : X.IsBddSec la f) (hg : X.IsBddSec la g) :
    X.IsBddSec la (fun y => f y - g y) := by
  obtain ⟨hf1, C1, hC1⟩ := hf
  obtain ⟨hg1, C2, hC2⟩ := hg
  refine ⟨?_, C1 + C2, fun x hx => (pnorm_sub_le X la f g x).trans (add_le_add (hC1 x hx) (hC2 x hx))⟩
  unfold Data.IsSec at hf1 hg1 ⊢
  obtain ⟨hd1, hb1, hl1⟩ := hf1
  obtain ⟨hd2, hb2, hl2⟩ := hg1
  refine ⟨hd1.sub hd2, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hb1 x hx b hb, hb2 x hx b hb]
    ring
  · simp only [hl1 γ hγ x hx, hl2 γ hγ x hx]
    ring

theorem poin_add (la : Wt X.Ψ r) {P1 P2 : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (h1 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P1 (lact γ.1 x)‖)
    (h2 : Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P2 (lact γ.1 x)‖) :
    poin X la (fun y => P1 y + P2 y) x = poin X la P1 x + poin X la P2 x := by
  unfold poin
  rw [← Summable.tsum_add h1.of_norm h2.of_norm]
  congr 1
  funext γ
  ring

theorem poin_smul (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    poin X la (fun y => a * P y) x = a * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  congr 1
  funext γ
  ring

theorem poin_zero (la : Wt X.Ψ r) (x : Frame X.Ψ r) : poin X la (fun _ => 0) x = 0 := by
  simp [poin]

variable (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))

def nuF : Measure (V (nd X)) :=
  ((muF X x0).restrict FF).withDensity fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal

variable {X x0 W FF}

private lemma measurable_cpt : Measurable (cpt X x0) := by
  refine Measurable.of_eval fun τ => Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [cpt, rmul, mat, nmat, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs
  · refine Measurable.const_mul ?_ _
    first
      | exact measurable_pi_apply _
      | exact (EuclideanSpace.proj _).continuous.measurable
      | fun_prop
  · exact measurable_const
  · exact measurable_const

theorem dens_meas (hW : Measurable W) :
    Measurable fun z => ENNReal.ofReal (W (cpt X x0 z)).toReal :=
  (hW.comp measurable_cpt).ennreal_toReal.ennreal_ofReal

theorem nuF_ac : nuF X x0 W FF ≪ muF X x0 := by
  unfold nuF
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

private lemma measurableSet_dom' : MeasurableSet X.dom := by
  have hc : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hd : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := fun τ =>
    Continuous.matrix_det (A := fun x : Frame X.Ψ r => mat x τ) (continuous_apply τ)
  have ho : IsOpen X.dom := by
    show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.setOf_forall, Set.setOf_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hd τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i =>
        isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hc τ i))))
  exact ho.measurableSet

theorem memLp_of (hW : Measurable W) {h : Frame X.Ψ r → ℂ} (hh : ContinuousOn h X.dom)
    (hF : InFF X x0 W FF h) : MemLp (fun z => h (cpt X x0 z)) 2 (nuF X x0 W FF) := by
  classical
  unfold InFF at hF
  have hOm : MeasurableSet (OmF X x0) := measurable_cpt measurableSet_dom'
  have hae : ∀ᵐ z ∂nuF X x0 W FF, z ∈ OmF X x0 := by
    have h1 : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := by
      unfold muF
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hOm)
    exact nuF_ac.ae_le h1
  have hg : Measurable (X.dom.piecewise h 0) :=
    ContinuousOn.measurable_piecewise hh continuous_const.continuousOn measurableSet_dom'
  have hm : AEStronglyMeasurable (fun z => h (cpt X x0 z)) (nuF X x0 W FF) := by
    have hm0 : Measurable fun z => X.dom.piecewise h 0 (cpt X x0 z) := hg.comp measurable_cpt
    refine hm0.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z hz
    exact Set.piecewise_eq_of_mem _ _ _ hz
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by
    simp only [Pi.zero_apply]
    positivity)]
  refine lt_of_le_of_lt ?_ hF
  unfold nuF
  refine (lintegral_withDensity_le_lintegral_mul _ (dens_meas hW) _).trans (lintegral_mono fun z => ?_)
  simp only [Pi.mul_apply]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le

theorem integral_nu (hW : Measurable W) (g : V (nd X) → ℂ) :
    ∫ z, g z ∂nuF X x0 W FF = ∫ z in FF, g z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  unfold nuF
  rw [integral_withDensity_eq_integral_toReal_smul (dens_meas hW)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, Complex.real_smul, mul_comm]

theorem inner_toLp (hW : Measurable W) {a b : V (nd X) → ℂ} (ha : MemLp a 2 (nuF X x0 W FF))
    (hb : MemLp b 2 (nuF X x0 W FF)) :
    ⟪ha.toLp a, hb.toLp b⟫_ℂ = ∫ z in FF, conj (a z) * b z * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 := by
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ z ∂nuF X x0 W FF, ⟪(ha.toLp a) z, (hb.toLp b) z⟫_ℂ = conj (a z) * b z := by
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply] <;> ring
  rw [integral_congr_ae h, integral_nu hW]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI
end

