module

public import Development.WeilBound.CoreStatements.CentralCharts.TraceMulReNonneg
public import Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogNorm
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPunctured
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CentralCharts.AnalyticAtDet
section
noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm Filter Topology Matrix
open scoped ComplexOrder MatrixOrder

variable {n k r : ℕ}

theorem posDef_ofReal {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.PosDef) : (Y.map Complex.ofReal).PosDef := by
  have h0 : 0 ≤ Y := hY.posSemidef.nonneg
  have h1 : (CFC.sqrt Y).PosSemidef := (CFC.sqrt_nonneg Y).posSemidef
  have h2 : Y = (CFC.sqrt Y)ᴴ * CFC.sqrt Y := by rw [h1.1.eq, CFC.sqrt_mul_sqrt_self Y h0]
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin k) (Fin k) ℝ, Y = Sᴴ * S := ⟨_, h2⟩
  have h3 : Y.map Complex.ofReal = (S.map Complex.ofReal)ᴴ * S.map Complex.ofReal := by
    rw [hS]
    ext i j
    simp [Matrix.mul_apply, ← Complex.ofReal_sum, ← Complex.ofReal_mul]
  have h4 : (Y.map Complex.ofReal).PosSemidef := by rw [h3]; exact posSemidef_conjTranspose_mul_self _
  refine h4.posDef_iff_det_ne_zero.2 ?_
  have h5 := Complex.ofRealHom.map_det Y
  rw [RingHom.mapMatrix_apply] at h5
  have h6 : (Y.map Complex.ofReal).det = (Y.det : ℂ) := h5.symm
  rw [h6]
  exact_mod_cast hY.det_pos.ne'

theorem analyticAt_det {m : ℕ} {A : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) : AnalyticAt ℂ (fun u => (A u).det) t := by
  simp only [det_apply']
  exact Finset.analyticAt_fun_sum _ fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => h _ _)

theorem analyticAt_inv {A : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {t : Fin n → ℂ}
    (h : ∀ p q, AnalyticAt ℂ (fun u => A u p q) t) (h0 : (A t).det ≠ 0) (p q : Fin k) :
    AnalyticAt ℂ (fun u => (A u)⁻¹ p q) t := by
  simp only [inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, adjugate_apply]
  refine ((analyticAt_det h).inv h0).mul (analyticAt_det fun i j => ?_)
  simp only [updateRow_apply]
  split_ifs
  · exact analyticAt_const
  · exact h _ _

theorem psh_core {τ : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ} {V : (Fin n → ℂ) → Matrix (Fin r) (Fin k) ℂ}
    {f : (Fin n → ℂ) → ℝ} (d : ℝ) (hτ : ∀ p q, AnalyticAt ℂ (fun u => τ u p q) 0)
    (hV : ∀ p q, AnalyticAt ℂ (fun u => V u p q) 0) (hV0 : Function.Injective (V 0).vecMul)
    (hpos : ∀ᶠ u in 𝓝 0, ((τ u).map Complex.im).PosDef) (hf : ContDiffAt ℝ 2 f 0)
    (he : ∀ᶠ u in 𝓝 0, (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).PosDef →
      f u = d + Real.log (V u * (((τ u).map Complex.im).map Complex.ofReal)⁻¹ * (V u)ᴴ).det.re) : PshAt0 f := by
  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ,
      ∀ u, Y u = ((τ u).map Complex.im).map Complex.ofReal := ⟨_, fun _ => rfl⟩
  simp only [← hY] at he
  have hYp : ∀ᶠ u in 𝓝 0, (Y u).PosDef := hpos.mono fun u hu => by rw [hY]; exact posDef_ofReal hu
  have hY0 := hYp.self_of_nhds
  have huY : IsUnit (Y 0).det := IsUnit.mk0 _ hY0.det_pos.ne'
  obtain ⟨C, hC⟩ : ∃ C, C = (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = V 0 * (Y 0)⁻¹ * (V 0)ᴴ := ⟨_, rfl⟩
  have hGp : G.PosDef := by rw [hG]; exact hY0.inv.mul_mul_conjTranspose_same hV0
  have huG : IsUnit G.det := IsUnit.mk0 _ hGp.det_pos.ne'
  have hVC : V 0 * C = G := by rw [hC, hG, Matrix.mul_assoc]
  have hM0 : Cᴴ * Y 0 * C = G := by
    rw [hC, hG, conjTranspose_mul, conjTranspose_conjTranspose, hY0.inv.1.eq]
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ huY]
  have hCi : Function.Injective C.mulVec := by
    have h1 : Function.Injective G.mulVec :=
      Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 huG)
    intro x y hxy
    apply h1
    rw [← hVC, ← mulVec_mulVec, ← mulVec_mulVec, hxy]
  have hF : AnalyticAt ℂ (fun u => (V u * C).det) 0 := analyticAt_det fun p q => by
    simp only [Matrix.mul_apply]
    exact Finset.analyticAt_fun_sum _ fun i _ => (hV _ _).mul analyticAt_const
  have hF0 : (V 0 * C).det ≠ 0 := by rw [hVC]; exact huG.ne_zero
  obtain ⟨Km, hK⟩ : ∃ Km, Km = C * G⁻¹ * Cᴴ := ⟨_, rfl⟩
  have hT : AnalyticAt ℂ (fun u => ∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)) 0 :=
    Finset.analyticAt_fun_sum _ fun p _ => Finset.analyticAt_fun_sum _ fun q _ =>
      analyticAt_const.mul (analyticAt_const.mul (hτ _ _))
  have htr : ∀ u, (∑ p, ∑ q, ((Km p q).re : ℂ) * (Complex.I * τ u q p)).re = -(G⁻¹ * (Cᴴ * Y u * C)).trace.re := by
    intro u
    have e : (G⁻¹ * (Cᴴ * Y u * C)).trace = (Km * Y u).trace := by
      rw [hK, ← Matrix.mul_assoc, trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [e, hY]
    simp [trace, Matrix.mul_apply, Complex.re_sum]
  have hg := padd (plog_norm 2 (d - Real.log G.det.re + r) hF hF0) (pre hT)
  refine ptouch hf hg ?_ ?_
  · rw [he.self_of_nhds (hG ▸ hGp), htr, hM0, hVC, ← hG, nonsing_inv_mul _ huG, trace_one]
    have : ‖G.det‖ = G.det.re := by
      rw [det_eq_re hGp, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg (det_re_pos hGp).le]
    rw [this]
    simp
    ring
  · filter_upwards [he, hYp, hF.continuousAt.eventually_ne hF0] with u h1 h2 h3
    have hN : Cᴴ * (V u)ᴴ = (V u * C)ᴴ := (conjTranspose_mul _ _).symm
    have hVi : Function.Injective (V u).vecMul := by
      have h4 : Function.Injective (V u * C).vecMul :=
        Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ h3))
      intro x y hxy
      apply h4
      have hxy' : x ᵥ* V u = y ᵥ* V u := hxy
      show x ᵥ* (V u * C) = y ᵥ* (V u * C)
      rw [← vecMul_vecMul, ← vecMul_vecMul, hxy']
    have hGu := h2.inv.mul_mul_conjTranspose_same hVi
    have hM := h2.conjTranspose_mul_mul_same hCi
    have a1 := logdet_dual_ge h2 (V u)ᴴ C hM (by rwa [conjTranspose_conjTranspose])
      (by rw [hN, det_conjTranspose]; exact star_ne_zero.2 h3)
    rw [hN, det_conjTranspose, norm_star, conjTranspose_conjTranspose] at a1
    have a2 := logdet_le hM hGp
    rw [h1 hGu, htr]
    linarith

end AnalyticReference.An.H
end
end

-- bundled from Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogdet
section
noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm GlobalTheory.CompanionTheory.Ar Filter Topology Matrix
open scoped ComplexOrder

theorem contDiffAt_logdet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ} {m : WithTop ℕ∞}
    {Γ : E → Matrix (Fin r) (Fin r) ℂ} {t : E} (h : ∀ p q, ContDiffAt ℝ m (fun u => Γ u p q) t) (hp : (Γ t).PosDef) :
    ContDiffAt ℝ m (fun u => Real.log (Γ u).det.re) t := by
  classical
  have hdet : ContDiffAt ℝ m (fun u => (Γ u).det) t := by
    simp only [Matrix.det_apply]
    refine ContDiffAt.sum fun σ _ => ?_
    refine ContDiffAt.const_smul _ ?_
    exact contDiffAt_prod fun i _ => h (σ i) i
  have hre : ContDiffAt ℝ m (fun u => (Γ u).det.re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t hdet
  refine hre.log ?_
  have hpos := hp.det_pos
  have h0 : 0 < (Γ t).det.re := (Complex.pos_iff.mp hpos).1
  exact h0.ne'

variable {n a : ℕ}

theorem tame_logdet {a₀ k r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ k Λ)
    (U : Fin r → (Fin n → ℂ) → Fin k → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hU : ∀ j, DifferentiableOn ℂ (U j) (Metric.ball 0 1)) (hli : LinearIndependent ℂ fun j => U j 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a) :
    Tame a fun t => Real.log (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)).det.re := by
  classical
  obtain ⟨ε, c, C, hε, hερ, hc, hC, hB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.logBound_recentred n a₀ k r a Λ L U 0 π ρ hρ hρ1 hU hli
    (fun i hi => ⟨ha i hi, rfl⟩)
  set G : (Fin n → ℂ) → Matrix (Fin r) (Fin r) ℂ :=
    fun y => HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π y) with hGdef
  have hpunct : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      HodgeMetric.uncentre 0 ρ π y ∈ Flat.punct n a₀ 1 := by
    intro y hy hy0
    refine ⟨HodgeMetric.uncentre_mem_ball hρ π (by simpa using hy.trans_le hερ), ?_⟩
    intro i hi
    simp only [HodgeMetric.uncentre, Pi.zero_apply, sub_zero]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hρ.ne')) (hy0 _ (ha i hi))
  have hB' : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ((G y)⁻¹ - (c : ℂ) • 1).PosSemidef ∧ (((C * logR a y : ℝ) : ℂ) • 1 - (G y)⁻¹).PosSemidef ∧
      ∀ p q, ‖fderiv ℝ (fun y' => G y' p q) y‖ ≤ C * Real.exp (logR a y / 2) := by
    intro y hy hy1 hy0
    exact hB y (by simpa using hy) hy1 (hpunct y hy hy0)
  have hPD : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      (G y).PosDef := fun y hy hy1 hy0 => posDef_of_inv_ge hc (hB' y hy hy1 hy0).1
  have hentry : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞) (fun u => G u p q) y := by
    intro y hy hy0 p q
    exact (_root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramSmooth.periodGram_contDiffAt n a₀ k r Λ L U hU p q _ (hpunct y hy hy0)).comp y
      (HodgeMetric.contDiff_uncentre 0 ρ π).contDiffAt
  have hgood : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ᶠ z in 𝓝 y, ‖z‖ < ε ∧ ‖z‖ < 1 ∧ ∀ i : Fin n, (i : ℕ) < a → z i ≠ 0 := by
    intro y hy hy1 hy0
    refine (continuous_norm.continuousAt.eventually_lt continuousAt_const hy).and
      ((continuous_norm.continuousAt.eventually_lt continuousAt_const hy1).and ?_)
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : (i : ℕ) < a
    · have hc' : ContinuousAt (fun z : Fin n → ℂ => z i) y := (continuous_apply i).continuousAt
      filter_upwards [hc'.eventually_ne (hy0 i hi)] with z hz _ using hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hi
  refine tame_of (C₁ := r * (|Real.log c| + |Real.log C| + 1))
    (C₂ := 3 * r ^ 4 * (max 1 c⁻¹) ^ 2 * max (max 1 c⁻¹) C * C) (e := 1) hε (by positivity)
    (by positivity) zero_le_one ?_
  intro y hy hy1 hy0
  have hB1 := hB' y hy hy1 hy0
  have hpd := hPD y hy hy1 hy0
  have hR1 : 1 ≤ logR a y := one_le_logR hy1 hy0
  have hLL : 1 ≤ Real.log (logR a y) := one_le_log_logR hy1 hy0
  have hK : 0 < C * logR a y := mul_pos hC (by linarith)
  refine ⟨contDiffAt_logdet (Γ := G) (hentry y hy hy0) hpd, ?_, ?_⟩
  · have hlo := logdet_mono (posDef_smul_one (r := r) hc) hpd.inv hB1.1
    have hhi := logdet_mono hpd.inv (posDef_smul_one (r := r) hK) hB1.2.1
    rw [logdet_smul_one hc, logdet_inv hpd] at hlo
    rw [logdet_smul_one hK, logdet_inv hpd, Real.log_mul hC.ne' (by linarith)] at hhi
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h1 : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have h2 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h3 : -((r : ℝ) * |Real.log c|) ≤ r * Real.log c := by
      have := mul_le_mul_of_nonneg_left h1 hr
      rwa [mul_neg] at this
    have p1 : 0 ≤ (r : ℝ) * |Real.log C| := mul_nonneg hr (abs_nonneg _)
    have p2 : 0 ≤ (r : ℝ) * |Real.log c| := mul_nonneg hr (abs_nonneg _)
    have p3 : (r : ℝ) * (|Real.log c| + |Real.log C|) ≤
        r * (|Real.log c| + |Real.log C|) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C|) := by positivity
      nlinarith
    have h4 : (r : ℝ) * Real.log C ≤ r * |Real.log C| := mul_le_mul_of_nonneg_left h2 hr
    have h5 : (r : ℝ) * (|Real.log c| + |Real.log C| + 1) ≤
        r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C| + 1) := by positivity
      nlinarith
    have h6 : (r : ℝ) * Real.log (logR a y) ≤ r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ Real.log (logR a y) := by linarith
      have : (0 : ℝ) ≤ |Real.log c| + |Real.log C| := by positivity
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  · set P : ℝ := max 1 c⁻¹ with hP
    set Q : ℝ := max P C * Real.exp (logR a y / 2) with hQ
    have hP1 : 1 ≤ P := le_max_left _ _
    have hE : 1 ≤ Real.exp (logR a y / 2) := Real.one_le_exp (by linarith)
    have hPQ : P ≤ Q := by
      have : P ≤ max P C := le_max_left _ _
      have : 0 ≤ max P C := by linarith
      nlinarith
    have hd := _root_.GlobalTheory.CompanionTheory.Ar.PB.StepW.gram_grad_scaled r r (Fin n → ℂ) G (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) y
      (C * logR a y)⁻¹ P Q (inv_pos.2 hK) (by linarith) hPQ
      (fun p q => ((hentry y hy hy0 p q).differentiableAt (by simp)))
      (fun p q => differentiableAt_const _)
      (by
        filter_upwards [hgood y hy hy1 hy0] with z hz
        refine ⟨hPD z hz.1 hz.2.1 hz.2.2, ?_⟩
        have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) = ⇑(Pi.basisFun ℂ (Fin r)) := by
          ext i j
          simp [Matrix.one_apply, Pi.single_apply, eq_comm]
        rw [Matrix.transpose_one, h1]
        exact (Pi.basisFun ℂ (Fin r)).linearIndependent)
      (by
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        exact ge_of_inv_le hK hpd hB1.2.1)
      (fun p q => ⟨(norm_entry_le hpd.posSemidef (le_of_inv_ge hc hpd hB1.1) p q).trans (le_max_right _ _),
        (hB1.2.2 p q).trans (by
          have : C ≤ max P C := le_max_right _ _
          have : 0 ≤ Real.exp (logR a y / 2) := by positivity
          nlinarith)⟩)
      (fun p q => ⟨by
          rw [Matrix.one_apply]
          split_ifs <;> simp <;> linarith,
        by simp [fderiv_const_apply]; linarith⟩)
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hd
    refine hd.trans (le_of_eq ?_)
    rw [Real.rpow_one, hQ, div_inv_eq_mul]
    ring

end AnalyticReference.An.H
end
end

