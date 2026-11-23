module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContDiffHerm
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_herm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (herm (n := n)) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have hc : ∀ a b : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : E n => ((x a b : ℝ) : ℂ)) := fun a b =>
    Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ (fun _ => ℝ) b).comp (contDiff_apply ℝ (fun _ => (Fin n → ℝ)) a))
  simp only [herm]
  push_cast
  exact (((hc i j).add (hc j i)).div_const 2).add ((contDiff_const.mul ((hc i j).sub (hc j i))).div_const 2)

theorem clsGainB_of (hC : CauchyW) (hI : Invar) (hB : PBound) (hL : Link) (hT : Twist) (hLg : Lagr) : ClsGain := by
  intro n s hs p q N R
  obtain ⟨hUo, hFc, -⟩ := hB n s hs p q R
  have hH : ContDiff ℝ (⊤ : ℕ∞) (cls s 0 p q R) := by
    rw [cls_zero]
    rw [contDiff_iff_contDiffAt]
    intro y
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (Fr s p q R) (herm y) :=
      ((hFc.restrict_scalars ℝ).contDiffAt (hUo.mem_nhds (herm_mem_Ugood s hs y)))
    exact h1.comp y (contDiff_herm n).contDiffAt
  obtain ⟨G, hGc, hG⟩ := hT n (cls s 0 p q R) hH N
  have hcls : ∀ z : ℂ, cls s z p q R = fun y => ((dP y : ℝ) : ℂ) ^ (-z) * cls s 0 p q R y := by
    intro z; funext y; simp only [cls, neg_zero, Complex.cpow_zero, one_mul]; ring
  set D := n * N with hD
  have hrat : ∀ i : ℕ, ∃ C : ℝ, ∀ y : E n,
      ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖ ≤ C * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2) :=
    fun i => ratBound hC hI hB hL s hs (p + i) (q + i) N R
  choose Ci hCi using hrat
  obtain ⟨CL, hCL⟩ := hLg D
  set Cm : ℝ := ∑ i ∈ Finset.range (D + 1), |Ci i| with hCm
  refine ⟨D + 1, fun j => Polynomial.X ^ (j : ℕ), fun j => G j, fun j => (hGc j).continuous, ⟨CL * Cm, ?_⟩, ?_⟩
  · intro j y
    have hdp := dP_pos y
    have hval : ∀ i ≤ D, ‖∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y‖ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
      intro i hi
      have e1 := hG (i : ℂ) y
      rw [← hcls, cls_nat s hs i p q R] at e1
      have hne : (((dP y : ℝ) : ℂ)) ^ (-(i : ℂ)) ≠ 0 := by
        rw [Complex.cpow_neg, Complex.cpow_natCast]; exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hdp.ne'))
      have e2 : ∑ j ∈ Finset.range (D + 1), ((i : ℕ) : ℂ) ^ j * G j y =
          (((dP y : ℝ) : ℂ)) ^ i * (Delta^[N] (cls s 0 (p + i) (q + i) R)) y := by
        rw [e1, Complex.cpow_neg, Complex.cpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hdp.ne')), one_mul]
      rw [e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdp.le]
      have hb := hCi i y
      have hCi_le : |Ci i| ≤ Cm := by
        rw [hCm]
        exact Finset.single_le_sum (f := fun i => |Ci i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      calc dP y ^ i * ‖(Delta^[N] (cls s 0 (p + i) (q + i) R)) y‖
          ≤ dP y ^ i * (Ci i * (dP y) ^ (-((p + i + (q + i) + N : ℕ) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hb (pow_nonneg hdp.le _)
        _ = Ci i * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) := by
            rw [← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hdp]
            congr 2; push_cast; ring
        _ ≤ Cm * (dP y) ^ (-((p + q + N : ℕ) : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCi_le) (Real.rpow_nonneg hdp.le _)
    have := hCL (fun j => G j y) _ hval j (Nat.lt_succ_iff.1 j.2)
    simpa [mul_assoc] using this
  · intro z y
    rw [hcls z, hG z y]
    congr 1
    rw [Finset.sum_range (fun j => z ^ j * G j y)]
    simp [Polynomial.eval_pow, Polynomial.eval_X]

end PositivityTheory.Rg.Sw.WR.K.GB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousCexpIp
section
noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem continuous_cexp_ip (t : ℝ) : Continuous (fun p : E n × E n => Complex.exp (-(Complex.I * t * ip p.1 p.2))) :=
  Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_ip)).neg)

set_option maxHeartbeats 1000000 in
theorem lim_one (ρ : E n → ℂ) (hρ : Integrable ρ) (t : ℝ) (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ)
    (C : ℂ) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k => ∫ β, ψ β * (C * ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))))
      atTop (𝓝 (∫ β, ψ β * (C * ∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y))))) := by
  have hexp := continuous_cexp_ip (n := n) t
  have hbd : ∀ k y β, ‖ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))‖ ≤ ‖ρ y‖ := by
    intro k y β
    rw [norm_mul, norm_mul, norm_cexp_neg_It, mul_one]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_gauss_le _ (hε k) y)
  have hcont : ∀ k, Continuous (fun β : E n => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y))) := by
    intro k
    refine continuous_of_dominated (bound := fun y => ‖ρ y‖) ?_ ?_ hρ.norm ?_
    · intro β
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro β; exact Eventually.of_forall fun y => hbd k y β
    · exact Eventually.of_forall fun y => by
        have hip : Continuous (fun β : E n => ip β y) := by
          unfold ip
          fun_prop
        have hy : Continuous (fun β : E n => Complex.exp (-(Complex.I * t * ip β y))) :=
          Complex.continuous_exp.comp ((continuous_const.mul (Complex.continuous_ofReal.comp hip)).neg)
        exact continuous_const.mul hy
  have hin : ∀ β : E n, Tendsto (fun k => ∫ y, ρ y * gam (ε k) y * Complex.exp (-(Complex.I * t * ip β y)))
      atTop (𝓝 (∫ y, ρ y * Complex.exp (-(Complex.I * t * ip β y)))) := by
    intro β
    refine tendsto_integral_of_dominated_convergence (fun y => ‖ρ y‖) ?_ hρ.norm ?_ ?_
    · intro k
      exact (hρ.aestronglyMeasurable.mul (continuous_gam (ε k)).aestronglyMeasurable).mul
        (hexp.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro k; exact Eventually.of_forall fun y => hbd k y β
    · refine Eventually.of_forall fun y => ?_
      have h0 : Tendsto (fun k => -(((ε k * ip y y : ℝ)) : ℂ)) atTop (𝓝 0) := by
        have h := hε0.mul_const (ip y y)
        rw [zero_mul] at h
        have h' := ((Complex.continuous_ofReal.tendsto 0).comp h).neg
        simpa [Function.comp_def] using h'
      have hg : Tendsto (fun k => gam (ε k) y) atTop (𝓝 1) := by
        have := (Complex.continuous_exp.tendsto 0).comp h0
        simpa [gam, Function.comp_def] using this
      have := ((tendsto_const_nhds (x := ρ y)).mul hg).mul
        (tendsto_const_nhds (x := Complex.exp (-(Complex.I * t * ip β y))))
      simpa using this
  refine tendsto_integral_of_dominated_convergence (fun β => ‖ψ β‖ * (‖C‖ * ∫ y, ‖ρ y‖)) ?_
    (hψi.norm.mul_const _) ?_ ?_
  · intro k
    exact (hψc.mul (continuous_const.mul (hcont k))).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun β => ?_
    rw [norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (norm_nonneg _)
    exact norm_integral_le_of_norm_le hρ.norm (Eventually.of_forall fun y => hbd k y β)
  · exact Eventually.of_forall fun β => tendsto_const_nhds.mul (tendsto_const_nhds.mul (hin β))

set_option maxHeartbeats 1000000 in
theorem lim_two (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (ψ : E n → ℂ)
    (hψc : Continuous ψ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (l : ℕ → ℝ) (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, Ψ x * mM ψ (l k) (qq x) ∂μ) atTop (𝓝 (∫ x, ψ (qq x) * Ψ x ∂μ)) := by
  have hlim : ∫ x, ψ (qq x) * Ψ x ∂μ = ∫ x, Ψ x * ψ (qq x) ∂μ := by simp_rw [mul_comm]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖Ψ x‖ * B) ?_ (hΨ.norm.mul_const _) ?_ ?_
  · intro k
    exact hΨ.aestronglyMeasurable.mul ((continuous_mM ψ B hB hψc (l k)).measurable.comp hqq).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun x => ?_
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_mM_le ψ B hB hψc _ _) (norm_nonneg _)
  · exact Eventually.of_forall fun x => tendsto_const_nhds.mul (tendsto_mM ψ B hB hψc l hl (qq x))

set_option maxHeartbeats 1000000 in
theorem eq_A (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by
  have ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ :=
    fun β => step_a Ψ qq hΨ hqq t ε hε β
  simp_rw [ha]
  rw [step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]
  congr 1
  funext x
  rw [step_c ψ t ε ht hε (qq x)]

theorem _root_.PositivityTheory.Rg.Sw.WR.D.mollId : MollId := by
  intro n X _ μ _ Ψ qq hΨ hqq t ht hρ ψ hψc hψs
  obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
  have hψi : Integrable ψ := hψc.integrable_of_hasCompactSupport hψs
  have hε : ∀ k : ℕ, 0 < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hε0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) atTop (𝓝 0) := by
    have e : (fun k : ℕ => (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1))))⁻¹) =
        fun k : ℕ => (2 / |t|) * Real.sqrt (1 / ((k : ℝ) + 1)) := by
      funext k; rw [inv_div]; ring
    rw [e]
    have h := ((Real.continuous_sqrt.tendsto 0).comp hε0).const_mul (2 / |t|)
    simpa [Real.sqrt_zero, Function.comp_def] using h
  have h1 := lim_one _ hρ t ψ hψc hψi ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ)) _ hε hε0
  have h2 := lim_two Ψ qq hΨ hqq ψ hψc B hB _ hl
  have e : (fun k : ℕ => ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam (1 / ((k : ℝ) + 1)) y *
          Complex.exp (-(Complex.I * t * ip β y)))) =
      fun k : ℕ => ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt (1 / ((k : ℝ) + 1)))) (qq x) ∂μ := by
    funext k
    exact eq_A Ψ qq hΨ hqq t ht ψ hψc hψi _ (hε k)
  rw [e] at h1
  exact tendsto_nhds_unique h2 h1

end PositivityTheory.Rg.Sw.WR.D.Moll
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GWickC
section
noncomputable section

open MeasureTheory Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.WR.G

open PositivityTheory.Rg.Sw

theorem wick_of (hI : IntegP) : Wick := by
  intro m n ε c t hc b hb M a i
  have hdet := amat_det_ne ε hc t hb a
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set E : (Fin m → Fin n → ℂ) → ℂ := fun x => Complex.exp (evX (phiP ε c t b) x) with hEdef
  have hsec : ∀ P, secN ε c t P b = ∫ x, evX P x * E x := by
    intro P; unfold secN; congr 1; funext x; rw [mul_assoc, exp_phiP]
  have hint : ∀ P, Integrable (fun x => evX P x * E x) := by
    intro P
    refine (hI m n c hc P).mono ?_ ?_
    · exact ((evX_continuous P).mul (evX_continuous (phiP ε c t b)).cexp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      have hx : E x = gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := (exp_phiP ε c t b x).symm
      rw [hx, ← mul_assoc, norm_mul _ (Complex.exp _), norm_exp_tr ε t b hb x, mul_one]
  have hE : ∀ x, HasFDerivAt E (E x • dEv (phiP ε c t b) x) x := fun x => (hasFDerivAt_evX (phiP ε c t b) x).cexp
  have hfd : ∀ x v, fderiv ℝ E x v = E x * evX (∑ k, C (crd k v) * pderiv k (phiP ε c t b)) x := by
    intro x v; rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul, dEv_apply]
  have hPd : ∀ (P : PX m n) x v, fderiv ℝ (evX P) x v = evX (∑ k, C (crd k v) * pderiv k P) x := by
    intro P x v; rw [(hasFDerivAt_evX P x).fderiv, dEv_apply]
  have hintD : ∀ (P : PX m n) v, Integrable (fun x => evX P x * fderiv ℝ E x v) := by
    intro P v
    refine (hint (P * ∑ k, C (crd k v) * pderiv k (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hfd]; simp only [evX, map_mul]; ring
  have hintM : ∀ (P : PX m n) v, Integrable (fun x => fderiv ℝ (evX P) x v * E x) := by
    intro P v; simp_rw [hPd]; exact hint _
  have ibp : ∀ (P : PX m n) (v : Fin m → Fin n → ℂ),
      ∫ x, evX P x * fderiv ℝ E x v = -∫ x, fderiv ℝ (evX P) x v * E x := by
    intro P v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hintM P v) (hintD P v) (hint P)
      (fun x _ => (hasFDerivAt_evX P x).differentiableAt) (fun x _ => (hE x).differentiableAt)
  have ibpW : ∀ j : Fin n, ∫ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
      -∫ x, evX (pderiv (a, j, false) M) x * E x := by
    intro j
    have hWE : ∀ x, fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
        Complex.I * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) =
        2 * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) := by
      intro x
      rw [(hE x).fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
      have := dEv_wirt (phiP ε c t b) x a j
      linear_combination (E x) * this
    have hpt : ∀ x, evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x) =
        (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) -
          Complex.I * (evX M x * fderiv ℝ E x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0))) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero)]
      linear_combination (-(evX M x)) * hWE x
    have hptM : ∀ x, evX (pderiv (a, j, false) M) x * E x =
        (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then (1 : ℂ) else 0) * E x -
          Complex.I * (fderiv ℝ (evX M) x (fun a' i' => if a' = a ∧ i' = j then Complex.I else 0) * E x)) / 2 := by
      intro x
      rw [eq_div_iff (two_ne_zero), (hasFDerivAt_evX M x).fderiv]
      have := dEv_wirt M x a j
      linear_combination (-(E x)) * this
    simp_rw [hpt, hptM]
    rw [integral_div, integral_div, integral_sub (hintD M _) ((hintD M _).const_mul _),
      integral_sub (hintM M _) ((hintM M _).const_mul _), integral_const_mul, integral_const_mul, ibp, ibp]
    ring
  have hAA : Amat ε c t b a * (Amat ε c t b a)⁻¹ = 1 := Matrix.mul_nonsing_inv (Amat ε c t b a) (isUnit_iff_ne_zero.mpr hdet)
  have key : ∀ x, evX (X (a, i, true) * M) x * E x =
      -∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * evX (pderiv (a, j, false) (phiP ε c t b)) x)) := by
    intro x
    simp only [evX_pderiv_phiP]
    have h1 : ∀ k, ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i = if k = i then 1 else 0 := by
      intro k; rw [← Matrix.mul_apply, hAA, Matrix.one_apply]
    have h2 : ∑ j, (Amat ε c t b a)⁻¹ j i * (evX M x * (E x * -∑ k, Amat ε c t b a k j * star (x a k))) =
        -(evX M x * E x * ∑ k, star (x a k) * ∑ j, Amat ε c t b a k j * (Amat ε c t b a)⁻¹ j i) := by
      simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_neg]
    simp only [evX, map_mul, eval_X, if_true]
    ring
  rw [hsec]
  simp_rw [key]
  rw [integral_neg, MeasureTheory.integral_finsetSum]
  · simp only [integral_const_mul, ibpW, hsec]
    simp only [Finset.sum_neg_distrib, mul_neg, neg_neg]
  · intro j _
    refine Integrable.const_mul ?_ _
    refine (hint (M * pderiv (a, j, false) (phiP ε c t b))).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [evX, map_mul]; ring

end PositivityTheory.Rg.Sw.WR.G
end
end

