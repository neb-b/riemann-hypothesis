module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.FderivXZxSkew
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x i j) :=
  contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j

theorem xZx_apply (x Z : M2 n) (i j : Fin n ⊕ Fin n) :
    (x * Z * xᴴ) i j = ∑ l, (∑ m, x i m * Z m l) * starRingEnd ℂ (x j l) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem contDiff_xZx (Z : M2 n) (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => (x * Z * xᴴ) i j) := by
  simp_rw [xZx_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)

theorem cDiff : CDiff := by
  intro n Z a b
  exact ⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩

theorem fderiv_xZx (Z x v : M2 n) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x v = (v * Z * xᴴ + x * Z * vᴴ) i j := by
  have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x :=
    ((contDiff_xZx Z i j).differentiable (by simp)).differentiableAt
  refine (hd.lineDeriv_eq_fderiv (v := v)).symm.trans ?_
  have e : (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) = fun t : ℝ =>
      (x * Z * xᴴ) i j + (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j + (t : ℂ) ^ 2 * (v * Z * vᴴ) i j := by
    funext t
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_smul]
    ring
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
      simpa using hr.mul_const ((v * Z * xᴴ + x * Z * vᴴ) i j)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * (v * Z * vᴴ) i j) 0 0 := by
      simpa using (hr.pow 2).mul_const ((v * Z * vᴴ) i j)
    have h3 := ((hasDerivAt_const (0 : ℝ) ((x * Z * xᴴ) i j)).add h1).add h2
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp
  simpa [lineDeriv] using h.deriv

theorem reK_add_imK (e : M2 n) : reK e + Complex.I • imK e = e := by
  simp only [reK, imK, smul_smul, smul_sub, smul_add]
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
  rw [h]
  module

theorem reK_conj (e : M2 n) : (reK e)ᴴ = -reK e := by
  simp only [reK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]; module

theorem imK_conj (e : M2 n) : (imK e)ᴴ = -imK e := by
  simp only [imK, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  have : star (-Complex.I / 2) = -(-Complex.I / 2) := by simp [Complex.conj_I]; ring
  rw [this]; module

theorem fderiv_xZx_skew (Z x E : M2 n) (hE : Eᴴ = -E) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x (E * x) = (E * (x * Z * xᴴ) - (x * Z * xᴴ) * E) i j := by
  rw [fderiv_xZx, Matrix.conjTranspose_mul, hE]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]

theorem dK_xZx (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by
  rw [dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]
  conv_rhs => rw [← reK_add_imK e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem toBlocks₂₂_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := rfl
theorem toBlocks₁₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := rfl

theorem decomp (M : M2 n) : M = fromBlocks (M.toBlocks₁₁ - M.toBlocks₂₂) (M.toBlocks₁₂ + M.toBlocks₂₁) 0 0 +
    ∑ a, ∑ b, (M.toBlocks₂₂ a b • eA a b + (-M.toBlocks₂₁ a b) • eB a b) := by
  ext i j
  rcases i with a' | a' <;> rcases j with b' | b' <;>
    simp [eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem eA_mul_apply (M : M2 n) (a b : Fin n) : (eA a b * M) (Sum.inr a) (Sum.inr b) = M (Sum.inr b) (Sum.inr b) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eA_apply (M : M2 n) (a b : Fin n) : (M * eA a b) (Sum.inr a) (Sum.inr b) = M (Sum.inr a) (Sum.inr a) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem eB_mul_apply (M : M2 n) (a b : Fin n) : (eB a b * M) (Sum.inr a) (Sum.inl b) = -M (Sum.inl b) (Sum.inl b) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem mul_eB_apply (M : M2 n) (a b : Fin n) : (M * eB a b) (Sum.inr a) (Sum.inl b) = -M (Sum.inr a) (Sum.inr a) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

theorem sumA (M : M2 n) : ∑ a, ∑ b, ((eA a b * M - M * eA a b : M2 n) (Sum.inr a) (Sum.inr b)) = 0 := by
  simp only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]
  simp

theorem sumB (M : M2 n) : ∑ a, ∑ b, -((eB a b * M - M * eB a b : M2 n) (Sum.inr a) (Sum.inl b)) =
    (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) := by
  simp only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) =
      M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a) := fun _ _ => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]

theorem ptId : PtId := by
  intro n Θ x Z hx hΘ hlaw
  set M := x * Z * xᴴ with hM
  have hxZ : x * Z = M * x := by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]
  have hΘd : DifferentiableAt ℂ Θ x := hΘ.differentiableAt (by simp)
  have hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v := fun v => by
    have h := (hΘd.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (congrArg (fun L => L v) h).trans rfl
  have hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x) := fun e => by
    rw [dK, hR, hR]
    conv_rhs => rw [← reK_add_imK e]
    rw [Matrix.add_mul, Matrix.smul_mul, map_add (f := _), map_smul, smul_eq_mul]
  have hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e,
      dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e := fun c hc e => by
    have hΘr : DifferentiableAt ℝ Θ x := hΘd.restrictScalars ℝ
    have h := (hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv
    have hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl
    simp only [dK, hv]
    ring
  have hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x := fun a b =>
    ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt
  have hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x := fun a b =>
    ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt
  have hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b) := fun a b e =>
    dK_xZx Z x e (Sum.inr a) (Sum.inr b)
  have hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b)) := fun a b e => by
    have : cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) := rfl
    have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x :=
      ((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt
    have hn := hd.hasFDerivAt.neg.fderiv
    have hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v =
        -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl
    have h := dK_xZx Z x e (Sum.inr a) (Sum.inl b)
    rw [dK] at h
    rw [this, dK, hv, hv, ← h]; ring

  have hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x +
      ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := by
    rw [hxZ]
    conv_lhs => rw [decomp M]
    rw [Matrix.add_mul, map_add (f := _), hlaw _ (by simp)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add (f := _), map_smul, smul_eq_mul, hdK]
    congr 1
    · simp [Matrix.trace_sub]
  rw [hL]
  simp only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]
  have e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) +
      (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) =
      ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b))) * Θ x +
      (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := fun a b => by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]
  ring

end PositivityTheory.Rg.Sw.LVs.II
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.IILeft
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def cE (E : M2 n) (s : ℝ) : M2 n := NormedSpace.exp (s • E)

set_option backward.isDefEq.respectTransparency false in
theorem cE_entry (E : M2 n) (a b : Fin n ⊕ Fin n) :
    HasDerivAt (fun s : ℝ => cE E s a b) (E a b) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) E (0 : ℝ)
  open scoped Matrix.Norms.Operator in
  have h2 := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simpa [Function.comp_def, cE] using h2

theorem cE_hasDerivAt0 (E : M2 n) : HasDerivAt (cE E) E 0 := by
  have h : HasDerivAt (fun s : ℝ => (cE E s : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ))
      (E : (Fin n ⊕ Fin n) → (Fin n ⊕ Fin n) → ℂ) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => cE_entry E a b
  exact h

theorem cE_zero (E : M2 n) : cE E 0 = 1 := by simp [cE]

theorem cE_add (E : M2 n) (s t : ℝ) : cE E (s + t) = cE E s * cE E t := by
  unfold cE
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl E).smul_left s |>.smul_right t)

def mulL (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ A)

def mulR (A : M2 n) : M2 n →L[ℝ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ A)

theorem mulL_apply (A B : M2 n) : mulL A B = A * B := rfl

theorem cE_hasDerivAt (E : M2 n) (s : ℝ) : HasDerivAt (cE E) (cE E s * E) s := by
  have h0 : HasDerivAt (fun t : ℝ => cE E (t - s)) E s := by
    have h : HasDerivAt (cE E) E (s - s) := by simpa using cE_hasDerivAt0 E
    exact HasDerivAt.comp_sub_const s s h
  have h1 : HasDerivAt (fun t : ℝ => cE E s * cE E (t - s)) (cE E s * E) s :=
    (mulL (cE E s)).hasFDerivAt.comp_hasDerivAt s h0
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp only
  rw [← cE_add]
  congr 1
  ring

theorem cE_continuous (E : M2 n) : Continuous (cE E) :=
  continuous_iff_continuousAt.2 fun s => (cE_hasDerivAt E s).continuousAt

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  simp [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

theorem cE_inK (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) (s : ℝ) : InK (cE E s) := by
  have hct : (cE E s)ᴴ = cE E (-s) := by
    unfold cE
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hE]
    simp [neg_smul, smul_neg]
  have hinv : (cE E s)ᴴ * cE E s = 1 := by
    rw [hct, ← cE_add, neg_add_cancel, cE_zero]
  have hcomm : cE E s * JJ n = JJ n * cE E s := by
    have hc : Commute (s • E) (JJ n) := by
      show s • E * JJ n = JJ n * (s • E)
      rw [Matrix.smul_mul, hEJ, Matrix.mul_smul]
    exact (hc.exp_left).eq
  refine ⟨?_, hinv⟩
  unfold InG
  rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem core {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n)
    (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hKU : KSet n ⊆ U) (hF : ContDiffOn ℝ 1 F U)
    (E : M2 n) (hE : Eᴴ = -E) (hEJ : E * JJ n = JJ n * E) :
    Integrable (fun k => fderiv ℝ F (ι k) (E * ι k)) μ ∧ ∫ k, fderiv ℝ F (ι k) (E * ι k) ∂μ = 0 := by
  have hΦc : Continuous (fun p : ℝ × Kg => cE E p.1 * ι p.2) :=
    ((cE_continuous E).comp continuous_fst).matrix_mul (hι.comp continuous_snd)
  have hmem0 : ∀ k, ι k ∈ U := fun k => hKU ((hK (ι k)).2 ⟨k, rfl⟩)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ k ∈ (Set.univ : Set Kg), cE E s * ι k ∈ U := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun k _ => ?_
    have h0 : cE E 0 * ι k ∈ U := by rw [cE_zero, Matrix.one_mul]; exact hmem0 k
    exact hΦc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hin : ∀ s : ℝ, |s| ≤ ε / 2 → ∀ k, cE E s * ι k ∈ U := fun s hs k =>
    hball (by rw [Real.dist_eq, sub_zero]; linarith) k (Set.mem_univ _)
  have hfd : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  set S : Set (ℝ × Kg) := Set.Icc (-(ε / 2)) (ε / 2) ×ˢ Set.univ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hmapS : ∀ p ∈ S, cE E p.1 * ι p.2 ∈ U := fun p hp =>
    hin p.1 (abs_le.2 ⟨hp.1.1, hp.1.2⟩) p.2
  have hGc : ContinuousOn (fun p : ℝ × Kg => fderiv ℝ F (cE E p.1 * ι p.2) (cE E p.1 * E * ι p.2)) S := by
    refine ContinuousOn.clm_apply (hfd.comp hΦc.continuousOn hmapS) ?_
    exact ((((cE_continuous E).comp continuous_fst).matrix_mul continuous_const).matrix_mul (hι.comp continuous_snd)).continuousOn
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hGc
  have hdiffF : ∀ y ∈ U, DifferentiableAt ℝ F y := fun y hy =>
    (hF.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hy)
  have hs : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by linarith)
  have hsub : ∀ s ∈ Metric.ball (0 : ℝ) (ε / 2), |s| ≤ ε / 2 := fun s hs' => by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs'; exact hs'.le
  have hcontF : ∀ s : ℝ, |s| ≤ ε / 2 → Continuous (fun k => F (cE E s * ι k)) := fun s hs' =>
    hF.continuousOn.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k
  have hcontF' : ∀ s : ℝ, |s| ≤ ε / 2 →
      Continuous (fun k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) := fun s hs' =>
    (hfd.comp_continuous (continuous_const.matrix_mul hι) fun k => hin s hs' k).clm_apply (continuous_const.matrix_mul hι)
  have h0 : |(0 : ℝ)| ≤ ε / 2 := by rw [abs_zero]; linarith
  have hint0 : Integrable (fun k => F (cE E 0 * ι k)) μ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcontF 0 h0).continuousOn
    exact Integrable.mono' (integrable_const C) (hcontF 0 h0).aestronglyMeasurable
      (Eventually.of_forall fun k => hC k (Set.mem_univ _))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s k => F (cE E s * ι k)) (bound := fun _ => B)
    (F' := fun s k => fderiv ℝ F (cE E s * ι k) (cE E s * E * ι k)) hs
    (by filter_upwards [hs] with s hs' using (hcontF s (hsub s hs')).aestronglyMeasurable)
    hint0 (hcontF' 0 h0).aestronglyMeasurable
    (Eventually.of_forall fun k s hs' => hB (s, k) ⟨⟨(abs_le.1 (hsub s hs')).1, (abs_le.1 (hsub s hs')).2⟩, Set.mem_univ _⟩)
    (integrable_const B)
    (Eventually.of_forall fun k s hs' => by
      have h1 := cE_hasDerivAt E s
      have h2 : HasDerivAt (fun t => cE E t * ι k) (cE E s * E * ι k) s :=
        (mulR (ι k)).hasFDerivAt.comp_hasDerivAt s h1
      exact (hdiffF _ (hin s (hsub s hs') k)).hasFDerivAt.comp_hasDerivAt s h2)
  have hconst : (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) = fun _ => ∫ k, F (ι k) ∂μ := by
    funext s
    obtain ⟨κ, hκ⟩ := (hK (cE E s)).1 (cE_inK E hE hEJ s)
    have : (fun k => F (cE E s * ι k)) = fun k => (fun k' => F (ι k')) (κ * k) := by
      funext k; show F (cE E s * ι k) = F (ι (κ * k)); rw [map_mul, hκ]
    rw [this, integral_mul_left_eq_self (fun k' => F (ι k')) κ]
  have hd0 : HasDerivAt (fun s : ℝ => ∫ k, F (cE E s * ι k) ∂μ) 0 0 := by
    rw [hconst]; exact hasDerivAt_const _ _
  have huniq := key.2.unique hd0
  have hF' : (fun k => fderiv ℝ F (cE E 0 * ι k) (cE E 0 * E * ι k)) = fun k => fderiv ℝ F (ι k) (E * ι k) := by
    funext k; simp [cE_zero]
  rw [hF'] at key huniq
  exact ⟨key.1, huniq⟩

theorem reK_skew (e : M2 n) : (reK e)ᴴ = -reK e := by
  ext i j
  simp only [reK, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem imK_skew (e : M2 n) : (imK e)ᴴ = -imK e := by
  ext i j
  simp only [imK, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

theorem comm_conjT {e : M2 n} (he : e * JJ n = JJ n * e) : eᴴ * JJ n = JJ n * eᴴ := by
  have h := congrArg conjTranspose he
  rw [conjTranspose_mul, conjTranspose_mul, JJ_conjTranspose] at h
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_inj] at h
  exact h.symm

theorem reK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : reK e * JJ n = JJ n * reK e := by
  unfold reK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, he, comm_conjT he]

theorem imK_comm {e : M2 n} (he : e * JJ n = JJ n * e) : imK e * JJ n = JJ n * imK e := by
  unfold imK
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, he, comm_conjT he]

theorem leftDeriv : LeftDeriv := by
  intro n Kg _ _ _ _ _ _ μ _ ι hι hK F U hU hKU hF e he
  obtain ⟨i1, z1⟩ := core μ ι hι hK F U hU hKU hF (reK e) (reK_skew e) (reK_comm he)
  obtain ⟨i2, z2⟩ := core μ ι hι hK F U hU hKU hF (imK e) (imK_skew e) (imK_comm he)
  refine ⟨i1.add (i2.const_mul Complex.I), ?_⟩
  unfold dK
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, z1, z2]
  simp

end PositivityTheory.Rg.Sw.LVs.II
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCBlockA
section
noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def embL (s : Finset (Fin n)) : Matrix s s ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := embOn s
      map_add' := fun T T' => by
        ext a b
        simp only [embOn, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun x T => by
        ext a b
        simp only [embOn, Matrix.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }

def bdL (j : ℕ) (c c' : ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := bdiag j c c'
      map_add' := fun T T' => by
        ext a b
        simp only [bdiag, Matrix.add_apply]
        split_ifs <;> ring
      map_smul' := fun x T => by
        ext a b
        simp only [bdiag, Matrix.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> ring }

theorem bdL_apply (j : ℕ) (c c' : ℂ) (t : Matrix (Fin n) (Fin n) ℂ) : bdL j c c' t = bdiag j c c' t := rfl

theorem mem_blkB (j : ℕ) (r : Fin n) : r ∈ blkB (n := n) j ↔ r ∉ blkA (n := n) j := by
  simp [blkB]

end PositivityTheory.Rg.Sw.LVs.TC
end
end

