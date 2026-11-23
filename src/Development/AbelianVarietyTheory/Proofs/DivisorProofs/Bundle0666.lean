module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivDiagIm
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesFDerivSkew
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_gram_entry (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) {R : ℝ}
    (hR : ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom) {w : V (nd X)}
    (hw : w ∈ Metric.ball (0 : V (nd X)) R) (τ : X.Ψ) (a b : Fin r) :
    ∑ k, yF X w τ k a * ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) * conj (yF X w τ k b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h1 := FrameDegreeData.ortho_bOf X (hR w hw) τ
  rw [bOf_cpt X hx w] at h1
  have h2 : mat (rmul (cpt X x w) (fun τ => gsB X w τ)) τ = mat x τ * yM X w τ := by
    show mat x τ * mat (nmat X w) τ * gsB X w τ = _
    rw [yM, Matrix.mul_assoc]
  rw [h2, FrameDegreeData.gram_mul, hx τ] at h1
  have h3 := congrFun (congrFun h1 a) b
  rw [Matrix.mul_apply] at h3
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply] at h3
  rw [← h3]
  rfl

theorem dY_skew (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    dY X z τ b a * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) + ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * conj (dY X z τ a b) = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  obtain ⟨R, hR, hdom⟩ := exists_ball X hx
  set ε : Fin r → ℂ := fun k => ((sgn X.p0 (k : ℕ) : ℝ) : ℂ) with hε
  have hY : HasFDerivAt (yF X) (dY X) 0 := hd.hasFDerivAt
  let P : Fin r → Fin r → (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ := fun k c =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) c).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : ∀ k c, HasFDerivAt (fun w => yF X w τ k c) ((P k c).comp (dY X)) 0 :=
    fun k c => (P k c).hasFDerivAt.comp 0 hY
  have hcc : ∀ k c, HasFDerivAt (fun w => conj (yF X w τ k c))
      ((Complex.conjCLE.toContinuousLinearMap).comp ((P k c).comp (dY X))) 0 :=
    fun k c => Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp 0 (hc k c)
  have hf := HasFDerivAt.sum (u := Finset.univ) fun k _ => ((hc k a).mul_const (ε k)).mul (hcc k b)
  have hconst : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b))
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    refine (hasFDerivAt_const (if a = b then ε a else 0) (0 : V (nd X))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : V (nd X)) hR] with w hw
    exact yF_gram_entry X hx hdom hw τ a b
  have hf' : HasFDerivAt (fun w => ∑ k ∈ Finset.univ, yF X w τ k a * ε k * conj (yF X w τ k b)) _ 0 :=
    hf.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp [Finset.sum_apply])
  have key := congrArg (fun L => L z) (hf'.unique hconst)
  have h0 : ∀ k c, yF X 0 τ k c = if k = c then 1 else 0 := by
    intro k c
    show yM X 0 τ k c = _
    rw [yM_zero, Matrix.one_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, h0] at key
  simp only [ite_mul, one_mul, zero_mul, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_smul, zero_smul,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at key
  linear_combination key

end GlobalTheory.SUChartSection
end

