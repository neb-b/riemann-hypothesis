module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Growth

open UpperHalfPlane hiding I

def sF (w : ℍ) : ℝ := (1 + ‖(w : ℂ)‖ ^ 2) / w.im

lemma sq_norm_coe (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]
  ring

lemma one_le_sF (w : ℍ) : 1 ≤ sF w := by
  have him := w.im_pos
  rw [sF, le_div_iff₀ him, one_mul, sq_norm_coe]
  nlinarith [sq_nonneg w.re, sq_nonneg (w.im - 1)]

lemma sF_nonneg (w : ℍ) : 0 ≤ sF w := zero_le_one.trans (one_le_sF w)

lemma poly_bound (a b c d x y : ℝ) :
    (c * x + d) ^ 2 + (c * y) ^ 2 + ((a * x + b) ^ 2 + (a * y) ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (1 + (x ^ 2 + y ^ 2)) := by
  nlinarith [sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]

lemma normSq_lin (a b : ℝ) (z : ℍ) :
    Complex.normSq ((a : ℂ) * z + b) = (a * z.re + b) ^ 2 + (a * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma sF_smul (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, sF (g • z) ≤ K * sF z := by
  have hD : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  refine ⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩
  have hN : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  have him := z.im_pos
  have h1 : sF (g • z) =
      (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im) := by
    rw [sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    field_simp
  have h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤
      ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2) := by
    have e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    have e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    rw [e1, e2, sq_norm_coe]
    exact poly_bound _ _ _ _ _ _
  rw [h1, sF, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h2 (mul_pos hD him).le

lemma denom_inv (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖denom g z‖⁻¹ ≤ K * sF z := by
  have hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hdet := g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet
  refine ⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩
  have him := z.im_pos
  have hm : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero g z)
  have hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_lin _ _ z
  have key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2) := by
    rw [hN, sq_norm_coe]
    nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1),
      sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]
  have hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
    have : 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by positivity
    linarith
  have hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) =
      ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1 := by
    field_simp
  have hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2 := by nlinarith [sq_nonneg ‖(z : ℂ)‖]
  set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef
  set K := 1 + 1 / q with hKdef
  set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef
  set m := ‖denom g z‖ with hmdef
  have h1 : 1 ≤ K ^ 2 * q * T := by
    have e : K ^ 2 * q * T = K * (K * q) * T := by ring
    rw [e, hKq]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1
  have hsq : z.im ^ 2 ≤ (K * T * m) ^ 2 := by
    have e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T) := by ring
    rw [e]
    have hKT : 0 ≤ K ^ 2 * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]
  have hP : 0 ≤ K * T * m := by positivity
  have hy : z.im ≤ K * T * m := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef,
    show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]
  exact hy

variable {F : Type} [Field F] [NumberField F]

def sP (z : Hn F) : ℝ := ∏ v, sF (z v)

lemma one_le_sP (z : Hn F) : 1 ≤ sP z := by
  calc (1 : ℝ) = ∏ v, (1 : ℝ) := by simp
    _ ≤ ∏ v, sF (z v) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun v _ => one_le_sF _)

lemma sP_nonneg (z : Hn F) : 0 ≤ sP z := zero_le_one.trans (one_le_sP z)

lemma gr_iff (f : Hn F → ℂ) : Gr f ↔ ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * sP z ^ A := by
  rw [Gr.eq_1]
  constructor
  · rintro ⟨C, A, hC⟩
    refine ⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)
  · rintro ⟨C, A, -, hC⟩
    exact ⟨C, A, hC⟩

lemma gr_add {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f + g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩
  have hP := one_le_sP z
  have e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  have e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * sP z ^ A1 + C2 * sP z ^ A2 := add_le_add (h1 z) (h2 z)
    _ ≤ C1 * sP z ^ (A1 + A2) + C2 * sP z ^ (A1 + A2) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
    _ = (C1 + C2) * sP z ^ (A1 + A2) := by ring

lemma gr_mul {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f * g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * sP z ^ A1) * (C2 * sP z ^ A2) :=
      mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg (sP_nonneg z) _))
    _ = C1 * C2 * sP z ^ (A1 + A2) := by ring

lemma gr_const (c : ℂ) : Gr (fun _ : Hn F => c) := by
  rw [gr_iff]
  exact ⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩

lemma gr_smul (c : ℂ) {f : Hn F → ℂ} (hf : Gr f) : Gr (c • f) := gr_mul (gr_const c) hf

lemma gr_act (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (fun z => f (act h z)) := by
  rw [gr_iff] at hf ⊢
  obtain ⟨C, A, hC, hfz⟩ := hf
  choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)
  have hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z := by
    intro z
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      exact sF_nonneg _
    · intro v _
      rw [act.eq_1]
      exact hK v (z v)
  refine ⟨C * (∏ v, K v) ^ A, A,
    mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩
  calc ‖f (act h z)‖ ≤ C * sP (act h z) ^ A := hfz _
    _ ≤ C * ((∏ v, K v) * sP z) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sP_nonneg _) (hact z) A) hC
    _ = C * (∏ v, K v) ^ A * sP z ^ A := by ring

lemma gr_denom (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    Gr (fun z : Hn F => (∏ v, denom (GlobalTheory.HilbertThetaSeries.cmp v h) (z v))⁻¹ ^ k) := by
  rw [gr_iff]
  choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)
  refine ⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩
  have hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z := by
    rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      positivity
    · intro v _
      exact hK v (z v)
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb k

lemma hilbertModerateGrowth_unnormalizedSlash (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl0 k h f) :=
  gr_mul (gr_denom k h) (gr_act h hf)

lemma gr_sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl k h f) :=
  gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)

theorem gr_closed : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Gr f → Gr g → Gr (f + g) ∧ Gr (c • f) ∧ Gr (f * g) ∧ Gr (1 : Hn F → ℂ) ∧ Gr (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Gr (sl0 k h f) ∧ Gr (sl k h f) :=
  fun _ _ _ k _ _ c hf hg =>
    ⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩

end GlobalTheory.HilbertThetaSeries.Growth
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashEvalSmoothWeightLowering
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries.ArchLift

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

noncomputable def arch {ι : Type} [Fintype ι] (k : ℕ) (g : (ι → ℂ) → ℂ) (x : Fin 2 → Fin 2 → ι → ℝ) : ℂ :=
  (((∏ v, (x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v)) ^ ((k : ℝ) / 2) : ℝ) : ℂ) *
    (∏ v, ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)) ^ (-(k : ℤ)) *
      g fun v => ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹

theorem den_ne {a b c d : ℝ} (h : 0 < a * d - b * c) : (c : ℂ) * Complex.I + d ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simp at h1 h2
  simp [h1, h2] at h

theorem im_pos' {a b c d : ℝ} (h : 0 < a * d - b * c) :
    0 < (((a : ℂ) * Complex.I + b) * ((c : ℂ) * Complex.I + d)⁻¹).im := by
  have h1 := Complex.normSq_pos.2 (den_ne h)
  have : (((a : ℂ) * Complex.I + b) * ((c : ℂ) * Complex.I + d)⁻¹).im =
      (a * d - b * c) / Complex.normSq ((c : ℂ) * Complex.I + d) := by
    rw [← div_eq_mul_inv, Complex.div_im]
    simp
    ring
  rw [this]
  positivity

theorem isOpen_up {ι : Type} [Fintype ι] : IsOpen {z : ι → ℂ | ∀ v, 0 < (z v).im} := by
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)

theorem arch_smooth {ι : Type} [Fintype ι] (k : ℕ) (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g {z | ∀ v, 0 < (z v).im}) (x : Fin 2 → Fin 2 → ι → ℝ)
    (hx : ∀ v, 0 < x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (arch k g) x := by
  have r : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => x i j v) x := by
    intro i j v; fun_prop
  have c : ∀ i j v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ => (x i j v : ℂ)) x :=
    fun i j v => Complex.ofRealCLM.contDiff.contDiffAt.comp x (r i j v)
  have hden : ∀ v, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin 2 → Fin 2 → ι → ℝ => (x 1 0 v : ℂ) * Complex.I + x 1 1 v) x :=
    fun v => ((c 1 0 v).mul contDiffAt_const).add (c 1 1 v)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ =>
      (∏ v, (x 0 0 v * x 1 1 v - x 0 1 v * x 1 0 v)) ^ ((k : ℝ) / 2)) x :=
    (contDiffAt_prod fun v _ => ((r 0 0 v).mul (r 1 1 v)).sub ((r 0 1 v).mul (r 1 0 v))).rpow_const_of_ne
      (Finset.prod_pos fun v _ => hx v).ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Fin 2 → Fin 2 → ι → ℝ =>
      (∏ v, ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)) ^ (-(k : ℤ))) x := by
    simp only [zpow_neg, zpow_natCast]
    exact ((contDiffAt_prod fun v _ => hden v).pow k).inv
      (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun v _ => den_ne (hx v)))
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun (x : Fin 2 → Fin 2 → ι → ℝ) (v : ι) =>
      ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹) x :=
    contDiffAt_pi.2 fun v => (((c 0 0 v).mul contDiffAt_const).add (c 0 1 v)).mul ((hden v).inv (den_ne (hx v)))
  have h4 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (fun v : ι =>
      ((x 0 0 v : ℂ) * Complex.I + x 0 1 v) * ((x 1 0 v : ℂ) * Complex.I + x 1 1 v)⁻¹) :=
    ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_up hg _ (fun v => im_pos' (hx v))).contDiffAt).restrict_scalars ℝ
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp x h1).mul h2).mul (h4.comp x h3)

theorem arch_der {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g {z | ∀ v, 0 < (z v).im}) (v : ι) :
    ∃ F' : ℂ, ∀ y : Fin 2 → Fin 2 → ℝ,
      fderiv ℝ (arch k g) (Matrix.of.symm 1) (fun i j => Pi.single v (y i j)) =
        (k : ℂ) / 2 * (y 0 0 + y 1 1) * g (fun _ => Complex.I) - k * (y 1 0 * Complex.I + y 1 1) * g (fun _ => Complex.I) +
        (y 0 0 * Complex.I + y 0 1 + y 1 0 - y 1 1 * Complex.I) * F' := by
  set x1 : Fin 2 → Fin 2 → ι → ℝ := Matrix.of.symm 1 with hx1
  set y1 : Fin 2 → Fin 2 → ℝ := Matrix.of.symm 1 with hy1
  have hgI : DifferentiableAt ℂ g (Function.update (fun _ => Complex.I) v Complex.I) := by
    rw [Function.update_eq_self_iff.2 rfl]
    exact hg.differentiableAt (isOpen_up.mem_nhds fun _ => by simp)
  have hF : DifferentiableAt ℂ (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I :=
    hgI.comp Complex.I (hasFDerivAt_update _ _).differentiableAt
  obtain ⟨L, hL, hv⟩ := key k _ _ hF.hasDerivAt y1 (by simp [hy1]) (by simp [hy1]) (by simp [hy1]) (by simp [hy1])
  let S : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ι → ℝ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
      (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) v).comp (cR i j)
  have hS : ∀ y, S y = fun i j => Pi.single v (y i j) := fun y => rfl
  let e : (Fin 2 → Fin 2 → ℝ) → (Fin 2 → Fin 2 → ι → ℝ) := fun y => S y + (x1 - S y1)
  have he : HasFDerivAt e S y1 := S.hasFDerivAt.add_const _
  have he1 : e y1 = x1 := by simp [e]
  have hev : ∀ y i j, e y i j v = y i j := by
    intro y i j
    fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1]
  have hew : ∀ y i j w, w ≠ v → e y i j w = y1 i j := by
    intro y i j w hw
    fin_cases i <;> fin_cases j <;> simp [e, hS, hx1, hy1, hw]
  have hA : DifferentiableAt ℝ (arch k g) (e y1) := by
    rw [he1]
    exact (arch_smooth k g hg x1 (by simp [hx1])).differentiableAt (by simp)
  have hc := hA.hasFDerivAt.comp y1 he
  have heq : arch k g ∘ e = fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          g (Function.update (fun _ => Complex.I) v
            (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) := by
    funext y
    simp only [Function.comp, arch]
    rw [Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp),
      Finset.prod_eq_single v (fun w _ hw => by simp [hew y _ _ w hw, hy1]) (by simp)]
    simp only [hev]
    congr 2
    funext w
    by_cases hw : w = v
    · subst hw
      simp [hev]
    · simp [hew y _ _ w hw, hy1, hw]
  rw [heq, he1] at hc
  refine ⟨deriv (fun z => g (Function.update (fun _ => Complex.I) v z)) Complex.I, fun y => ?_⟩
  have := hv y
  rw [hL.unique hc, Function.update_eq_self_iff.2 rfl] at this
  exact this

end GlobalTheory.HilbertThetaSeries.ArchLift

theorem GlobalTheory.HilbertThetaSeries.arch_lift : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)] (k : ℕ) (f : Hn F → ℂ), Hol f → ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ, (∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A {x | ∀ v, 0 < (Matrix.of x).det v} ∧ ∀ v, ∀ D : Fin 2 → Fin 2 → ℂ, (∀ i j, D i j = fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single i j (Pi.single v 1)))) → D 0 1 - D 1 0 = Complex.I * k * f (fun _ => UpperHalfPlane.I) ∧ D 0 0 - D 1 1 = Complex.I * (D 0 1 + D 1 0) := by
  intro F _ _ _ k f hf
  refine ⟨ArchLift.arch k fun z => f fun v => ofComplex (z v), fun h hh => ?_, fun x hx => ?_, fun v D hD => ?_⟩
  · have hp : ∀ v, 0 < h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v := fun v => by
      simpa [Matrix.det_fin_two] using hh v
    have hz : (fun v => ofComplex (((h.val 0 0 v : ℂ) * Complex.I + h.val 0 1 v) *
        ((h.val 1 0 v : ℂ) * Complex.I + h.val 1 1 v)⁻¹)) = act h fun _ => UpperHalfPlane.I := by
      funext v
      have hd : 0 < (GlobalTheory.HilbertThetaSeries.cmp v h).det.val := by
        simpa [GlobalTheory.HilbertThetaSeries.cmp, Matrix.det_fin_two] using hp v
      rw [← ofComplex_apply (act h (fun _ => UpperHalfPlane.I) v), act, coe_smul_of_det_pos hd]
      simp [num, denom, GlobalTheory.HilbertThetaSeries.cmp, div_eq_mul_inv]
    have ha : ∀ v, |h.val.det v| = h.val 0 0 v * h.val 1 1 v - h.val 0 1 v * h.val 1 0 v := fun v => by
      rw [abs_of_pos (hh v)]; simp [Matrix.det_fin_two]
    simp only [ArchLift.arch, sl, sl0, Matrix.of_symm_apply, hz, ha, mul_assoc, zpow_neg, zpow_natCast, inv_pow]
    simp [denom, GlobalTheory.HilbertThetaSeries.cmp]
  · exact (ArchLift.arch_smooth k _ hf x fun v => by simpa [Matrix.det_fin_two] using hx v).contDiffWithinAt
  · obtain ⟨F', hF⟩ := ArchLift.arch_der k _ hf v
    have hE : ∀ i j : Fin 2, (Matrix.of.symm (Matrix.single i j (Pi.single v (1 : ℝ))) :
        Fin 2 → Fin 2 → InfinitePlace F → ℝ) = fun a b => Pi.single v (Matrix.single i j (1 : ℝ) a b) := by
      intro i j
      funext a b
      simp only [Matrix.single, Matrix.of_symm_apply, Matrix.of_apply]
      split_ifs <;> simp
    have hI : ofComplex Complex.I = UpperHalfPlane.I := by
      rw [← coe_I, ofComplex_apply]
    have hD' := fun i j => (hD i j).trans ((congrArg _ (hE i j)).trans (hF fun a b => Matrix.single i j (1 : ℝ) a b))
    simp only [hD', hI]
    simp [Matrix.single]
    refine ⟨Or.inl (mul_comm _ _), ?_⟩
    linear_combination (k * f fun _ => UpperHalfPlane.I) * Complex.I_mul_I

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_slash_eval_smooth_weight_lowering : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)] (k : ℕ) (f : Hn F → ℂ), Hol f → ∃ A : (Fin 2 → Fin 2 → InfinitePlace F → ℝ) → ℂ, (∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → A (Matrix.of.symm h.val) = sl k h f fun _ => UpperHalfPlane.I) ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A {x | ∀ v, 0 < (Matrix.of x).det v} ∧ ∀ v, ∀ D : Fin 2 → Fin 2 → ℂ, (∀ i j, D i j = fderiv ℝ A (Matrix.of.symm 1) (Matrix.of.symm (Matrix.single i j (Pi.single v 1)))) → D 0 1 - D 1 0 = Complex.I * k * f (fun _ => UpperHalfPlane.I) ∧ D 0 0 - D 1 1 = Complex.I * (D 0 1 + D 1 0) := by
  first | exact @GlobalTheory.HilbertThetaSeries.arch_lift | exact GlobalTheory.HilbertThetaSeries.arch_lift | (intros; apply GlobalTheory.HilbertThetaSeries.arch_lift <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SlashCocycle

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

theorem cmp_det (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v) _).symm

theorem det_mul_apply (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v * (h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [← cmp_det, ← cmp_det, ← cmp_det, map_mul, map_mul, Units.val_mul]

theorem det_inv_apply (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      ((h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v)⁻¹ := by
  rw [← cmp_det, ← cmp_det, map_inv, map_inv, Units.val_inv_eq_inv_val]

theorem denom_cmp_mul (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (z : ℍ) :
    denom (cmp v h * cmp v h') z = denom (cmp v h) ((cmp v h' • z : ℍ) : ℂ) * denom (cmp v h') z := by
  have hp : 0 < ((cmp v h').det : ℝ) := by rw [cmp_det]; exact hh' v
  rw [denom_cocycle_σ, σ, if_pos hp]
  rfl

theorem act_mul (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (z : Hn F) : act (h * h') z = act h (act h' z) := by
  funext v
  simp only [act, map_mul]
  exact mul_smul _ _ _

theorem act_one (z : Hn F) : act (1 : GL (Fin 2) (InfinitePlace F → ℝ)) z = z := by
  funext v
  simp only [act, map_one]
  exact one_smul _ _

theorem hilbertSlashUnnormalized_mul (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (f : Hn F → ℂ) :
    sl0 k (h * h') f = sl0 k h' (sl0 k h f) := by
  funext z
  simp only [sl0, act_mul, map_mul]
  simp only [act, denom_cmp_mul _ h h' hh', Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

theorem hilbertSlashUnnormalized_one (k : ℕ) (f : Hn F → ℂ) : sl0 k 1 f = f := by
  funext z
  simp [sl0, act_one, denom_one]

theorem hilbertSlashUnnormalized_const_mul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (c : ℂ) (f : Hn F → ℂ) (z : Hn F) :
    sl0 k h (fun w => c * f w) z = c * sl0 k h f z := by
  simp only [sl0]; ring

theorem slash_cocycle : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (f : Hn F → ℂ), Pos h → Pos h' → Pos (h * h') ∧ Pos h⁻¹ ∧ sl0 k (h * h') f = sl0 k h' (sl0 k h f) ∧ sl k (h * h') f = sl k h' (sl k h f) ∧ sl0 k 1 f = f ∧ sl k 1 f = f := by
  intro F _ _ k h h' f hh hh'
  refine ⟨fun v => ?_, fun v => ?_, hilbertSlashUnnormalized_mul k h h' hh' f, ?_, hilbertSlashUnnormalized_one k f, ?_⟩
  · rw [det_mul_apply]; exact mul_pos (hh v) (hh' v)
  · rw [det_inv_apply]; exact inv_pos.mpr (hh v)
  · funext z
    have hprod : (∏ v, |((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) =
        (∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) *
          ∏ v, |(h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
      simp only [det_mul_apply, abs_mul, Finset.prod_mul_distrib]
    have hsl : sl k h f = fun w => ((((∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) * sl0 k h f w := rfl
    simp only [sl]
    rw [hsl, hilbertSlashUnnormalized_const_mul, hilbertSlashUnnormalized_mul k h h' hh' f, hprod,
      Real.mul_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _) (Finset.prod_nonneg fun v _ => abs_nonneg _)]
    push_cast
    ring
  · funext z
    simp [sl, hilbertSlashUnnormalized_one]

end GlobalTheory.HilbertThetaSeries.SlashCocycle
end

