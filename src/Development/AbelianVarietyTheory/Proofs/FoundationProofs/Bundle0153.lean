module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Formalism.DirichletDensity.DirichletDensityProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableQExpansionOfCoeffPolynomialGrowth
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

private lemma summable_poly_mul_geometric (C : ℝ) (A : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ A * r ^ n := by
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have h := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one A hr : Summable fun m : ℕ => (m : ℝ) ^ A * r ^ m)
  refine (h.mul_left (C * r⁻¹)).congr fun n => ?_
  have hr' : r ≠ 0 := hr0.ne'
  push_cast
  rw [pow_succ]
  field_simp

private lemma qs_term_bound (a : ℕ → ℂ) (C : ℝ) (A : ℕ) (hC : ∀ n : ℕ, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ A)
    (y0 : ℝ) (n : ℕ) (w : ℂ) (hw : y0 < w.im) :
    ‖a n * cexp (2 * π * Complex.I * n * w)‖ ≤ C * ((n : ℝ) + 1) ^ A * Real.exp (-(2 * π * y0)) ^ n := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (2 * π * Complex.I * n * w).re = -(2 * π * n * w.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hexp : Real.exp (-(2 * π * n * w.im)) ≤ Real.exp (-(2 * π * y0)) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hp : (0:ℝ) ≤ 2 * π * n := by positivity
    have := mul_le_mul_of_nonneg_left hw.le hp
    nlinarith
  exact mul_le_mul (hC n) hexp (Real.exp_pos _).le (le_trans (norm_nonneg _) (hC n))

theorem qs_mdifferentiable : ∀ a : ℕ → ℂ, PolyB a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (qs a) := by
  rintro a ⟨C, A, hC⟩
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have hz' : 0 < z.im := hz
  set y0 := z.im / 2 with hy0def
  have hy0 : 0 < y0 := by positivity
  set U : Set ℂ := {w | y0 < w.im} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hzU : z ∈ U := by
    show y0 < z.im
    linarith
  have hr0 : 0 < Real.exp (-(2 * π * y0)) := Real.exp_pos _
  have hr1 : Real.exp (-(2 * π * y0)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have := Real.pi_pos
    nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * n * w)) U :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_poly_mul_geometric C A hr0 hr1)
      (fun n => (by fun_prop : Differentiable ℂ fun w : ℂ => a n * cexp (2 * π * Complex.I * n * w)).differentiableOn)
      hU (fun n w hw => qs_term_bound a C A hC y0 n w hw)
  have hDz := (hD z hzU).differentiableAt (hU.mem_nhds hzU)
  apply DifferentiableAt.differentiableWithinAt
  apply hDz.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  have hw' : 0 < w.im := lt_trans hy0 hw
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  rfl

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqEqOfPosCoeffEq
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma summable_norm_qterm_of_polyB (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r : ℝ := Real.exp (-2 * π * τ.im) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero, Real.exp_lt_exp]
    have := τ.im_pos
    nlinarith [Real.pi_pos]
  have hnorm : ∀ n : ℕ, ‖cexp (2 * π * Complex.I * n * τ)‖ = r ^ n := by
    intro n
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hg : Summable fun n : ℕ => ((n : ℝ) + 1) ^ A * r ^ n := by
    have h0 : Summable fun n : ℕ => (n : ℝ) ^ A * r ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr fun n => ?_
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg.mul_left C)
  rw [norm_mul, hnorm n, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg hr0.le n)

end GlobalTheory.EisM

namespace GlobalTheory.EisM

lemma qs_sub_eq_const (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) (hab : ∀ n, n ≠ 0 → a n = b n) (τ : ℍ) :
    qs a τ - qs b τ = a 0 - b 0 := by
  unfold qs
  rw [← (summable_norm_qterm_of_polyB a ha τ).of_norm.tsum_sub (summable_norm_qterm_of_polyB b hb τ).of_norm]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    rw [hab n hn, sub_self]

theorem eq_of_coeff_pos_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b →
    (∀ n, n ≠ 0 → a n = b n) → a = b := by
  intro k L χ a b hk hL ha hb hab
  set c : ℂ := a 0 - b 0 with hc
  have hconst := qs_sub_eq_const a b ha.1 hb.1 hab
  let γ : SL(2, ℤ) := ⟨!![1, 0; (L : ℤ), 1], by simp [Matrix.det_fin_two]⟩
  have hγ10 : γ 1 0 = (L : ℤ) := rfl
  have hγ11 : γ 1 1 = 1 := rfl
  have key : ∀ τ : ℍ, c = χ 1 * ((L : ℂ) * τ + 1) ^ k * c := by
    intro τ
    have h1 := ha.2 γ (by rw [hγ10]) τ
    have h2 := hb.2 γ (by rw [hγ10]) τ
    rw [hγ10, hγ11] at h1 h2
    have e1 := hconst (γ • τ)
    rw [h1, h2, ← mul_sub, hconst τ, ← hc] at e1
    push_cast at e1
    exact e1.symm
  by_contra hne
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · exact sub_eq_zero.mp h0
    · exact hab n hn
  have hone : ∀ τ : ℍ, ‖χ 1‖ * ‖(L : ℂ) * τ + 1‖ ^ k = 1 := by
    intro τ
    have h := key τ
    have h' : χ 1 * ((L : ℂ) * τ + 1) ^ k = 1 := by
      have : (χ 1 * ((L : ℂ) * τ + 1) ^ k - 1) * c = 0 := by rw [sub_mul, ← h]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc0)
    rw [← norm_pow, ← norm_mul, h', norm_one]
  let τ₁ : ℍ := ⟨Complex.I, by simp⟩
  let τ₂ : ℍ := ⟨2 * Complex.I, by simp⟩
  have e1 := hone τ₁
  have e2 := hone τ₂
  have hχ : ‖χ 1‖ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact zero_ne_one e1
  have heq : ‖(L : ℂ) * τ₁ + 1‖ ^ k = ‖(L : ℂ) * τ₂ + 1‖ ^ k :=
    mul_left_cancel₀ hχ (e1.trans e2.symm)
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : ‖(L : ℂ) * τ₁ + 1‖ < ‖(L : ℂ) * τ₂ + 1‖ := by
    have s1 : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 = 1 + (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₁, UpperHalfPlane.coe_mk]
      ring
    have s2 : ‖(L : ℂ) * τ₂ + 1‖ ^ 2 = 1 + 4 * (L : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [τ₂, UpperHalfPlane.coe_mk]
      ring
    have : ‖(L : ℂ) * τ₁ + 1‖ ^ 2 < ‖(L : ℂ) * τ₂ + 1‖ ^ 2 := by
      rw [s1, s2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have := pow_lt_pow_left₀ hlt (norm_nonneg _) (by omega : k ≠ 0)
  exact absurd heq (ne_of_lt this)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructure
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.Lin

theorem norm_term (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = (Real.exp (-2 * π * τ.im)) ^ n := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem summ_norm (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => ‖a n * cexp (2 * π * Complex.I * n * τ)‖ := by
  obtain ⟨C, A, hC⟩ := ha
  set r := Real.exp (-2 * π * τ.im) with hr
  have r0 : 0 < r := Real.exp_pos _
  have r1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have := τ.im_pos
    have := Real.pi_pos
    nlinarith
  have hs : Summable fun n : ℕ => ((n : ℝ)) ^ A * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one A (by rw [Real.norm_eq_abs, abs_of_pos r0]; exact r1)
  have hs1 : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ A * r ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun n : ℕ => C * (((n : ℝ) + 1) ^ A * r ^ n) := by
    apply Summable.mul_left
    have := hs1.mul_right r⁻¹
    refine this.congr (fun n => ?_)
    push_cast
    rw [pow_succ]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs2
  rw [norm_mul, norm_term, ← hr, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC n) (pow_nonneg r0.le _)

theorem summ (a : ℕ → ℂ) (ha : PolyB a) (τ : ℍ) :
    Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
  (summ_norm a ha τ).of_norm

theorem polyB_zero : PolyB (0 : ℕ → ℂ) := ⟨0, 0, fun n => by simp⟩

theorem polyB_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : PolyB (a + b) := by
  obtain ⟨C, A, hC⟩ := ha
  obtain ⟨D, B, hD⟩ := hb
  refine ⟨|C| + |D|, A + B, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have hA : ((n : ℝ) + 1) ^ A ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have hB : ((n : ℝ) + 1) ^ B ≤ ((n : ℝ) + 1) ^ (A + B) := pow_le_pow_right₀ h1 (by omega)
  have p0 : 0 ≤ ((n : ℝ) + 1) ^ A := by positivity
  have p1 : 0 ≤ ((n : ℝ) + 1) ^ B := by positivity
  calc ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C * ((n : ℝ) + 1) ^ A + D * ((n : ℝ) + 1) ^ B := add_le_add (hC n) (hD n)
    _ ≤ |C| * ((n : ℝ) + 1) ^ (A + B) + |D| * ((n : ℝ) + 1) ^ (A + B) := by
        apply add_le_add
        · exact (mul_le_mul_of_nonneg_right (le_abs_self C) p0).trans
            (mul_le_mul_of_nonneg_left hA (abs_nonneg C))
        · exact (mul_le_mul_of_nonneg_right (le_abs_self D) p1).trans
            (mul_le_mul_of_nonneg_left hB (abs_nonneg D))
    _ = (|C| + |D|) * ((n : ℝ) + 1) ^ (A + B) := by ring

theorem polyB_smul (c : ℂ) (a : ℕ → ℂ) (ha : PolyB a) : PolyB (c • a) := by
  obtain ⟨C, A, hC⟩ := ha
  refine ⟨‖c‖ * C, A, fun n => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg c)

theorem qs_zero : qs (0 : ℕ → ℂ) = 0 := by
  funext τ; simp [qs]

theorem qs_add (a b : ℕ → ℂ) (ha : PolyB a) (hb : PolyB b) : qs (a + b) = qs a + qs b := by
  funext τ
  simp only [qs, Pi.add_apply, add_mul]
  exact (summ a ha τ).tsum_add (summ b hb τ)

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (c • a) = c • qs a := by
  funext τ
  simp only [qs, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem coprime_of_level (L : ℕ) (γ : SL(2, ℤ)) (h : (L : ℤ) ∣ γ 1 0) : IsCoprime (γ 1 1) (L : ℤ) := by
  obtain ⟨m, hm⟩ := h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨γ 0 0, -(γ 0 1 * m), ?_⟩
  rw [hm] at hdet
  linear_combination hdet

end GlobalTheory.EisM.Lin

open GlobalTheory.EisM.Lin in
theorem GlobalTheory.EisM.mf_linear : ∀ (k L : ℕ) (χ : ℤ → ℂ), (MF k L χ 0) ∧ (∀ a b, MF k L χ a → MF k L χ b → MF k L χ (a + b) ∧ qs (a + b) = qs a + qs b) ∧ (∀ (c : ℂ) a, MF k L χ a → MF k L χ (c • a) ∧ qs (c • a) = c • qs a) ∧ (∀ χ' a, (∀ d : ℤ, IsCoprime d L → χ d = χ' d) → MF k L χ a → MF k L χ' a) ∧ (∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a) ∧ (∀ L' a, L ∣ L' → CF k L χ a → CF k L' χ a) := by
  intro k L χ
  have lev : ∀ L' a, L ∣ L' → MF k L χ a → MF k L' χ a := by
    intro L' a hL ⟨hp, hi⟩
    refine ⟨hp, fun γ hγ τ => hi γ ?_ τ⟩
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hL) hγ
  refine ⟨⟨polyB_zero, fun γ _ τ => by simp [qs_zero]⟩, ?_, ?_, ?_, lev, ?_⟩
  · intro a b ⟨ha, ia⟩ ⟨hb, ib⟩
    have e := qs_add a b ha hb
    refine ⟨⟨polyB_add a b ha hb, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.add_apply, Pi.add_apply, ia γ hγ τ, ib γ hγ τ]
    ring
  · intro c a ⟨ha, ia⟩
    have e := qs_smul c a
    refine ⟨⟨polyB_smul c a ha, fun γ hγ τ => ?_⟩, e⟩
    rw [e, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ia γ hγ τ]
    ring
  · intro χ' a hχ ⟨ha, ia⟩
    refine ⟨ha, fun γ hγ τ => ?_⟩
    rw [ia γ hγ τ, hχ _ (coprime_of_level L γ hγ)]
  · intro L' a hL ⟨hm, hc⟩
    exact ⟨lev L' a hL hm, hc⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NotSummableInvPrimesCongrNegOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem sub_one_mul_log_div_rpow_le (n : ℕ) (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    (x - 1) * (Real.log n / (n : ℝ) ^ x) ≤ 1 / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have e : (n : ℝ) ^ x = (n : ℝ) ^ (x - 1) * n := by
    rw [Real.rpow_sub_one hp.ne' x]; field_simp
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hp _
  have hl : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    rw [Real.rpow_def_of_pos hp]
    have := Real.add_one_le_exp (Real.log n * (x - 1))
    nlinarith [this]
  have hrw : (x - 1) * (Real.log n / (n : ℝ) ^ x) =
      ((x - 1) * Real.log n / (n : ℝ) ^ (x - 1)) * (1 / n) := by
    rw [e]; field_simp
  rw [hrw]
  refine mul_le_of_le_one_left (by positivity) ((div_le_one hq).2 hl)

theorem not_summable_one_div_primes_eq_neg_one :
    ∀ M : ℕ, 0 < M → ¬ Summable fun p : ℕ =>
      if p.Prime ∧ (p : ZMod M) = -1 then (1 : ℝ) / p else 0 := by
  intro M hM hs
  haveI : NeZero M := ⟨hM.ne'⟩
  have hD := Formalism.HF.apLogDensity M (-1 : ZMod M) isUnit_one.neg
  unfold Formalism.HF.LogDensity at hD
  set S := {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod M) = -1}} with hS
  have h0 : Tendsto (fun x : ℝ => ∑' n : ℕ,
      (x - 1) * S.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) (𝓝[>] 1)
      (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun n => ?_) ?_
    · by_cases hn : n ∈ S
      · simp only [Set.indicator_of_mem hn]
        have hp : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
        have hc : Continuous fun x : ℝ => (x - 1) * (Real.log n / (n : ℝ) ^ x) := by
          refine (continuous_id.sub continuous_const).mul (continuous_const.div ?_ ?_)
          · exact continuous_const.rpow continuous_id (fun _ => Or.inl hp.ne')
          · intro x; exact (Real.rpow_pos_of_pos hp x).ne'
        have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
        simpa using this
      · simp only [Set.indicator_of_notMem hn, mul_zero]
        exact tendsto_const_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx n
      have hx : (1 : ℝ) < x := hx
      by_cases hn : n ∈ S
      · have hc : n.Prime ∧ (n : ZMod M) = -1 := hn
        simp only [Set.indicator_of_mem hn, if_pos hc]
        have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hc.1.one_lt.le)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith)
          (div_nonneg hlog (Real.rpow_nonneg n.cast_nonneg _)))]
        exact sub_one_mul_log_div_rpow_le n hc.1.one_lt hx
      · have hc : ¬ (n.Prime ∧ (n : ZMod M) = -1) := hn
        simp only [Set.indicator_of_notMem hn, if_neg hc, mul_zero, norm_zero, le_refl]
  simp only [tsum_zero, tsum_mul_left] at h0
  have hu := tendsto_nhds_unique hD h0
  have ht : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 hM
  rw [one_div] at hu
  exact (inv_pos.2 ht).ne' hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PSqSmulKaehlerMemSpan
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt

section Klc

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_eq_pow (T : Tower p Ω) (k j : ℕ) : zS T k = zS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.ζpow (k + j)).symm

theorem qS_eq_pow (T : Tower p Ω) (k j : ℕ) : qS T k = qS T (k + j) ^ (p ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, pow_succ' p j, pow_mul]
    congr 1
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    exact (T.qpow (k + j)).symm

theorem D_zS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [zS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem D_qS_mem_span (T : Tower p Ω) {k m : ℕ} (h : k ≤ m) :
    KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T k) ∈
      Submodule.span (integralClosure (O0 p) Ω)
        {KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m),
          KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m)} := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [qS_eq_pow T k j, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Klc


theorem p_sq_smul_kaehler_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (η : KaehlerDifferential (O0 p) (integralClosure (O0 p) Ω))
    (n : ℕ), ∃ m, n ≤ m ∧ ∃ x y : (integralClosure (O0 p) Ω), (p : (integralClosure (O0 p) Ω)) ^ 2 • η =
      x • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (zS T m) +
        y • KaehlerDifferential.D (O0 p) (integralClosure (O0 p) Ω) (qS T m) := by
  intro p _ Ω _ _ hp2 hclo T η n
  let 𝒮 := integralClosure (O0 p) Ω
  let 𝒟 := KaehlerDifferential.D (O0 p) 𝒮
  let N : ℕ → Submodule 𝒮 (KaehlerDifferential (O0 p) 𝒮) :=
    fun m => Submodule.span 𝒮 {𝒟 (zS T m), 𝒟 (qS T m)}
  have hmono : Monotone N := fun k m h => Submodule.span_le.2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [D_zS_mem_span T h, D_qS_mem_span T h])
  have hder : ∀ B : Subalgebra (O0 p) 𝒮, IsDerOn B (fun x => 𝒟 x) := fun B =>
    ⟨fun x _ y _ => map_add 𝒟 x y, fun x _ y _ => Derivation.leibniz 𝒟 x y,
      fun a => (𝒟).map_algebraMap a⟩
  have hgen : ∀ t : 𝒮, (p : 𝒮) ^ 2 • 𝒟 t ∈ ⨆ m, N m := by
    intro t
    obtain ⟨C, tr, k, a, b, hF, htr⟩ := _root_.GlobalTheory.AlmostEt.TrTower.exists_trData_towerAlg p Ω hp2 hclo T {t}
    have h1 := _root_.GlobalTheory.AlmostEt.derOn_mem_span_of_trData (O0 p) 𝒮 _ (towerAlg T) C tr k a b _ htr (fun x => 𝒟 x) (hder C) t
      (hF (by simp))
    have h2 : Submodule.span 𝒮 ((fun x => 𝒟 x) '' (towerAlg T : Set 𝒮)) ≤ ⨆ m, N m := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have h3 := _root_.GlobalTheory.AlmostEt.derOn_adjoin_mem_span (O0 p) 𝒮 _ (Set.range (zS T) ∪ Set.range (qS T)) (fun x => 𝒟 x)
        (hder _) x hx
      refine Submodule.span_le.2 ?_ h3
      rintro _ ⟨y, (⟨k, rfl⟩ | ⟨k, rfl⟩), rfl⟩
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
      · exact Submodule.mem_iSup_of_mem k (Submodule.subset_span (by simp))
    rw [pow_two]
    exact h2 h1
  have hall : ∀ ω ∈ Submodule.span 𝒮 (Set.range 𝒟), (p : 𝒮) ^ 2 • ω ∈ ⨆ m, N m := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hgen t
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx
  have hη : (p : 𝒮) ^ 2 • η ∈ ⨆ m, N m :=
    hall η (by rw [KaehlerDifferential.span_range_derivation]; trivial)
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed N hmono.directed_le).1 hη
  refine ⟨max m n, le_max_right _ _, ?_⟩
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.1 (hmono (le_max_left m n) hm)
  exact ⟨x, y, hxy.symm⟩

end GlobalTheory.AlmostEt
end

