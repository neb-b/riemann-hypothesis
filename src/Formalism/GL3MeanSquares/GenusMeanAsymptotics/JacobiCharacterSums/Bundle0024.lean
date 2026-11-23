module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0019

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_phi_hasDerivAt (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := by
  have h1 : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w) ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1) 1 :=
    (hasDerivAt_id' (1 : ℂ)).const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have h2 := h1.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have e : ((y : ℂ) ^ (1 : ℂ) * Complex.log y * 1 * 1 - (y : ℂ) ^ (1 : ℂ) * 1) / 1 ^ 2 =
      (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [Complex.cpow_one, ← Complex.ofReal_log hy.le]
    ring
  exact h2.congr_deriv e

theorem ex_phi_differentiableOn (y : ℝ) (hy : 0 < y) :
    DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  exact ((differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hy.ne'))).div differentiableAt_id hw0).differentiableWithinAt

theorem ex_rect_double (y : ℝ) (hy : 0 < y) (x₀ x₁ y₀ y₁ : ℝ) (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    Formalism.ZF.rectInt (fun w => exKer y w / (w - 1)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * ((y : ℂ) * (Real.log y : ℂ) - y) := by
  have hb : HasDerivAt (fun w : ℂ => (y : ℂ) ^ w / w) ((y : ℂ) * (Real.log y : ℂ) - y) 1 := ex_phi_hasDerivAt y hy
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1U : {w : ℂ | 0 < w.re} ∈ nhds (1 : ℂ) := hU.mem_nhds (by simp)
  have hφd : DifferentiableOn ℂ (fun w : ℂ => (y : ℂ) ^ w / w) {w : ℂ | 0 < w.re} := ex_phi_differentiableOn y hy
  have hG : DifferentiableOn ℂ (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) {w : ℂ | 0 < w.re} :=
    (differentiableOn_dslope h1U).2 ((differentiableOn_dslope h1U).2 hφd)
  have hd1 : dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1 1 = (y : ℂ) * (Real.log y : ℂ) - y := by
    rw [dslope_same, hb.deriv]
  refine Formalism.ZF.rectangle_double_pole (fun w => exKer y w / (w - 1))
    (dslope (dslope (fun w : ℂ => (y : ℂ) ^ w / w) 1) 1) (y : ℂ) ((y : ℂ) * (Real.log y : ℂ) - y) 1 x₀ x₁ y₀ y₁
    (by simpa using hx₀1) (by simpa using hx₁) (by simpa using hy₀) (by simpa using hy₁)
    ⟨{w : ℂ | 0 < w.re}, hU, ?_, hG⟩ ?_
  · intro z hz
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hz
    show 0 < z.re
    linarith [hz.1.1]
  · intro w hw
    have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    rw [dslope_of_ne _ hw, slope_def_field, dslope_of_ne _ hw, slope_def_field, hd1]
    simp only [exKer, Complex.cpow_one, div_one]
    by_cases h0 : w = 0
    · subst h0
      simp
      ring
    · field_simp
      ring

def exBdry (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {w : ℂ | x₀ ≤ w.re ∧ w.re ≤ x₁ ∧ y₀ ≤ w.im ∧ w.im ≤ y₁ ∧
    (w.re = x₀ ∨ w.re = x₁ ∨ w.im = y₀ ∨ w.im = y₁)}

theorem ex_mem_horiz {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = y₀ ∨ c = y₁) {x : ℝ}
    (h : x ∈ Set.uIcc x₀ x₁) : ((x : ℂ) + c * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hx] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : y₀ ≤ c ∧ c ≤ y₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using h1, by simpa using h2, by simpa using hc'.1, by simpa using hc'.2, ?_⟩
  right; right
  simpa using hc

theorem ex_mem_vert {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) {c : ℝ} (hc : c = x₀ ∨ c = x₁) {t : ℝ}
    (h : t ∈ Set.uIcc y₀ y₁) : ((c : ℂ) + t * I) ∈ exBdry x₀ x₁ y₀ y₁ := by
  rw [Set.uIcc_of_le hy] at h
  obtain ⟨h1, h2⟩ := h
  have hc' : x₀ ≤ c ∧ c ≤ x₁ := by
    rcases hc with rfl | rfl <;> constructor <;> linarith
  refine ⟨by simpa using hc'.1, by simpa using hc'.2, by simpa using h1, by simpa using h2, ?_⟩
  rcases hc with hc | hc
  · left
    simpa using hc
  · right; left
    simpa using hc

theorem ex_rectInt_congr {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ w ∈ exBdry x₀ x₁ y₀ y₁, f w = g w) :
    Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ = Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  have hh : ∀ c : ℝ, (c = y₀ ∨ c = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + c * I)) = ∫ x : ℝ in x₀..x₁, g (x + c * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun x hx' => h _ (ex_mem_horiz hx hy hc hx')
  have hv : ∀ c : ℝ, (c = x₀ ∨ c = x₁) →
      (∫ t : ℝ in y₀..y₁, f (c + t * I)) = ∫ t : ℝ in y₀..y₁, g (c + t * I) := by
    intro c hc
    exact intervalIntegral.integral_congr fun t ht => h _ (ex_mem_vert hx hy hc ht)
  unfold Formalism.ZF.rectInt
  rw [hh y₀ (Or.inl rfl), hh y₁ (Or.inr rfl), hv x₀ (Or.inl rfl), hv x₁ (Or.inr rfl)]

theorem ex_ii_horiz {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = y₀ ∨ c = y₁) :
    IntervalIntegrable (fun x : ℝ => f (x + c * I)) MeasureTheory.volume x₀ x₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + c * I).continuousOn
    fun x hx' => ex_mem_horiz hx hy hc hx'

theorem ex_ii_vert {f : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) {c : ℝ} (hc : c = x₀ ∨ c = x₁) :
    IntervalIntegrable (fun t : ℝ => f (c + t * I)) MeasureTheory.volume y₀ y₁ := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).continuousOn
    fun t ht => ex_mem_vert hx hy hc ht

theorem ex_rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by
  unfold Formalism.ZF.rectInt
  rw [intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inl rfl)) (ex_ii_horiz hx hy hg (Or.inl rfl)),
    intervalIntegral.integral_add (ex_ii_horiz hx hy hf (Or.inr rfl)) (ex_ii_horiz hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inr rfl)) (ex_ii_vert hx hy hg (Or.inr rfl)),
    intervalIntegral.integral_add (ex_ii_vert hx hy hf (Or.inl rfl)) (ex_ii_vert hx hy hg (Or.inl rfl))]
  ring

theorem exKer_continuousAt (y : ℝ) (hy : 0 < y) {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    ContinuousAt (exKer y) w := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  unfold exKer
  apply ContinuousAt.div₀
  · exact continuousAt_const_cpow hy0
  · fun_prop
  · exact mul_ne_zero h0 (sub_ne_zero.mpr h1)

theorem ex_bdry_ne {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  constructor
  · rintro rfl
    simp at h1
    linarith
  · rintro rfl
    simp at h5
    rcases h5 with h | h | h | h <;> linarith

private theorem neg_div_mul_eq_neg_add_div_mul_add_div (a b K u : ℂ) (ha : a ≠ 0) (hu : u ≠ 0) :
    -(b / a) * K = -((1 * a + u * b) / (u * a)) * K + K / u := by
  field_simp
  ring

set_option maxHeartbeats 800000 in
theorem ex_rect_Fchi {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y : ℝ) (hy : 0 < y) (σ₁ σ₀ T' : ℝ)
    (hσ₁ : 0 < σ₁) (hσ₁1 : σ₁ < 1) (hσ₀ : 1 < σ₀) (hT' : 0 < T')
    (Z : Finset ℂ) (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T'))
    (hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T') :
    Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T') T' =
      2 * Real.pi * I * (explicitFormulaConstant χ * y + (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) -
        ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) := by
  have hfd : Differentiable ℂ (exLF χ) := exLF_differentiable χ
  have hx : σ₁ ≤ σ₀ := by linarith
  have hyy : -T' ≤ T' := by linarith
  have hZ' : ∀ ρ : ℂ, ρ ∈ Z ↔ exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ ρ.re < σ₀ ∧ -T' < ρ.im ∧ ρ.im < T' := by
    intro ρ
    rw [hZ ρ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have := exLF_re_lt_one χ h0
      exact ⟨h0, h1, by linarith, (abs_lt.mp h2).1, (abs_lt.mp h2).2⟩
    · rintro ⟨h0, h1, -, h3, h4⟩
      exact ⟨h0, h1, abs_lt.mpr ⟨h3, h4⟩⟩
  have hedge' : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → -T' ≤ w.im → w.im ≤ T' → exLF χ w = 0 →
      σ₁ < w.re ∧ w.re < σ₀ ∧ -T' < w.im ∧ w.im < T' := by
    intro w h1 h2 h3 h4 h0
    obtain ⟨h5, h6⟩ := hedge w h1 h2 (abs_le.mpr ⟨h3, h4⟩) h0
    have := exLF_re_lt_one χ h0
    exact ⟨h5, by linarith, (abs_lt.mp h6).1, (abs_lt.mp h6).2⟩
  have hmain := ex_rect_logDeriv (exLF χ) hfd (exLF_one_ne_zero χ) y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀
    (by linarith) hT' Z hZ' hedge'
  by_cases hχ : χ = 1
  · subst hχ
    have hbd : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', w ≠ 0 ∧ w ≠ 1 ∧ exLF (1 : DirichletCharacter ℂ M) w ≠ 0 := by
      intro w hw
      obtain ⟨h0, h1⟩ := ex_bdry_ne hσ₁ hσ₁1 hσ₀ (by linarith) hT' hw
      refine ⟨h0, h1, fun hfw => ?_⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hw
      obtain ⟨b1, b2, b3, b4⟩ := hedge' w a1 a2 a3 a4 hfw
      rcases a5 with h | h | h | h <;> linarith
    have hA : ContinuousOn (fun w => -(deriv (exLF (1 : DirichletCharacter ℂ M)) w /
        exLF (1 : DirichletCharacter ℂ M) w) * exKer y w) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hd : ContinuousAt (deriv (exLF (1 : DirichletCharacter ℂ M))) w :=
        (hfd.analyticAt w).deriv.continuousAt
      exact (((hd.div (hfd w).continuousAt h2).neg).mul (exKer_continuousAt y hy h0 h1)).continuousWithinAt
    have hK : ContinuousOn (fun w => exKer y w / (w - 1)) (exBdry σ₁ σ₀ (-T') T') := by
      intro w hw
      obtain ⟨h0, h1, -⟩ := hbd w hw
      have hs : ContinuousAt (fun s : ℂ => s - 1) w := continuousAt_id.sub continuousAt_const
      exact ((exKer_continuousAt y hy h0 h1).div hs (sub_ne_zero.mpr h1)).continuousWithinAt
    have hB : ∀ w ∈ exBdry σ₁ σ₀ (-T') T', Fchi (1 : DirichletCharacter ℂ M) y w =
        -(deriv (exLF (1 : DirichletCharacter ℂ M)) w / exLF (1 : DirichletCharacter ℂ M) w) * exKer y w +
          exKer y w / (w - 1) := by
      intro w hw
      obtain ⟨h0, h1, h2⟩ := hbd w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hfw : exLF (1 : DirichletCharacter ℂ M) w =
          (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := exLF_one_char_apply h1
      have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w ≠ 0 := by
        intro h
        apply h2
        rw [hfw, h, mul_zero]
      have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w :=
        DirichletCharacter.differentiableAt_LFunction 1 w (Or.inl h1)
      have hev : exLF (1 : DirichletCharacter ℂ M) =ᶠ[nhds w]
          fun s => (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s :=
        (eventually_ne_nhds h1).mono fun s hs => exLF_one_char_apply hs
      have hder : deriv (exLF (1 : DirichletCharacter ℂ M)) w =
          1 * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w +
            (w - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w := by
        rw [hev.deriv_eq]
        exact (((hasDerivAt_id' w).sub_const 1).mul hLd.hasDerivAt).deriv
      have e1 : Fchi (1 : DirichletCharacter ℂ M) y w =
          -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) w /
            DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w) * exKer y w := by
        simp only [Fchi, negLD, exKer, mul_div_assoc]
      rw [e1, hder, hfw]
      exact neg_div_mul_eq_neg_add_div_mul_add_div _ _ _ _ hL hw1
    rw [ex_rectInt_congr hx hyy hB, ex_rectInt_add hx hyy hA hK, hmain,
      ex_rect_double y hy σ₁ σ₀ (-T') T' hσ₁ hσ₁1 hσ₀ (by linarith) hT', if_pos rfl]
    simp only [explicitFormulaConstant, exOrd]
    ring
  · have hfL : exLF χ = DirichletCharacter.LFunction χ := exLF_of_ne hχ
    have hF : Fchi χ y = fun w => -(deriv (exLF χ) w / exLF χ w) * exKer y w := by
      funext w
      simp only [Fchi, negLD, exKer, hfL, mul_div_assoc]
    rw [hF, hmain, if_neg hχ]
    simp only [explicitFormulaConstant, exOrd]
    ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiC
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem main_lower {θ β η l X : ℝ} (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hl : l ≤ Real.log X) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * l) :
    X * η / (2 * Real.log X) ≤ liX X - θ * liX (X ^ β) := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log X := Real.log_pos (by linarith)
  have h2 : 2 ≤ X ^ β := by
    calc (2 : ℝ) ≤ 4 := by norm_num
      _ = √16 := by
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ √X := Real.sqrt_le_sqrt hX
      _ = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ
  have hXβ : X ^ β ≤ X := by
    calc X ^ β ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
      _ = X := Real.rpow_one X
  have hli := liX_nonneg h2
  rcases hη with h | h
  · have h1 := liX_lower (by linarith : 4 ≤ X)
    have h3 : X * η / (2 * Real.log X) ≤ X / (2 * Real.log X) := by
      gcongr
      nlinarith
    nlinarith
  · have h1 := liX_sub_ge h2 hXβ
    have hθ1 : θ ≤ 1 := (abs_le.1 hθ).2
    have h3 : liX X - liX (X ^ β) ≤ liX X - θ * liX (X ^ β) := by nlinarith
    have hw : η ≤ (1 - β) * Real.log X := h.trans (mul_le_mul_of_nonneg_left hl (by linarith))
    have he : X ^ β = X * Real.exp (-((1 - β) * Real.log X)) := by
      rw [Real.rpow_def_of_pos hX0]
      nth_rw 2 [← Real.exp_log hX0]
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-((1 - β) * Real.log X)) ≤ 1 - η / 2 :=
      (Real.exp_le_exp.2 (by linarith)).trans (exp_neg_le_one_sub_half hη0 hη1)
    have h4 : X * η / 2 ≤ X - X ^ β := by
      rw [he]
      nlinarith
    have h5 : X * η / (2 * Real.log X) ≤ (X - X ^ β) / Real.log X := by
      rw [show X * η / (2 * Real.log X) = (X * η / 2) / Real.log X by field_simp]
      gcongr
    linarith

theorem exp_sum_le_min_exponent {c l L u : ℝ} (hc : 0 < c) (hl : 0 < l) (hL : 0 ≤ L) (hu : L / 2 ≤ u) :
    Real.exp (-(c * u / l)) + Real.exp (-(c * Real.sqrt u)) ≤
      Real.exp (-(min (c / 2) (c ^ 2 / 2) * L / l)) + Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * L)) := by
  have hu0 : 0 ≤ u := by linarith
  have hm1 : min (c / 2) (c ^ 2 / 2) ≤ c / 2 := min_le_left _ _
  have hm2 : min (c / 2) (c ^ 2 / 2) ≤ c ^ 2 / 2 := min_le_right _ _
  have hm0 : 0 ≤ min (c / 2) (c ^ 2 / 2) := le_min (by positivity) (by positivity)
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hl.le
    have h1 := mul_le_mul_of_nonneg_right hm1 hL
    nlinarith
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [show c * Real.sqrt u = Real.sqrt (c ^ 2 * u) by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]]
    apply Real.sqrt_le_sqrt
    have h1 := mul_le_mul_of_nonneg_right hm2 hL
    nlinarith

theorem small_terms {c₃ c₁ L l η φ : ℝ} (hc₃ : 0 ≤ c₃) (hc₁ : 0 < c₁) (hL : 16 * l ≤ L) (hL1 : 1 ≤ L)
    (hη : c₁ * Real.exp (-l) ≤ η) (hφ0 : 0 < φ) (hφ : φ ≤ Real.exp l) :
    44 * Real.exp (L / 2) * L ≤
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
  have hL0 : 0 < L := by linarith
  have hsq : Real.sqrt (c₃ * L) ≤ 2 * c₃ + L / 8 := by
    calc Real.sqrt (c₃ * L) ≤ Real.sqrt ((2 * c₃ + L / 8) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (2 * c₃ - L / 8)])
      _ = 2 * c₃ + L / 8 := Real.sqrt_sq (by positivity)
  have hexpL : L ^ 2 ≤ 64 * Real.exp (L / 4) := by
    have h := Real.quadratic_le_exp_of_nonneg (x := L / 4) (by positivity)
    nlinarith
  have hsplit : Real.exp (3 * L / 4) = Real.exp (L / 2) * Real.exp (L / 4) := by
    rw [← Real.exp_add]
    ring_nf
  have key : 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L =
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := by
    have e : Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) =
        Real.exp (2 * c₃) * Real.exp (-Real.sqrt (c₃ * L)) * Real.exp L * Real.exp (-l) / Real.exp l := by
      rw [show 2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l = 2 * c₃ + -Real.sqrt (c₃ * L) + L + -l - l by ring,
        Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add]
    rw [e]
    field_simp
    ring
  calc 44 * Real.exp (L / 2) * L ≤ 2816 * Real.exp (3 * L / 4) / L := by
        rw [le_div_iff₀ hL0, hsplit]
        have hp := Real.exp_pos (L / 2)
        nlinarith
    _ ≤ 2816 * Real.exp (2 * c₃ - Real.sqrt (c₃ * L) + L - 2 * l) / L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        linarith
    _ = 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) *
        (Real.exp L * (c₁ * Real.exp (-l)) / (2 * L) / Real.exp l) := key
    _ ≤ 5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by
        gcongr
        exact div_nonneg (mul_nonneg (Real.exp_pos L).le (le_trans (mul_pos hc₁ (Real.exp_pos _)).le hη)) (by positivity)

theorem pi_core (M : ℕ) [NeZero M] (h8 : 8 ∣ M) (b : ℕ) (hb : b.Coprime M)
    (e : Option (DirichletCharacter ℂ M × ℝ)) {θ β η c A c₁ X : ℝ}
    (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (hmain : ∀ t : ℝ, 0 ≤ t → ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * Real.log M) (hc₁ : 0 < c₁)
    (hηl : c₁ * (M : ℝ) ^ (-1 : ℝ) ≤ η) (hc : 0 < c) (hA : 0 ≤ A) (hX : 0 < X)
    (hL : 16 * Real.log M ≤ Real.log X)
    (hP : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi e χ y‖ ≤
      A * y * η * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))) :
    |(piAP X M b : ℝ) - (liX X - θ * liX (X ^ β)) / (M.totient : ℝ)| ≤
      (10 * A + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁) *
        (Real.exp (-(min (c / 2) (c ^ 2 / 2) * Real.log X / Real.log M)) +
          Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * Real.log X))) *
        ((liX X - θ * liX (X ^ β)) / (M.totient : ℝ)) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos h8
  have hM0 : (0 : ℝ) < M := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have hX16 : 16 ≤ X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by norm_num) hX]
    linarith
  have hφ1 : (1 : ℝ) ≤ M.totient := by exact_mod_cast Nat.totient_pos.2 hMpos
  have hφM : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hφ0 : (0 : ℝ) < M.totient := by linarith
  set l := Real.log M with hldef
  set L := Real.log X with hLdef
  set φ : ℝ := (M.totient : ℝ) with hφdef
  set c₃ := min (c / 2) (c ^ 2 / 2) with hc₃def
  have hc₃ : 0 ≤ c₃ := le_min (by positivity) (by positivity)
  set E := Real.exp (-(c₃ * L / l)) + Real.exp (-Real.sqrt (c₃ * L)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hs0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hcore := abel_core (cAP M b) (vonMangoldtAP_nonneg M b) (vonMangoldtAP_le M b) (K := 1 / φ) (θ := θ) (β := β)
    (D := A * η * E / φ) (X := X) (by positivity) (by rw [div_le_one hφ0]; exact hφ1) hθ hβ hβ1 hX16
    (by positivity) (by
      intro t h1 h2
      have hs4 : 0 < √X := Real.sqrt_pos.2 hX
      have ht0 : 0 < t := by linarith
      have hu : L / 2 ≤ Real.log t := by
        rw [hLdef, ← Real.log_sqrt hX.le]
        exact Real.log_le_log hs4 h1
      rw [sum_cAP]
      calc |psiAP M b t - Fm (1 / φ) θ β t|
          ≤ (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / φ :=
            abs_psiAP_sub_le M b hb e θ β t (hmain t ht0.le)
        _ ≤ (A * t * η * E) / φ := by
            gcongr
            refine (hP t h1 h2).trans ?_
            gcongr
            exact exp_sum_le_min_exponent hc (by linarith) (by linarith) hu
        _ = A * η * E / φ * t := by ring)
  have hpp := abs_piAP_sub_le M b (by linarith : 1 ≤ X)
  have hm := main_lower hθ hβ hβ1 hX16 (by linarith : l ≤ L) hη0 hη1 hη
  have hexpl : Real.exp l = M := Real.exp_log hM0
  have hst := small_terms (c₃ := c₃) (c₁ := c₁) (L := L) (l := l) (η := η) (φ := φ) hc₃ hc₁ hL (by linarith)
    (by
      have : (M : ℝ) ^ (-1 : ℝ) = Real.exp (-l) := by
        rw [Real.rpow_def_of_pos hM0]; congr 1; ring
      rw [← this]; exact hηl) hφ0 (by rw [hexpl]; exact hφM)
  rw [Real.exp_half, Real.exp_log hX] at hst
  set m := liX X - θ * liX (X ^ β) with hmdef
  set P := X * η / (2 * L) / φ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPm : P ≤ m / φ := by
    rw [hPdef]
    gcongr
  have hKm : 1 / φ * m = m / φ := by ring
  rw [hKm] at hcore
  have h5 : 5 * (A * η * E / φ) * X / L = 10 * A * E * P := by
    rw [hPdef]
    field_simp
    ring
  rw [h5] at hcore
  have h40 : 40 * √X ≤ 40 * √X * L := by nlinarith
  have hEs : Real.exp (-Real.sqrt (c₃ * L)) ≤ E := by
    rw [hEdef]
    have := Real.exp_pos (-(c₃ * L / l))
    linarith
  have hA2 : 0 ≤ 5632 * Real.exp (2 * c₃) / c₁ := by positivity
  have hst2 : 44 * √X * L ≤ 5632 * Real.exp (2 * c₃) / c₁ * E * P :=
    hst.trans (by gcongr)
  have htot : |(piAP X M b : ℝ) - m / φ| ≤ (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P := by
    have hexp : (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P =
        10 * A * E * P + 5632 * Real.exp (2 * c₃) / c₁ * E * P := by ring
    have h44 : 44 * √X * L = 4 * √X * L + 40 * √X * L := by ring
    rw [hexp]
    rw [abs_le] at hcore hpp ⊢
    constructor <;> linarith [hcore.1, hcore.2, hpp.1, hpp.2]
  exact htot.trans (by gcongr)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

