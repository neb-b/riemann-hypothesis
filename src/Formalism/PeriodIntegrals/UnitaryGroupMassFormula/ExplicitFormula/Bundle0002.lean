module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0010
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
section
noncomputable section

namespace PI.EF

open Complex

section defs

variable {N : ℕ} [NeZero N]

abbrev mult (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ


open Classical in
def eps0 (χ : DirichletCharacter ℂ N) : ℂ := by
  classical
  exact if χ.Even ∧ χ ≠ 1 then 1 else 0


open Classical in
def del1 (χ : DirichletCharacter ℂ N) : ℂ := if χ = 1 then 1 else 0

def psiRaw (χ : DirichletCharacter ℂ N) (u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N)

def zsum (χ : DirichletCharacter ℂ N) (T u : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ ZerosBelow χ T, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)

def S1 (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑ᶠ ρ ∈ ZerosBelow χ 1, (mult χ ρ : ℝ) / ‖ρ‖

def NoOrdinate (χ : DirichletCharacter ℂ N) (T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 → |ρ.im| ≠ T'

def GoodHeight (χ : DirichletCharacter ℂ N) (κ T' : ℝ) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 →
    1 / (κ * Real.log (N * T')) ≤ |(|ρ.im|) - T'|

end defs

def cLine (u : ℝ) : ℝ := 1 + 1 / Real.log u

def Err (N : ℕ) (u T : ℝ) : ℝ := u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u)

def rectInt (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f (x + y₀ * I)) - (∫ x : ℝ in x₀..x₁, f (x + y₁ * I)) +
    I • (∫ y : ℝ in y₀..y₁, f (x₁ + y * I)) - I • ∫ y : ℝ in y₀..y₁, f (x₀ + y * I)

def rect (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ := Set.Icc x₀ x₁ ×ℂ Set.Icc y₀ y₁

def perronK (y c T : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

def kb (T y : ℝ) : ℝ := if T * |Real.log y| ≤ 1 then 2 else 1 / (T * |Real.log y|)

def vertInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u T' : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T')..T',
    (-logDeriv (DirichletCharacter.LFunction χ) ((cLine u : ℂ) + t * I)) *
      ((u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I))

def PerronL (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u T T' : ℝ), 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 →
    ‖psiRaw χ u - vertInt χ u T'‖ ≤ C * Err N u T

def ShiftBound (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → GoodHeight χ κ T' →
      ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ ≤ C * (Err N u T + S1 χ)

def GoodHeightExists (κ : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T →
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ GoodHeight χ κ T'

def TruncChange (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 →
      ‖zsum χ T' u - zsum χ T u‖ ≤ C * Err N u T

def ZerosFinite : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T : ℝ, (ZerosBelow χ T).Finite

def PerronKernel : Prop :=
  ∀ y c T : ℝ, 0 < y → 0 < c → 0 < T →
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ 2 * y ^ c ∧
    T * |Real.log y| * ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c

def PerronSumBound (C : ℝ) : Prop :=
  ∀ u T : ℝ, 2 ≤ u → 2 ≤ T →
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)) ∧
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n) ≤
      C * (u * Real.log u ^ 2 / T + Real.log u)

def PerronTrunc (C : ℝ) : Prop :=
  ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) → ∀ u T : ℝ, 2 ≤ u → 2 ≤ T →
    ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) - (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T,
        LSeries a ((cLine u : ℂ) + t * I) *
          ((u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I))‖ ≤
      C * (u * Real.log u ^ 2 / T + Real.log u)

def RectResidue : Prop :=
  ∀ (x₀ x₁ y₀ y₁ : ℝ) (H : ℂ → ℂ) (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ) (u : ℝ), 0 < u →
    x₀ < 0 → 0 < x₁ → y₀ < 0 → 0 < y₁ → DifferentiableOn ℂ H (rect x₀ x₁ y₀ y₁) →
    (∀ ρ ∈ Z, ρ ≠ 0 ∧ x₀ < ρ.re ∧ ρ.re < x₁ ∧ y₀ < ρ.im ∧ ρ.im < y₁) →
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * ((u : ℂ) ^ s / s)) x₀ x₁ y₀ y₁ =
      2 * Real.pi * I * (H 0 + (∑ ρ ∈ Z, wt ρ * (((u : ℂ) ^ ρ - 1) / ρ)) + e * Real.log u)

def ZeroLocus : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -3 / 2 ≤ s.re → s ≠ 1 →
    DirichletCharacter.LFunction χ s = 0 →
      (0 < s.re ∧ s.re < 1) ∨ (s = 0 ∧ χ.Even ∧ χ ≠ 1) ∨ (s = -1 ∧ χ.Odd)

def IsRegPart {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x₁ T' : ℝ) (H : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ H (rect (-1 / 2) x₁ (-T') T') ∧
  ∀ s ∈ rect (-1 / 2) x₁ (-T') T', DirichletCharacter.LFunction χ s ≠ 0 → s ≠ 1 →
    logDeriv (DirichletCharacter.LFunction χ) s =
      H s + (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / (s - ρ)) + eps0 χ / s - del1 χ / (s - 1)

def RegularPart : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ x₁ T' : ℝ, 1 < x₁ → 0 < T' →
    NoOrdinate χ T' → ∃ H : ℂ → ℂ, IsRegPart χ x₁ T' H

def LocalAbstract : Prop :=
  ∀ r R' R : ℝ, 0 < r → r < R' → R' < R → ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ), AnalyticOnNhd ℂ f (Metric.closedBall s₀ R) → f s₀ ≠ 0 → 0 ≤ M →
      (∀ s ∈ Metric.closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) →
      ({ρ | ρ ∈ Metric.closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ Metric.closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ Metric.closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ C * M

def LGrowth (A C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 →
    ‖(1 + del1 χ * (s - 2)) * DirichletCharacter.LFunction χ s‖ ≤ C * (N * (|s.im| + 2)) ^ A

def LocalLemma (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 3 →
    DirichletCharacter.LFunction χ s ≠ 0 → s ≠ 1 →
    ‖logDeriv (DirichletCharacter.LFunction χ) s -
        (∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)) - eps0 χ / s + del1 χ / (s - 1)‖ ≤
      C * Real.log (N * (|s.im| + 2))

def LogDerivHoriz (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ T' : ℝ, 2 ≤ T' →
    GoodHeight χ κ T' → ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ 3 →
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + T' * I)‖ ≤ C * Real.log (N * T') ^ 2 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (-T' : ℝ) * I)‖ ≤ C * Real.log (N * T') ^ 2

def LogDerivLeft (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    ‖logDeriv (DirichletCharacter.LFunction χ) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      C * Real.log (N * (|t| + 2))

def RegAtZero (C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (x₁ T' : ℝ) (H : ℂ → ℂ), 1 < x₁ →
    2 ≤ T' → IsRegPart χ x₁ T' H →
      ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0‖ ≤ C * Real.log (2 * N) + S1 χ

def ContourIdentity : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ (u T' : ℝ) (H : ℂ → ℂ), 2 ≤ u →
    2 ≤ T' → NoOrdinate χ T' → IsRegPart χ (cLine u) T' H →
      rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
          (-1 / 2) (cLine u) (-T') T' =
        2 * Real.pi * I * (H 0 + zsum χ T' u - (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          eps0 χ * Real.log u - del1 χ * (u - 1))

def SidesBound (κ C : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → GoodHeight χ κ T' →
      ‖rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
          (-1 / 2) (cLine u) (-T') T' + 2 * Real.pi * I * vertInt χ u T'‖ ≤ C * Err N u T

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFE
section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter
open scoped ZMod

variable {N : ℕ} [NeZero N]

theorem zmodL_const_mul (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun k => c * Φ k) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem norm_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ (ZMod.stdAddChar (N := N))‖ ≤ N := by
  rw [gaussSum]
  calc ‖∑ a, χ a * ZMod.stdAddChar a‖ ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
        exact DirichletCharacter.norm_le_one χ a
    _ = N := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

private theorem re_pi_mul_I_mul_div_two (w : ℂ) :
    ((Real.pi : ℂ) * I * w / 2).re = -(Real.pi / 2 * w.im) := by
  rw [show ((Real.pi : ℂ) * I * w / 2) = ((Real.pi / 2 : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

private theorem re_neg_pi_mul_I_mul_div_two (w : ℂ) :
    (-(Real.pi : ℂ) * I * w / 2).re = Real.pi / 2 * w.im := by
  rw [show (-(Real.pi : ℂ) * I * w / 2) = ((-(Real.pi / 2) : ℝ) : ℂ) * (I * w) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

private theorem norm_LFunction_const_mul_le_of_norm_le (χ : DirichletCharacter ℂ N) {c : ℂ} (hc : ‖c‖ ≤ N)
    (w : ℂ) :
    ‖ZMod.LFunction (fun k => c * (χ : ZMod N → ℂ) k) w‖
      ≤ N * ‖ZMod.LFunction (χ : ZMod N → ℂ) w‖ := by
  rw [zmodL_const_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem norm_L_one_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖LFunction χ⁻¹ w‖ := by
  change ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - w)‖
    ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖
  set L := ‖ZMod.LFunction ((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) w‖ with hL
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hs : ∀ n : ℕ, w ≠ -n := by
    intro n hn
    have : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : (χ : ZMod N → ℂ) 0 = 0 ∨ w ≠ 1 := h
  rw [ZMod.LFunction_one_sub _ hs hs']
  set g := gaussSum χ (ZMod.stdAddChar (N := N)) with hg
  have hgN : ‖g‖ ≤ N := norm_gaussSum_le χ
  have hF : 𝓕 (χ : ZMod N → ℂ) = fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
    funext k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_eq_neg_one_mul k, map_mul]
    ring
  have hneg : (fun x => (χ : ZMod N → ℂ) (-x)) = χ (-1) • (χ : ZMod N → ℂ) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ← map_mul, neg_one_mul]
  have hc1 : ‖g * χ⁻¹ (-1)‖ ≤ N := by
    rw [norm_mul]
    calc ‖g‖ * ‖χ⁻¹ (-1)‖ ≤ N * 1 :=
          mul_le_mul hgN (DirichletCharacter.norm_le_one _ _) (norm_nonneg _) (by positivity)
      _ = N := mul_one _
  have hc2 : ‖χ (-1) * (g * χ⁻¹ (-1))‖ ≤ N := by
    rw [norm_mul]
    calc ‖χ (-1)‖ * ‖g * χ⁻¹ (-1)‖ ≤ 1 * N :=
          mul_le_mul (DirichletCharacter.norm_le_one _ _) hc1 (norm_nonneg _) (by positivity)
      _ = N := one_mul _
  have hA : ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖ ≤ N * L := by
    rw [hF]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc1 w
  have hB : ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ ≤ N * L := by
    rw [hneg, map_smul, hF]
    have e : (χ (-1) • fun k => (g * χ⁻¹ (-1)) * (χ⁻¹ : DirichletCharacter ℂ N) k)
        = fun k => (χ (-1) * (g * χ⁻¹ (-1))) * (χ⁻¹ : DirichletCharacter ℂ N) k := by
      funext k
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact norm_LFunction_const_mul_le_of_norm_le χ⁻¹ hc2 w
  set E := Real.exp (Real.pi / 2 * |w.im|) with hE
  have he1 : ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := neg_abs_le w.im
    have := Real.pi_pos
    nlinarith
  have he2 : ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖ ≤ E := by
    rw [Complex.norm_exp, re_neg_pi_mul_I_mul_div_two]
    apply Real.exp_le_exp.mpr
    have := le_abs_self w.im
    have := Real.pi_pos
    nlinarith
  have hP : ‖(N : ℂ) ^ (w - 1)‖ ≤ (N : ℝ) ^ 4 := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N), Complex.sub_re, Complex.one_re]
    calc (N : ℝ) ^ (w.re - 1) ≤ (N : ℝ) ^ ((4 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
      _ = (N : ℝ) ^ 4 := Real.rpow_natCast _ _
  have hQ : ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hGE : ‖Complex.Gamma w‖ * E ≤ 3 * ‖w + 1‖ ^ 5 :=
    Gamma_decay h1 (by linarith)
  have hsum : ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w
      + cexp (-(Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖
      ≤ 2 * E * N * L := by
    calc _ ≤ ‖cexp ((Real.pi : ℂ) * I * w / 2) * ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)
              * ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := norm_add_le _ _
      _ = ‖cexp ((Real.pi : ℂ) * I * w / 2)‖ * ‖ZMod.LFunction (𝓕 (χ : ZMod N → ℂ)) w‖
          + ‖cexp (-(Real.pi : ℂ) * I * w / 2)‖
              * ‖ZMod.LFunction (𝓕 fun x => (χ : ZMod N → ℂ) (-x)) w‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ E * (N * L) + E * (N * L) := by gcongr
      _ = 2 * E * N * L := by ring
  have hEn : 0 ≤ E := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(N : ℂ) ^ (w - 1)‖ * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖_‖
      ≤ (N : ℝ) ^ 4 * 1 * ‖Complex.Gamma w‖ * (2 * E * N * L) := by gcongr
    _ = 2 * (N : ℝ) ^ 5 * L * (‖Complex.Gamma w‖ * E) := by ring
    _ ≤ 2 * (N : ℝ) ^ 5 * L * (3 * ‖w + 1‖ ^ 5) := by gcongr
    _ = 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * L := by ring

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBoundOfZeroFree
section
namespace PI.EF.Loc

open Complex Metric Set Filter Topology

theorem logDeriv_bound_of_zero_free (hDL : PI.DiscLog) {g : ℂ → ℂ} {s₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball s₀ R))
    (hz : ∀ z ∈ ball s₀ R, g z ≠ 0) (hb : ∀ z ∈ ball s₀ R, ‖g z‖ ≤ Real.exp M * ‖g s₀‖) :
    ∀ z ∈ closedBall s₀ r, ‖deriv g z / g z‖ ≤ 4 * (r + R) / (R - r) ^ 2 * M := by
  intro z hzr
  obtain ⟨L, hL0, hLd, hLe⟩ := hDL g s₀ R hg hz
  have hR : 0 < R := hr.trans hrR
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hg0 : 0 < ‖g s₀‖ := norm_pos_iff.mpr (hz s₀ hs₀)
  have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun x hx =>
    (hLd x hx).differentiableAt.differentiableWithinAt
  have hre : ∀ x ∈ ball s₀ R, (L x).re ≤ M := by
    intro x hx
    have h1 := hb x hx
    rw [hLe x hx, norm_mul, Complex.norm_exp, mul_comm (Real.exp M)] at h1
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_left h1 hg0)
  have hmem : ∀ u ∈ ball (0 : ℂ) R, s₀ + u ∈ ball s₀ R := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    simpa [dist_eq_norm] using hu
  have hFd : DifferentiableOn ℂ (fun u => L (s₀ + u)) (ball 0 R) := by
    intro u hu
    have h1 : DifferentiableAt ℂ L (s₀ + u) := (hLd _ (hmem u hu)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun v : ℂ => s₀ + v) u := differentiableAt_id.const_add s₀
    exact (h1.comp u h2).differentiableWithinAt
  have hFre : MapsTo (fun u => L (s₀ + u)) (ball 0 R) {w | w.re ≤ M} :=
    fun u hu => hre _ (hmem u hu)
  have hF0 : (fun u => L (s₀ + u)) 0 = 0 := by simp [hL0]
  have hρR : (r + R) / 2 < R := by linarith
  have hbound : ∀ x ∈ closedBall s₀ ((r + R) / 2),
      ‖L x‖ ≤ 2 * M * ((r + R) / 2) / (R - (r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hu : x - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := Complex.borelCaratheodory_zero hM hFd hFre hR hu hF0
    have e : s₀ + (x - s₀) = x := by ring
    simp only [e] at h1
    refine h1.trans ?_
    have hpos : 0 < R - (r + R) / 2 := by linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    nlinarith [mul_nonneg (mul_nonneg hM.le hR.le) (sub_nonneg.mpr hx)]
  have hδ : 0 < (R - r) / 2 := by linarith
  have hzr' : ‖z - s₀‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hzr; exact hzr
  have hsub : closedBall z ((R - r) / 2) ⊆ closedBall s₀ ((r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have : ‖x - s₀‖ ≤ ‖x - z‖ + ‖z - s₀‖ := by
      have := norm_add_le (x - z) (z - s₀)
      simpa using this
    linarith
  have hsubB : closedBall s₀ ((r + R) / 2) ⊆ ball s₀ R := closedBall_subset_ball hρR
  have hdc : DiffContOnCl ℂ L (ball z ((R - r) / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hδ.ne']
    exact hLdiff.mono (hsub.trans hsubB)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc
    (fun x hx => hbound x (hsub (sphere_subset_closedBall hx)))
  have hzB : z ∈ ball s₀ R := hsubB (hsub (mem_closedBall_self hδ.le))
  rw [(hLd z hzB).deriv] at hc
  refine hc.trans (le_of_eq ?_)
  have e1 : R - (r + R) / 2 = (R - r) / 2 := by ring
  have hne : R - r ≠ 0 := by linarith
  rw [e1]
  field_simp
  ring

end PI.EF.Loc
end

