module

public import Mathlib
public import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondLam
section
open Formalism.BasicNotions

theorem UpperTheory.Ram.cond_le_four_n_sq :
    ∀ (R : Ranks) (H : Host R), (H.QS : ℝ) * H.q * H.d ≤ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ∧ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ≤ ((H.QS : ℝ) * H.q * H.d) ^ 2 ∧ (R.f : ℝ) ≤ H.QS := by
  intro R H
  have hQS : H.QS ≤ R.n ^ 2 := H.QS_le
  have h2 : 2 * R.ord ≤ H.QS := (UpperTheory.Ram.ord_le_totient_QS H.toHostAx).2
  have hf : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    simp only [Ranks.f]
    push_cast
    ring
  have hn : (R.n : ℝ) = (R.ord : ℝ) := by simp [Ranks.n]
  have hq1 : (1 : ℝ) ≤ H.q := by
    have := H.qd_big.1
    exact_mod_cast (by omega : 1 ≤ H.q)
  have hd1 : (1 : ℝ) ≤ H.d := by
    have := H.qd_big.2
    exact_mod_cast (by omega : 1 ≤ H.d)
  have hQSr : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast hQS
  have h2r : 2 * (R.n : ℝ) ≤ H.QS := by
    rw [hn]; exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
  have hqd : (0 : ℝ) ≤ (H.q : ℝ) * H.d := by positivity
  have hqd1 : (1 : ℝ) ≤ (H.q : ℝ) * H.d := by nlinarith
  rw [hf]
  refine ⟨?_, ?_, h2r⟩
  · have : (H.QS : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hqd
    nlinarith
  · have hsq : 4 * (2 * (R.n : ℝ) / 2) ^ 2 ≤ (H.QS : ℝ) ^ 2 := by nlinarith
    have hqq : (H.q : ℝ) * H.d ≤ ((H.q : ℝ) * H.d) ^ 2 := by nlinarith
    have hA : (0 : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by positivity
    calc 4 * (2 * (R.n : ℝ) / 2) ^ 2 * H.q * H.d = 4 * (2 * (R.n : ℝ) / 2) ^ 2 * ((H.q : ℝ) * H.d) := by ring
      _ ≤ (H.QS : ℝ) ^ 2 * ((H.q : ℝ) * H.d) ^ 2 := mul_le_mul hsq hqq hqd (by positivity)
      _ = ((H.QS : ℝ) * H.q * H.d) ^ 2 := by ring
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.TwoFmLeRdE
section
open Formalism.BasicNotions

theorem UpperTheory.Ram.two_fm_le_rdE :
    ∀ (R : Ranks) (H : Host R), 2 * (R.f : ℝ) * R.m ≤ H.rdE ∧ 4 * (R.t : ℝ) * R.r + 1 ≤ H.rdE := by
  intro R H
  obtain ⟨hq, hd⟩ := H.qd_big
  obtain ⟨-, -, hsq, -⟩ := UpperTheory.KR.log_qd_le_rd H.toHostAx H.flPS
  have hrd : H.toHostAx.rd = H.rdE := rfl
  have hq' : H.toHostAx.q = H.q := rfl
  have hd' : H.toHostAx.d = H.d := rfl
  rw [hrd, hq', hd'] at hsq
  set X : ℝ := 4 * (R.t : ℝ) * R.r + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hqX : X < (H.q : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.q : ℝ) := by exact_mod_cast hq
    simpa [hX] using this
  have hdX : X < (H.d : ℝ) := by
    have : ((4 * R.t * R.r + 1 : ℕ) : ℝ) < (H.d : ℝ) := by exact_mod_cast hd
    simpa [hX] using this
  have hprod : X * X < (H.q : ℝ) * H.d := mul_lt_mul'' hqX hdX hX0 hX0
  have hsqrt : X < √((H.q : ℝ) * H.d) := by
    rw [show X = √(X * X) from (Real.sqrt_mul_self hX0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hprod
  have hmain : X ≤ H.rdE := le_trans hsqrt.le hsq
  refine ⟨?_, hmain⟩
  have hf : R.f ≤ R.k := by
    have := R.f_le_k
    simp only [Ranks.f, Ranks.n]
    omega
  have hm := R.two_le_m
  have hr : R.k + 1 ≤ R.r := by
    simp only [Ranks.r]
    omega
  have hmt : R.m ≤ R.t := by
    have := R.three_m_lt_t
    omega
  have hnat : 2 * R.f * R.m ≤ 4 * R.t * R.r + 1 := by
    have h1 : R.f ≤ R.r := by omega
    calc 2 * R.f * R.m ≤ 2 * R.r * R.t := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) hmt
      _ ≤ 4 * R.t * R.r + 1 := by nlinarith
  have : (2 * (R.f : ℝ) * R.m) ≤ X := by
    rw [hX]
    exact_mod_cast hnat
  linarith
end

