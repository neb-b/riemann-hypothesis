module

public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.MinkowskiNumberDvdFactorial
public import Formalism.LocalRingCardinality.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.KernelPlaceMeanBound
section
noncomputable section

namespace Formalism.BasicNotions.DV

open Formalism.BasicNotions

def logHook (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, Real.log (Real.Gamma (a i + n - i))) -
    ∑ i ∈ Finset.range n, ∑ l ∈ Finset.Ioo i n, Real.log (a i - a l + l - i)

def Lprime (D : D7) (L : SizeData₂ D) : ℝ :=
  Real.log (L.sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def L6lo (D : D7) (L : SizeData₂ D) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lprime D L

def kernelPlaceMeanBound (D : D7) (L : SizeData₂ D) (C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlace D L u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * L.La +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * L.sc.L

def hExpl6 (D : D7) (L : SizeData₂ D) (X : DivX D) (C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbP D L C u + (∑ j ∈ SizeData₂.lifts D, kernelPlaceMeanBound D L C u j) - (∑ j ∈ SizeData₂.lifts D, L6lo D L C j) -
    meanE D (fun e => Real.log (X.kapR e))

end Formalism.BasicNotions.DV

end
end

-- bundled from Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber
section
namespace Formalism.BasicNotions

open Formalism.HermitianLatticeCounting.S6 (minkowskiM minkowskiExp)

theorem minkM_pos (n : ℕ) : 0 < minkM n :=
  Finset.prod_pos fun _ hp => pow_pos (Finset.mem_filter.1 hp).2.pos _

theorem minkM_dvd_factorial (n : ℕ) : minkM n ∣ (2 * n).factorial := Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial n

theorem log_minkM_le_two (n : ℕ) : Real.log (minkM n : ℝ) ≤ 2 * n * Real.log (2 * n) := by
  have h1 : minkM n ≤ (2 * n) ^ (2 * n) :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (minkM_dvd_factorial n)).trans (Nat.factorial_le_pow _)
  have h2 : (minkM n : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ (2 * n) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < minkM n := by exact_mod_cast minkM_pos n
  have h4 := Real.log_le_log h3 h2
  rw [Real.log_pow] at h4
  push_cast at h4
  exact h4

theorem Ranks.two_le_fN (R : Ranks) : 2 ≤ R.f * R.N R.m := by
  have hf : 2 ≤ R.f := by
    have h1 := R.two_le_m
    have h2 := R.m_le_f
    unfold Ranks.f Ranks.n; omega
  have hN : 1 ≤ R.N R.m := by
    have h1 := R.k_ge
    have h2 : R.k ≤ R.N R.m := Nat.le_add_right _ _
    omega
  calc 2 = 2 * 1 := rfl
    _ ≤ R.f * R.N R.m := Nat.mul_le_mul hf hN

theorem DGamMink.mem {D : D7} (h : DGamMink D) (hD : DGamDef D) (u : D.what₂.Word) :
    (D.mem u).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m) := by
  rw [← hD.one u D.u₀ D.what₂.mu0, hD.one D.u₀ D.u₀ D.what₂.mu0]; exact h

theorem DGamMink.fact {D : D7} (h : DGamMink D) (hD : DGamDef D) : FactDGam D 12 := by
  intro u
  rw [h.mem hD u]
  have hy : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.N D.R.m := by exact_mod_cast D.R.two_le_fN
  have h1 := log_minkM_le_two (2 * D.R.f * D.R.N D.R.m)
  have e : ((2 * D.R.f * D.R.N D.R.m : ℕ) : ℝ) = 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by push_cast; ring
  rw [e] at h1
  have e2 : (2 : ℝ) * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) = 2 * 2 * ((D.R.f : ℝ) * D.R.N D.R.m) := by ring
  have h2 : Real.log (2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m))) =
      Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by
    rw [e2, Real.log_mul (by norm_num) (by linarith), Real.log_mul (by norm_num) (by norm_num)]
  have h3 : Real.log 2 ≤ Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := Real.log_le_log (by norm_num) hy
  rw [h2] at h1
  have h4 : 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (Real.log 2 + Real.log 2 + Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) ≤
      2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc Real.log (minkM (2 * D.R.f * D.R.N D.R.m) : ℝ)
      ≤ 2 * (2 * ((D.R.f : ℝ) * D.R.N D.R.m)) * (3 * Real.log ((D.R.f : ℝ) * D.R.N D.R.m)) := h1.trans h4
    _ = 12 * D.R.f * D.R.N D.R.m * Real.log ((D.R.f : ℝ) * D.R.N D.R.m) := by ring

end Formalism.BasicNotions
end

-- bundled from Formalism.LocalRingCardinality.NFLeTwoMulTSq
section
namespace Formalism.BasicNotions

theorem ParamsT.nV_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.R.nV = T.TO * T.nWn + (8 * D.R.f * D.R.r + 4) := by
  have h1 := T.split
  have h2 := T.nP_eq
  unfold Ranks.nV
  omega

theorem ParamsT.nV_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ D.R.nV := by
  rw [T.nV_eq]; exact Nat.le_add_left _ _

end Formalism.BasicNotions
end

