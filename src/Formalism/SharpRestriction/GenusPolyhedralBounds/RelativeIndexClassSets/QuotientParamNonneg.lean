module

public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0001

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.T0

theorem levels_real (A B R δ d D T cg c w G PH Pη L F' fr aδ aF HF Hδ SS Λ' lδ : ℝ)
    (hR : 0 ≤ R) (hRδ : R * δ ≤ d) (hδ : 0 ≤ δ) (hlδ : 0 ≤ lδ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hcg0 : 0 ≤ cg) (hcg1 : cg ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ PH * L) (hG : 0 ≤ G) (hPH : 0 ≤ PH)
    (hPη : 0 ≤ Pη) (hL : 0 ≤ L) (hfr : 0 ≤ fr)
    (h1 : 2 * A ≤ δ * lδ + 2 * SS + 2 * D * aF * w + 2 * HF)
    (h2 : B ≤ cg * (Hδ + D * aδ * w) + T * c * δ * Pη)
    (hSS : SS ≤ δ * Λ') (hΛ : Λ' ≤ G * F') (hF : F' ≤ (D + 2) * L + 5 * fr * T)
    (haδ : aδ ≤ 4 / 3 * δ) (haF : aF ≤ 4 / 3 * (D + 4) * δ)
    (hHF : HF ≤ (D + 4) * (D + 1) * δ * (2 * G + 6 * PH) * L)
    (hHδ : Hδ ≤ (D + 1) * δ * (2 * G + 6 * PH) * L) :
    R * (A + 1 / 2 * B) ≤
      d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
  have hSS' : SS ≤ δ * (G * ((D + 2) * L + 5 * fr * T)) :=
    hSS.trans (mul_le_mul_of_nonneg_left (hΛ.trans (mul_le_mul_of_nonneg_left hF hG)) hδ)
  have haFw : aF * w ≤ 4 / 3 * (D + 4) * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haF hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haFw' : D * (aF * w) ≤ D * (4 / 3 * (D + 4) * δ * (PH * L)) := mul_le_mul_of_nonneg_left haFw hD
  have haδw : aδ * w ≤ 4 / 3 * δ * (PH * L) :=
    (mul_le_mul_of_nonneg_right haδ hw0).trans (mul_le_mul_of_nonneg_left hw (by positivity))
  have haδw' : D * (aδ * w) ≤ D * (4 / 3 * δ * (PH * L)) := mul_le_mul_of_nonneg_left haδw hD
  have hXb0 : 0 ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by positivity
  have hin : Hδ + D * aδ * w ≤ (D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L)) := by
    have e : D * aδ * w = D * (aδ * w) := by ring
    linarith
  have hB' : B ≤ ((D + 1) * δ * (2 * G + 6 * PH) * L + D * (4 / 3 * δ * (PH * L))) + T * c * δ * Pη := by
    have e2 := mul_le_mul_of_nonneg_left hin hcg0
    have e3 := mul_le_of_le_one_left hXb0 hcg1
    linarith
  have hAB : A + 1 / 2 * B ≤ δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by
    have p1 : 0 ≤ δ * G * L * D ^ 2 := by positivity
    have p2 : 0 ≤ δ * G * L * D := by positivity
    have p3 : 0 ≤ δ * G * L := by positivity
    have p4 : 0 ≤ δ * PH * L * D ^ 2 := by positivity
    have p5 : 0 ≤ δ * PH * L * D := by positivity
    have p6 : 0 ≤ δ * PH * L := by positivity
    have p7 : 0 ≤ δ * lδ := by positivity
    have e : D * aF * w = D * (aF * w) := by ring
    linarith
  have hT0 : 0 ≤ ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by positivity
  calc R * (A + 1 / 2 * B) ≤ R * (δ * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)) := mul_le_mul_of_nonneg_left hAB hR
    _ = (R * δ) * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := by ring
    _ ≤ d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη) := mul_le_mul_of_nonneg_right hRδ hT0

theorem total_named_real (d D T c G PH Pη Pd PD PQ DivisibilityWeightConstant RR γ L κ fr lδ ρ ρ' : ℝ)
    (hd : 0 ≤ d) (hD : 1 ≤ D) (hT : 1 ≤ T) (hG : 0 ≤ G) (hPH : 0 ≤ PH) (hPD : 0 ≤ PD) (hPQ : 0 ≤ PQ)
    (hκ : 0 ≤ κ) (hS2 : T * L ≤ 2 * κ) (hlδ0 : 0 ≤ lδ) (hlδ : lδ ≤ Pd)
    (hρ : ρ ≤ ρ' + 22 * D ^ 2 * d / T) (hρ' : ρ' ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ)) :
    d * ((D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη)
        + ρ * PD * κ + ρ' * PQ * κ ≤
      d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) := by
  have hT0 : 0 < T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hLT : L ≤ 2 * κ / T := by
    rw [le_div_iff₀ hT0]
    linarith
  have hDD : (D + 4) * (D + 1) ≤ 10 * D ^ 2 := by nlinarith
  have hk : 0 ≤ 2 * κ / T := by positivity
  have hGP : 0 ≤ 3 * G + 9 * PH := by positivity
  have e1 : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L ≤ (60 * G + 180 * PH) * D ^ 2 * κ / T := by
    calc (D + 4) * (D + 1) * (3 * G + 9 * PH) * L
        ≤ (D + 4) * (D + 1) * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_left hLT (by positivity)
      _ ≤ 10 * D ^ 2 * (3 * G + 9 * PH) * (2 * κ / T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDD hGP) hk
      _ = (60 * G + 180 * PH) * D ^ 2 * κ / T := by ring
  have hPd0 : 0 ≤ Pd := le_trans hlδ0 hlδ
  have e2 : lδ ≤ Pd * T := hlδ.trans (le_mul_of_one_le_right hPd0 hT)
  have hX : (D + 4) * (D + 1) * (3 * G + 9 * PH) * L + 5 * G * fr * T + lδ + 1 / 2 * T * c * Pη ≤ ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) := by
    have ea : (5 * G * fr + Pd) * T = 5 * G * fr * T + Pd * T := by ring
    have eb : Pη / 2 * T * c = 1 / 2 * T * c * Pη := by ring
    linarith
  have g1 := mul_le_mul_of_nonneg_left hX hd
  have f1 : ρ * (PD * κ) ≤ (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg hPD hκ)
  have f2 : ρ' * ((PD + PQ) * κ) ≤ d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) :=
    mul_le_mul_of_nonneg_right hρ' (mul_nonneg (add_nonneg hPD hPQ) hκ)
  have e5 : 22 * D ^ 2 * d / T * (PD * κ) ≤ d * (40 * PD * D ^ 2 * κ / T) := by
    have h0 : 0 ≤ d * PD * D ^ 2 * κ / T := by positivity
    have ea : 22 * D ^ 2 * d / T * (PD * κ) = 22 * (d * PD * D ^ 2 * κ / T) := by ring
    have eb : d * (40 * PD * D ^ 2 * κ / T) = 40 * (d * PD * D ^ 2 * κ / T) := by ring
    rw [ea, eb]
    linarith
  have eq1 : d * ((60 * G + 180 * PH + 40 * PD) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c
        + DivisibilityWeightConstant * (PD + PQ) * (1 / T + RR ^ 2 * c) * κ / γ) =
      d * ((60 * G + 180 * PH) * D ^ 2 * κ / T + (5 * G * fr + Pd) * T + Pη / 2 * T * c) + d * (40 * PD * D ^ 2 * κ / T) +
        d * (DivisibilityWeightConstant * (RR ^ 2 * c + 1 / T) / γ) * ((PD + PQ) * κ) := by ring
  have eq2 : ρ * PD * κ + ρ' * PQ * κ = ρ * (PD * κ) + ρ' * ((PD + PQ) * κ) - ρ' * (PD * κ) := by ring
  have eq3 : (ρ' + 22 * D ^ 2 * d / T) * (PD * κ) = ρ' * (PD * κ) + 22 * D ^ 2 * d / T * (PD * κ) := by
    ring
  rw [eq1]
  linarith

theorem total_le_of_bounds (d D T c RR γ κ P1 P2 P3 P4 PP : ℝ)
    (hd : 0 ≤ d) (hT : 0 < T) (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (h1 : P1 * D ^ 2 ≤ PP ^ 2 * D ^ 3) (h2 : P2 ≤ PP ^ 3) (h3 : P3 ≤ PP ^ 2) (h4 : P4 ≤ PP ^ 2) :
    d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ) ≤
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by
  have a1 : P1 * D ^ 2 * (κ / T) ≤ PP ^ 2 * D ^ 3 * (κ / T) := mul_le_mul_of_nonneg_right h1 (by positivity)
  have a2 : P2 * T ≤ PP ^ 3 * T := mul_le_mul_of_nonneg_right h2 hT.le
  have a3 : P3 * (T * c) ≤ PP ^ 2 * (T * c) := mul_le_mul_of_nonneg_right h3 (by positivity)
  have a4 : P4 * ((1 / T + RR ^ 2 * c) * κ / γ) ≤ PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hsum : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ ≤
      PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T := by
    have e : P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ =
        P1 * D ^ 2 * (κ / T) + P2 * T + P3 * (T * c) + P4 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    have e' : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T =
        PP ^ 2 * D ^ 3 * (κ / T) + PP ^ 3 * T + PP ^ 2 * (T * c) + PP ^ 2 * ((1 / T + RR ^ 2 * c) * κ / γ) := by ring
    rw [e, e']
    linarith
  calc d * (P1 * D ^ 2 * κ / T + P2 * T + P3 * T * c + P4 * (1 / T + RR ^ 2 * c) * κ / γ)
      ≤ d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + PP ^ 3 * T) :=
        mul_le_mul_of_nonneg_left hsum hd
    _ = d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / γ) + d * PP ^ 3 * T := by ring

structure SumDat (ι : Type*) where

  s : Finset ι

  l : ι → ℝ

  I : ι → ℝ

  N : ι → ℝ

  cD : ι → ℝ

  vQ : ι → ℝ

  be : ι → ℝ

  (R δ d D T c i g₀ rw : ℝ)

  (G PH Prw Pη Pd PD PQ DivisibilityWeightConstant RR γ₀ : ℝ)

  (L κ F' f r : ℝ)

  (aδ aF HF Hδ SS Λ' : ℝ)

  (ρ ρ' : ℝ)

namespace SumDat

variable {ι : Type*} (X : SumDat ι)

def rr (la : ι) : ℝ :=
  X.R * (X.I la + X.T * (X.c / (2 * X.i)) * X.N la) + X.cD la + (X.vQ la + X.ρ' * X.be la)

def P1 : ℝ := 60 * X.G + 180 * X.PH + 40 * X.PD

def P2 : ℝ := 5 * X.G * (X.f * X.r ^ 2) + X.Pd

def P3 : ℝ := X.Pη / 2

def P4 : ℝ := X.DivisibilityWeightConstant * (X.PD + X.PQ)

variable {X}

end SumDat

end Formalism.MainNotions.Gaps.T0
