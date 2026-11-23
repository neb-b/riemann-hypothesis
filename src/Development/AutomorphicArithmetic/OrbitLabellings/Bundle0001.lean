module

public import Mathlib
public import Formalism.GaussJetBounds.Bundle0001
public import Formalism.IncomingBounds.IncomingBound
public import Formalism.IncomingBounds.FlowDegreeBounds.LemmaFd
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsMaxFlowAttainedAndIsOptDual

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.ColDefs
section
noncomputable section

open scoped BigOperators
open Formalism.DworkPowerSeriesWeights Formalism.IncomingBounds

namespace UpperTheory.G2

structure IsPos {Lt : Type} (i : ℕ) (pos : Lt → ℕ → Lt) : Prop where
  zero : ∀ z, pos z 0 = z
  add : ∀ z a b, pos (pos z a) b = pos z (a + b)
  period : ∀ z, pos z i = z

section Series

variable {K : Type} {Lt β : Type}

def logS [Field K] [DecidableEq Lt] [DecidableEq β] (l i : ℕ) (pos : Lt → ℕ → Lt) (v : Lt × β) : MvPowerSeries (Lt × β) K :=
  genLog l (fun y : Lt × β => (pos y.1 (2 * (i - 1)), y.2)) v

def beS [Field K] [Fintype β] (i : ℕ) (pos : Lt → ℕ → Lt) (R : Finset Lt) (sg : Lt → K)
    (be : Lt → MvPowerSeries (ZMod (2 * i)) K) : MvPowerSeries (Lt × β) K :=
  ∑ r ∈ R, (sg r / 2) • ∑ b : β,
    MvPowerSeries.subst (fun s : ZMod (2 * i) => (MvPowerSeries.X (pos r s.val, b) : MvPowerSeries (Lt × β) K)) (be r)

def ShapeS [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) (pos : Lt → ℕ → Lt)
    (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K) (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ U : MvPowerSeries (Lt × β) K, Integral U ∧
    MvPowerSeries.subst (fun v : Lt × β => MvPowerSeries.C ep * logS (K := K) l i pos v) Th =
      U * MvPowerSeries.subst (logS (K := K) (β := β) l i pos) (mvExp (beS i pos R sg be))

def HasThetaProductForm [NormedField K] [CharZero K] [DecidableEq Lt] [DecidableEq β] [Fintype β] (l i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt)
    (Th : MvPowerSeries (Lt × β) K) : Prop :=
  ∃ (K0 : Subfield K) (ζ : K) (R : Finset Lt) (ep : K) (sg : Lt → K) (be : Lt → MvPowerSeries (ZMod (2 * i)) K),
    Unram l K0 ∧ IsPrimitiveRoot ζ (l ^ (2 * i) - 1) ∧ ‖ep‖ = 1 ∧ (∀ r ∈ R, sg r = 1 ∨ sg r = -1) ∧
      (∀ r ∈ R, BHyp l (2 * i) K0 ζ (be r)) ∧ ShapeS l i pos R ep sg be Th

def linS [Field K] {K0 : Type} [Field K0] (j : K0 →+* K) (σ : K0 →+* K0) (i : ℕ) [NeZero i] (pos : Lt → ℕ → Lt) (c : K0) (r : Lt)
    (b : β) : MvPowerSeries (Lt × β) K :=
  ∑ s : ZMod (2 * i), if s.val % 2 = 0 then MvPowerSeries.C (j (σ^[s.val] c)) * MvPowerSeries.X (pos r s.val, b) else 0

end Series

def IsRadii {Lt : Type} (l : ℕ) (pos : Lt → ℕ → Lt) (sig : Lt → ℝ) : Prop :=
  (∀ z, 0 ≤ sig z) ∧ ∀ z, ∀ e : ℕ, Odd e → 1 ≤ (l : ℝ) ^ e * sig z + sig (pos z e)

end UpperTheory.G2

end
end

-- bundled from Development.AutomorphicArithmetic.OrbitLabellings.SumDemandFilterTwoDivLeOfIsOptDual
section
open scoped BigOperators
open Formalism.IncomingBounds

theorem UpperTheory.sum_demand_filter_two_div_le_of_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D sig : ZMod d → ℝ, 0 ≤ D → IsOptDual l d D sig →
    (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s) ≤ (∑ s : ZMod d, D s) / l := by
  intro l d _ hl D sig hD hopt
  obtain ⟨⟨x, hx, hxv⟩, -⟩ := UpperTheory.exists_maxFlow_attained_and_isOptDual l d hl D hD
  have hl0 : (0 : ℝ) < l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hl1 : (1 : ℝ) ≤ l := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hin_nn : ∀ s : ZMod d, 0 ≤ ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
    fun s => Finset.sum_nonneg fun i _ => hx.1 _ _
  have hF : ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s ≤ flowVal d x := by
    calc ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s
        = ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s),
            ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
          refine Finset.sum_congr rfl fun s hs => ?_
          exact (FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.mp hs).2 x hx hxv).2
      _ ≤ ∑ s, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun s _ _ => hin_nn s
      _ = flowVal d x := by
          unfold flowVal
          exact FlowDualityReindexing.in_reindex x
  have hout : ∀ s : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x s i
      ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hodd : Odd i := (Finset.mem_filter.mp hi).2
    have hi1 : 1 ≤ i := hodd.pos
    have hpow : (l : ℝ) ≤ (l : ℝ) ^ i := by
      calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl1 hi1
    exact mul_le_mul_of_nonneg_right hpow (hx.1 s i)
  have htot : (l : ℝ) * flowVal d x + flowVal d x ≤ ∑ s, D s := by
    have h := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => hx.2 s
    rw [Finset.sum_add_distrib, FlowDualityReindexing.in_reindex x] at h
    have h2 : (l : ℝ) * flowVal d x ≤ ∑ s, ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i := by
      unfold flowVal
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => hout s
    unfold flowVal at h2 ⊢
    linarith
  have hFnn : 0 ≤ flowVal d x :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => hx.1 _ _
  rw [le_div_iff₀ hl0]
  nlinarith
end

