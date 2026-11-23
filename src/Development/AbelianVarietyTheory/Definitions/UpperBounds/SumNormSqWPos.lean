module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Up

open Classical in
noncomputable def Wdiv {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) *
    ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
    ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0

section API

variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}

theorem Wdiv_of_mem (hx : x ∈ X.dom) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-phla X Xa.Fp x)) *
      ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) *
      ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) := by
  unfold Wdiv
  rw [if_pos hx]

theorem sum_normSq_pos {N : ℕ} {a : Fin N → ℂ} (h : ∃ k, a k ≠ 0) : 0 < ∑ k, ‖a k‖ ^ 2 := by
  obtain ⟨k, hk⟩ := h
  exact Finset.sum_pos' (fun _ _ => by positivity)
    ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk) 2⟩

theorem sum_normSq_w_pos (hx : x ∈ X.dom) : 0 < ∑ k, ‖Xa.w k x‖ ^ 2 :=
  sum_normSq_pos (Xa.w_nz x hx)

theorem Wdiv_eq_top (hn : 1 ≤ n) (hx : x ∈ X.dom) (hs : ∀ k, Fl.s k x = 0) :
    Wdiv X Xa Fl n x = ⊤ := by
  have hw := sum_normSq_w_pos Xa hx
  have hn' : -((n : ℝ) - 1 / 2) < 0 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h0 : ∑ k, ‖Fl.s k x‖ ^ 2 = 0 := by simp [hs]
  rw [Wdiv_of_mem Xa Fl n hx, h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hn',
    ENNReal.ofReal_rpow_of_pos hw, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.mul_top]
  exact (ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hw _))).ne'

theorem phla_add_nsmul (hx : x ∈ X.dom) (la la' : Wt X.Ψ r) (k : ℕ) :
    phla X (la + k • la') x = phla X la x + k * phla X la' x := by
  rw [IW.phla_eq X hx, IW.phla_eq X hx, IW.phla_eq X hx, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem pnorm_sq_eq_exp (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    X.pnorm la P x ^ 2 = Real.exp (-phla X la x) * ‖P x‖ ^ 2 := by
  have hpos : 0 < X.nfac la x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos
      (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _
  have h : Real.exp (-phla X la x) = X.nfac la x ^ 2 := by
    unfold phla
    rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) * ((2 : ℕ) : ℝ) by
      push_cast; ring, Real.exp_mul, Real.exp_log hpos, Real.rpow_natCast]
  rw [h]
  show (‖P x‖ * X.nfac la x) ^ 2 = _
  ring

end API

end GlobalTheory.Up
