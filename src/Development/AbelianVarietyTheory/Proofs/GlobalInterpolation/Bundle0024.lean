module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteBox
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroBand

theorem finite_box (f : ℂ → ℂ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite) (T : ℝ) :
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0}.Finite := by
  refine Set.Finite.subset
    ((Finset.Icc ⌊-T⌋ ⌊T⌋).finite_toSet.biUnion fun k _ => hW (k : ℝ)) ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  rw [abs_lt] at h2
  refine Set.mem_iUnion₂.2 ⟨⌊ρ.im⌋, ?_, h0, h1, ?_, h3⟩
  · rw [Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.floor_mono h2.1.le, Int.floor_mono h2.2.le⟩
  · rw [abs_le]
    constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]

theorem norm_term_le (m : ℕ) {u T : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) {ρ : ℂ} (h1 : ρ.re < 1)
    (h2 : T ≤ |ρ.im|) : ‖(m : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (m : ℝ) * (u / T) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hρ : T ≤ ‖ρ‖ := h2.trans (Complex.abs_im_le_norm ρ)
  have hρ0 : 0 < ‖ρ‖ := hT0.trans_le hρ
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  have hup : u ^ ρ.re ≤ u := by
    calc u ^ ρ.re ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h1.le
      _ = u := Real.rpow_one u
  calc u ^ ρ.re / ‖ρ‖ ≤ u / ‖ρ‖ := div_le_div_of_nonneg_right hup hρ0.le
    _ ≤ u / T := div_le_div_of_nonneg_left hu0.le hT0 hρ

theorem band_le (f : ℂ → ℂ) (m : ℂ → ℕ) (B : ℝ → ℝ)
    (hW : ∀ t : ℝ, {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}.Finite ∧
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ f ρ = 0}, (m ρ : ℝ) ≤ B t)
    {u T T' : ℝ} (hT : 2 ≤ T) (hu : T ≤ u) (hT1 : T ≤ T') (hT2 : T' ≤ T + 1) :
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)) -
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ f ρ = 0},
        (m ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ (B T + B (-T)) * (u / T) := by
  classical
  have hT0 : 0 < T := by linarith
  have hS' := finite_box f (fun t => (hW t).1) T'
  have hS := finite_box f (fun t => (hW t).1) T
  have hA := (hW T).1
  have hA' := (hW (-T)).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hS', finsum_mem_eq_finite_toFinset_sum _ hS]
  have hsub : hS.toFinset ⊆ hS'.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨a, b, c, d⟩ := hρ
    exact ⟨a, b, c.trans_le hT1, d⟩
  rw [← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hD : ∀ ρ ∈ hS'.toFinset \ hS.toFinset,
      ρ ∈ hA.toFinset ∪ hA'.toFinset ∧ ρ.re < 1 ∧ T ≤ |ρ.im| := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hρ
    rw [Set.Finite.mem_toFinset] at h1 h2
    obtain ⟨a, b, c, d⟩ := h1
    have hT' : T ≤ |ρ.im| := not_lt.1 fun h => h2 ⟨a, b, h, d⟩
    refine ⟨?_, b, hT'⟩
    rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    rw [abs_lt] at c
    rcases le_or_gt 0 ρ.im with h | h
    · left
      rw [abs_of_nonneg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
    · right
      rw [abs_of_neg h] at hT'
      refine ⟨a, b, ?_, d⟩
      rw [abs_le]
      constructor <;> linarith
  have hm : ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) ≤ B T + B (-T) := by
    calc ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)
        ≤ ∑ ρ ∈ hA.toFinset ∪ hA'.toFinset, (m ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hD ρ hρ).1)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hA.toFinset, (m ρ : ℝ) + ∑ ρ ∈ hA'.toFinset, (m ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      _ ≤ B T + B (-T) := by
          rw [← finsum_mem_eq_finite_toFinset_sum _ hA, ← finsum_mem_eq_finite_toFinset_sum _ hA']
          exact add_le_add (hW T).2 (hW (-T)).2
  calc _ ≤ ∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ) * (u / T) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
        obtain ⟨-, h1, h2⟩ := hD ρ hρ
        exact norm_term_le (m ρ) hT hu h1 h2
    _ = (∑ ρ ∈ hS'.toFinset \ hS.toFinset, (m ρ : ℝ)) * (u / T) := by rw [Finset.sum_mul]
    _ ≤ (B T + B (-T)) * (u / T) :=
        mul_le_mul_of_nonneg_right hm (div_nonneg (by linarith) hT0.le)

theorem zeros_band : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T T' : ℝ, 2 ≤ T → T ≤ u → T ≤ T' → T' ≤ T + 1 → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)) - ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T) := by
  obtain ⟨C, hC, hcount⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨2 * C, by linarith, ?_⟩
  intro N _ χ hχ u T T' hT hu hT1 hT2
  have hw := hcount N χ hχ
  refine ⟨finite_box _ (fun t => (hw t).1) T, ?_⟩
  refine (band_le (LFunction χ) (fun ρ => analyticOrderNatAt (LFunction χ) ρ)
    (fun t => C * Real.log (N * (|t| + 2))) hw hT hu hT1 hT2).trans ?_
  have hT0 : 0 < T := by linarith
  rw [abs_neg, abs_of_pos hT0]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have huT : T + 2 ≤ u * T := by nlinarith
  have hx : (N : ℝ) * (T + 2) ≤ N * u * T := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left huT (by linarith)
  have hpos : 0 < (N : ℝ) * (T + 2) := by positivity
  have hL1 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) := Real.log_le_log hpos hx
  have h4 : (4 : ℝ) ≤ N * u * T := by nlinarith
  have hL : 1 ≤ Real.log (N * u * T) := by
    have he : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    exact ((Real.lt_log_iff_exp_lt (by linarith)).2 (by linarith)).le
  have hL2 : Real.log (N * (T + 2)) ≤ Real.log (N * u * T) ^ 2 := hL1.trans (by nlinarith)
  have hq : 0 ≤ u / T := div_nonneg (by linarith) hT0.le
  calc (C * Real.log (N * (T + 2)) + C * Real.log (N * (T + 2))) * (u / T)
      = 2 * C * Real.log (N * (T + 2)) * (u / T) := by ring
    _ ≤ 2 * C * Real.log (N * u * T) ^ 2 * (u / T) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by linarith)) hq
    _ = 2 * C * (u * Real.log (N * u * T) ^ 2 / T) := by ring

end GlobalTheory.ZeroBand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GaussianOddJacobiThetaEqDerivMulSgStar
section
open Complex

noncomputable section

namespace GlobalTheory.SgStarOddTheta

open Formalism.L2.Th1.F

theorem jacobiTheta₂_add_int_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      cexp (-(Real.pi : ℂ) * I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

theorem oddTheta_add (τ : UpperHalfPlane) (z : ℂ) (m k : ℤ) :
    GlobalTheory.ThetaWeberRoad.oddTheta τ (z + (m * (τ : ℂ) + k)) =
      cexp ((Real.pi : ℂ) * I * (k - m - m ^ 2 * (τ : ℂ) - 2 * m * z)) *
        GlobalTheory.ThetaWeberRoad.oddTheta τ z := by
  unfold GlobalTheory.ThetaWeberRoad.oddTheta
  rw [show z + (m * (τ : ℂ) + k) + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + (m * (τ : ℂ) + k) by ring,
    jacobiTheta₂_add_int_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

theorem exp_pi_I_int (j : ℤ) : cexp ((Real.pi : ℂ) * I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

theorem area_periodPairOfTau (τ : UpperHalfPlane) : area (GlobalTheory.periodPairOfTau τ) = τ.im := by
  simp [area, GlobalTheory.periodPairOfTau, abs_of_pos τ.im_pos]

theorem semiChar_periodPairOfTau (τ : UpperHalfPlane) (m k : ℤ) :
    semiChar (GlobalTheory.periodPairOfTau τ) (m * (τ : ℂ) + k) =
      cexp ((Real.pi : ℂ) * I * ((k - m + m * k : ℤ) : ℂ)) := by
  have hpar : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  have hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨p, q, e⟩
      have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
        push_cast
        linear_combination -2 * e
      have h1 := congrArg Complex.im e1
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
      rw [h1, add_right_inj, Int.cast_inj] at e1
      exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, by push_cast; ring⟩
  rw [exp_pi_I_int, semiChar]
  by_cases h : Even m ∧ Even k
  · rw [if_pos (hmem.2 h), if_pos (hpar.2 h)]
  · rw [if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]

def expOddTheta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z

theorem differentiable_expOddTheta (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by
  have := GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ
  unfold expOddTheta
  fun_prop

theorem expOddTheta_law (τ : UpperHalfPlane) : ∀ ω ∈ (GlobalTheory.periodPairOfTau τ).lattice, ∀ z,
    semiChar (GlobalTheory.periodPairOfTau τ) ω * opU (GlobalTheory.periodPairOfTau τ) ω (expOddTheta τ) z =
      expOddTheta τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ ω).1 hω
  simp only [one_mul]
  rw [semiChar_periodPairOfTau, opU, herm, herm, area_periodPairOfTau, expOddTheta, expOddTheta,
    oddTheta_add]
  have hE : ∀ A B C D w : ℂ, cexp A * (cexp B * (cexp C * w) * cexp D) = cexp (A + B + C + D) * w := by
    intros
    simp only [Complex.exp_add]
    ring
  rw [hE]
  congr 1
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨k - m + m * k, ?_⟩
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * I := by
    apply Complex.ext <;> simp
    ring
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  simp only [map_add (f := _), map_mul, map_intCast, hc]
  field_simp
  push_cast
  ring

theorem exp_mul_oddTheta_eq_deriv_mul_sgStar :
    Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ),
      Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  intro hTL hSB τ z
  obtain ⟨c, hc⟩ := hTL _ (expOddTheta τ) (differentiable_expOddTheta τ) (expOddTheta_law τ)
  have hfun : expOddTheta τ = fun z => c * sgStar (GlobalTheory.periodPairOfTau τ) z := funext hc
  obtain ⟨hdiff, -, -, hd1, -⟩ := hSB (GlobalTheory.periodPairOfTau τ)
  have h1 : deriv (expOddTheta τ) 0 = c := by
    rw [hfun]
    have := ((hdiff 0).hasDerivAt.const_mul c).deriv
    rw [hd1, mul_one] at this
    exact this
  have he : HasDerivAt (fun z : ℂ => cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ)))) 0 0 := by
    have := (((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const
      (2 * ((τ.im : ℝ) : ℂ))).cexp
    simpa using this
  have h2 : deriv (expOddTheta τ) 0 = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 := by
    have := (he.mul (GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ 0).hasDerivAt).deriv
    simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, Complex.exp_zero, one_mul] at this
    exact this
  have := hc z
  rw [expOddTheta] at this
  rw [this, ← h1, h2]

end GlobalTheory.SgStarOddTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodDiffThetaFourthOfSigmaStarAddition
section
open Complex
open scoped Real

noncomputable section

namespace GlobalTheory.ThetaWeberRoad

theorem exp_half_pi_I : cexp ((π : ℂ) * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring]
  exact Complex.exp_pi_div_two_mul_I

theorem exp_neg_half_pi_I : cexp (-((π : ℂ) * I / 2)) = -I := by
  rw [show -((π : ℂ) * I / 2) = -π / 2 * I by ring]
  exact Complex.exp_neg_pi_div_two_mul_I

theorem neg_cexp (x : ℂ) : -cexp x = cexp ((π : ℂ) * I + x) := by
  rw [Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul]

theorem I_mul_cexp (x : ℂ) : I * cexp x = cexp ((π : ℂ) * I / 2 + x) := by
  rw [Complex.exp_add, exp_half_pi_I]

theorem negI_mul_cexp (x : ℂ) : -I * cexp x = cexp (-((π : ℂ) * I / 2) + x) := by
  rw [Complex.exp_add, exp_neg_half_pi_I]

theorem thetaConst_zero_zero (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ = jacobiTheta₂ 0 τ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]

theorem thetaConst_zero_one (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ = jacobiTheta₂ (1 / 2) τ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]

theorem thetaConst_one_zero (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ =
      cexp ((π : ℂ) * I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst
  push_cast
  congr 2 <;> ring

theorem oddTheta_eq_of (τ : UpperHalfPlane) (z w k : ℂ)
    (h : jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ = cexp k * jacobiTheta₂ w τ) :
    oddTheta τ z = cexp ((π : ℂ) * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2) + k) * jacobiTheta₂ w τ := by
  unfold oddTheta
  rw [h, ← mul_assoc, ← Complex.exp_add]

theorem oddTheta_half (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2) = -GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ := by
  have h : jacobiTheta₂ (1 / 2 + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    rw [show (1 : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = (τ : ℂ) / 2 + 1 by ring, jacobiTheta₂_add_left,
      Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_one_zero, ← neg_mul, neg_cexp]
  congr 2
  ring

theorem oddTheta_tau_half (τ : UpperHalfPlane) :
    oddTheta τ ((τ : ℂ) / 2) =
      -I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ ((τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * (1 / 2))) * jacobiTheta₂ (1 / 2) τ := by
    rw [show (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 1 / 2 + (τ : ℂ) by ring, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, negI_mul_cexp]
  congr 2
  ring

theorem oddTheta_one_add_tau_half (τ : UpperHalfPlane) :
    oddTheta τ ((1 + (τ : ℂ)) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ ((1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * (τ : ℂ)) * jacobiTheta₂ 0 τ := by
    rw [show (1 + (τ : ℂ)) / 2 + ((τ : ℂ) + 1) / 2 = (0 + 1) + (τ : ℂ) by ring, jacobiTheta₂_add_left',
      jacobiTheta₂_add_left]
    congr 1
    rw [show -(π : ℂ) * I * ((τ : ℂ) + 2 * (0 + 1)) = -π * I * (τ : ℂ) - 2 * π * I by ring,
      Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring

theorem oddTheta_one_sub_tau_half (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2 - (τ : ℂ) / 2) =
      -cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ := by
  have h : jacobiTheta₂ (1 / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ 0 τ := by
    rw [show (1 : ℂ) / 2 - (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = 0 + 1 by ring, jacobiTheta₂_add_left,
      Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_zero, neg_cexp]
  congr 2
  ring

theorem oddTheta_one_add_tau_half' (τ : UpperHalfPlane) :
    oddTheta τ (1 + (τ : ℂ) / 2) =
      I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ (1 + (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * (1 / 2))) * jacobiTheta₂ (1 / 2) τ := by
    rw [show 1 + (τ : ℂ) / 2 + ((τ : ℂ) + 1) / 2 = (1 / 2 + (τ : ℂ)) + 1 by ring, jacobiTheta₂_add_left,
      jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, I_mul_cexp]
  congr 2
  ring

theorem oddTheta_neg_tau_half (τ : UpperHalfPlane) :
    oddTheta τ (-((τ : ℂ) / 2)) =
      I * cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ := by
  have h : jacobiTheta₂ (-((τ : ℂ) / 2) + ((τ : ℂ) + 1) / 2) τ = cexp 0 * jacobiTheta₂ (1 / 2) τ := by
    rw [show -((τ : ℂ) / 2) + ((τ : ℂ) + 1) / 2 = 1 / 2 by ring, Complex.exp_zero, one_mul]
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_zero_one, I_mul_cexp]
  congr 2
  ring

theorem oddTheta_half_add_tau (τ : UpperHalfPlane) :
    oddTheta τ (1 / 2 + (τ : ℂ)) =
      -(cexp (-((π : ℂ) * I * (τ : ℂ))) * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) := by
  have h : jacobiTheta₂ (1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2) τ =
      cexp (-π * I * ((τ : ℂ) + 2 * ((τ : ℂ) / 2))) * jacobiTheta₂ ((τ : ℂ) / 2) τ := by
    rw [show 1 / 2 + (τ : ℂ) + ((τ : ℂ) + 1) / 2 = ((τ : ℂ) / 2 + (τ : ℂ)) + 1 by ring,
      jacobiTheta₂_add_left, jacobiTheta₂_add_left']
  rw [oddTheta_eq_of τ _ _ _ h, thetaConst_one_zero, ← mul_assoc, ← Complex.exp_add, ← neg_mul, neg_cexp]
  congr 2
  ring

private theorem g_add_mul_g_sub_of_addition_laws (E g σ : ℂ → ℂ) (c Δ z w : ℂ)
    (hE : E (z + w) * E (z - w) = E z ^ 2 * E w ^ 2) (hz : E z ≠ 0) (hw : E w ≠ 0)
    (hI : ∀ u, E u * g u = c * σ u) (hσ : σ (z + w) * σ (z - w) = -(σ z ^ 2 * σ w ^ 2 * Δ)) :
    c ^ 2 * (g (z + w) * g (z - w)) = -(g z ^ 2 * g w ^ 2 * Δ) := by
  have h0 : E z ^ 2 * E w ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ hw)
  apply mul_left_cancel₀ h0
  have h1 := hI (z + w)
  have h2 := hI (z - w)
  have h3 := hI z
  have h4 := hI w
  calc E z ^ 2 * E w ^ 2 * (c ^ 2 * (g (z + w) * g (z - w)))
      = c ^ 2 * ((E (z + w) * g (z + w)) * (E (z - w) * g (z - w))) := by rw [← hE]; ring
    _ = c ^ 4 * (σ (z + w) * σ (z - w)) := by rw [h1, h2]; ring
    _ = -((c * σ z) ^ 2 * (c * σ w) ^ 2 * Δ) := by rw [hσ]; ring
    _ = -((E z * g z) ^ 2 * (E w * g w) ^ 2 * Δ) := by rw [h3, h4]
    _ = E z ^ 2 * E w ^ 2 * -(g z ^ 2 * g w ^ 2 * Δ) := by ring

theorem oddTheta_addition (hSA : Formalism.L2.Th1.F.SgStarAdd) (τ : UpperHalfPlane)
    (hI : ∀ z : ℂ, Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * oddTheta τ z =
      deriv (oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z)
    (z w : ℂ) (hz : z ∉ (GlobalTheory.periodPairOfTau τ).lattice) (hw : w ∉ (GlobalTheory.periodPairOfTau τ).lattice) :
    deriv (oddTheta τ) 0 ^ 2 * (oddTheta τ (z + w) * oddTheta τ (z - w)) =
      -(oddTheta τ z ^ 2 * oddTheta τ w ^ 2 *
        (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ z - GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp τ w)) := by
  have hσ := hSA (GlobalTheory.periodPairOfTau τ) z w hz hw
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.wp
  refine g_add_mul_g_sub_of_addition_laws (fun u => Complex.exp ((Real.pi : ℂ) * u ^ 2 / (2 * ((τ.im : ℝ) : ℂ))))
    (oddTheta τ) (Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ)) _ _ z w ?_ (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _) hI hσ
  simp only [← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem d_eq_sq_mul_pow_four_of_relations (p A B C g c e d1 d2 d3 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hc : c ≠ 0) (hg : g ^ 2 = p ^ 2 * (A * B * C) ^ 2) (hc4 : c ^ 4 = e)
    (e1 : g ^ 2 * (-c * A * (-c * A)) = -((-C) ^ 2 * (-I * c * B) ^ 2 * d1))
    (e2 : g ^ 2 * (I * c * B * (I * c * B)) = -((-C) ^ 2 * (-c * A) ^ 2 * d2))
    (e3 : g ^ 2 * (-(e * C) * -C) = -((-c * A) ^ 2 * (-I * c * B) ^ 2 * d3)) :
    d1 = p ^ 2 * A ^ 4 ∧ d2 = p ^ 2 * B ^ 4 ∧ d3 = p ^ 2 * C ^ 4 := by
  rw [hg] at e1 e2 e3
  rw [← hc4] at e3
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  refine ⟨?_, ?_, ?_⟩
  · have h : (c ^ 2 * B ^ 2 * C ^ 2) * d1 = (c ^ 2 * B ^ 2 * C ^ 2) * (p ^ 2 * A ^ 4) := by
      linear_combination (-1 : ℂ) * e1 + C ^ 2 * c ^ 2 * B ^ 2 * d1 * hI2
    exact mul_left_cancel₀ (by simp [hc, hB, hC]) h
  · have h : (c ^ 2 * A ^ 2 * C ^ 2) * d2 = (c ^ 2 * A ^ 2 * C ^ 2) * (p ^ 2 * B ^ 4) := by
      linear_combination e2 - p ^ 2 * A ^ 2 * B ^ 4 * C ^ 2 * c ^ 2 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hC]) h
  · have h : (c ^ 4 * A ^ 2 * B ^ 2) * d3 = (c ^ 4 * A ^ 2 * B ^ 2) * (p ^ 2 * C ^ 4) := by
      linear_combination (-1 : ℂ) * e3 + c ^ 4 * A ^ 2 * B ^ 2 * d3 * hI2
    exact mul_left_cancel₀ (by simp [hc, hA, hB]) h

theorem halfPeriodDiff_of : Formalism.L2.Th1.F.SgStarAdd →
    (∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) *
      GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z) →
    (∀ τ : UpperHalfPlane, HasDerivAt (GlobalTheory.ThetaWeberRoad.oddTheta τ)
      (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0) →
    (∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ) →
    ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ := by
  intro hSA hI hD hJ τ
  obtain ⟨n1, n2, n3⟩ := GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem τ
  have hd : deriv (oddTheta τ) 0 = -2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3 := (hD τ).deriv
  have hJ' : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ = 2 * ModularForm.eta (τ : ℂ) ^ 3 := hJ τ
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hABC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := by
    rw [hJ']
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have hA : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ ≠ 0 := fun h => hABC (by rw [h]; ring)
  have hg : deriv (oddTheta τ) 0 ^ 2 = (π : ℂ) ^ 2 * (GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ *
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 1 τ * GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 1 0 τ) ^ 2 := by
    rw [hd, hJ']
    ring
  have hc4 : cexp (-((π : ℂ) * I * (τ : ℂ) / 4)) ^ 4 = cexp (-((π : ℂ) * I * (τ : ℂ))) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e1 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((τ : ℂ) / 2) n1 n2
  have e2 := oddTheta_addition hSA τ (hI τ) (1 / 2) ((1 + (τ : ℂ)) / 2) n1 n3
  have e3 := oddTheta_addition hSA τ (hI τ) ((1 + (τ : ℂ)) / 2) ((τ : ℂ) / 2) n3 n2
  rw [show (1 : ℂ) / 2 + (τ : ℂ) / 2 = (1 + (τ : ℂ)) / 2 by ring] at e1
  rw [show (1 : ℂ) / 2 + (1 + (τ : ℂ)) / 2 = 1 + (τ : ℂ) / 2 by ring,
    show (1 : ℂ) / 2 - (1 + (τ : ℂ)) / 2 = -((τ : ℂ) / 2) by ring] at e2
  rw [show (1 + (τ : ℂ)) / 2 + (τ : ℂ) / 2 = 1 / 2 + (τ : ℂ) by ring,
    show (1 + (τ : ℂ)) / 2 - (τ : ℂ) / 2 = 1 / 2 by ring] at e3
  rw [oddTheta_one_add_tau_half, oddTheta_one_sub_tau_half, oddTheta_half, oddTheta_tau_half] at e1
  rw [oddTheta_one_add_tau_half', oddTheta_neg_tau_half, oddTheta_half, oddTheta_one_add_tau_half] at e2
  rw [oddTheta_half_add_tau, oddTheta_half, oddTheta_one_add_tau_half, oddTheta_tau_half] at e3
  exact d_eq_sq_mul_pow_four_of_relations _ _ _ _ _ _ _ _ _ _ hA hB hC (Complex.exp_ne_zero _) hg hc4 e1 e2 e3

end GlobalTheory.ThetaWeberRoad
end
end

