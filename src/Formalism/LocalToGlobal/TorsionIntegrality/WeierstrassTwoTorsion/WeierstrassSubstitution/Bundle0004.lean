module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
public import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeJ
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

namespace Bridge

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem integral_of_coeff {f : K⟦X⟧} (h : ∀ n, coeff n f ∈ Formalism.G.unitBall K) :
    Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  have e : n = Finsupp.single () (n ()) := by
    ext
    simp
  have hn := h (n ())
  rw [e]
  exact hn

theorem integral_of_mvCoeff {ι : Type} {f : MvPowerSeries ι K}
    (h : ∀ n, MvPowerSeries.coeff n f ∈ Formalism.G.unitBall K) : Formalism.DworkPowerSeriesWeights.Integral f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  exact h n

theorem integral_map {ι : Type} (c : MvPowerSeries ι (Formalism.G.unitBall K)) :
    Formalism.DworkPowerSeriesWeights.Integral (MvPowerSeries.map (Formalism.G.unitBall K).subtype c) := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n c).2

def model (W : WeierstrassCurve K) (h : IntModel W) : WeierstrassCurve (Formalism.G.unitBall K) :=
  ⟨⟨W.a₁, h.1⟩, ⟨W.a₂, h.2.1⟩, ⟨W.a₃, h.2.2.1⟩, ⟨W.a₄, h.2.2.2.1⟩, ⟨W.a₆, h.2.2.2.2⟩⟩

theorem model_map (W : WeierstrassCurve K) (h : IntModel W) :
    (model W h).map (Formalism.G.unitBall K).subtype = W := by
  rfl

end Ball

end Bridge

open Bridge

theorem bridgeWp_of (h : WpCleared.{0}) : BridgeWp := by
  unfold BridgeWp
  intro K _ _ W
  exact h K W

theorem bridgeLaw_of (hM : CoeffMem.{0}) (hFL : FglLog.{0}) (hHS : HalfSpec.{0})
    (hHL : HalfLog.{0, 0}) : BridgeLaw := by
  intro K _ _ _ W hW
  obtain ⟨-, -, -, -, -, hi, hF, -, hh, -, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  obtain ⟨hl0, hl1, -, -⟩ := logSpec K W
  refine ⟨⟨(fglChord K W).2.2.2.2.1, integral_of_mvCoeff hF, hl0, hl1, ?_⟩,
    ⟨(iSerSpec K W).1, integral_of_coeff hi, (logNeg K W).1⟩, fun h2 => ?_⟩
  · unfold Formalism.InvariantFactorPaths.G7.cob Formalism.InvariantFactorPaths.G7.at1
    rw [(hFL K W).1]
    ring
  · have hu : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr two_ne_zero
    refine ⟨(hHS K W hu).1, integral_of_coeff (hh ⟨2⁻¹, ?_, mul_inv_cancel₀ two_ne_zero⟩), ?_⟩
    · change ‖(2 : K)⁻¹‖ ≤ 1
      rw [norm_inv, h2, inv_one]
    · have key := hHL.1 K W
      have h21 : (C (2 : K)⁻¹ : K⟦X⟧) * 2 = 1 := by
        rw [← map_ofNat (C : K →+* K⟦X⟧) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      calc (logSer W).subst (halfSer W)
          = (C (2 : K)⁻¹ * 2) * (logSer W).subst (halfSer W) := by rw [h21, one_mul]
        _ = C (2 : K)⁻¹ * (2 * (logSer W).subst (halfSer W)) := by ring
        _ = C (2 : K)⁻¹ * logSer W := by rw [key]

theorem bridgeCurve_of (hM : CoeffMem.{0}) (hU : WpInU.{0}) (hC : CubeTwoR.{0}) :
    BridgeCurve := by
  intro K _ _ _ W hW
  obtain ⟨-, hx, -⟩ :=
    hM K W (Formalism.G.unitBall K) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2
  refine ⟨integral_of_coeff hx, CurveSer.xS_cc W, hU K W, ?_⟩
  obtain ⟨c, hc0, hc⟩ := hC (Formalism.G.unitBall K) (model W hW)
  refine ⟨MvPowerSeries.map (Formalism.G.unitBall K).subtype c, integral_map c, ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hc0]
    simp
  · have hi0 : constantCoeff (iSer (model W hW)) = 0 := (iSerSpec _ (model W hW)).1
    have hs : MvPowerSeries.HasSubst
        (![U₁, (iSer (model W hW)).subst
            (U₂ : MvPowerSeries (Fin 2) (Formalism.G.unitBall K))] :
          Fin 2 → MvPowerSeries (Fin 2) (Formalism.G.unitBall K)) := by
      apply MvPowerSeries.hasSubst_of_constantCoeff_zero
      intro i
      fin_cases i
      · simp
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        exact PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X 1) _ hi0
    have key := congrArg (MvPowerSeries.map (Formalism.G.unitBall K).subtype) hc
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, MvPowerSeries.map_X,
      MvPowerSeries.map_X, PowerSeries.map_subst (HasSubst.X 0),
      PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, MvPowerSeries.map_X,
      CurveSer.map_xS, MvPowerSeries.map_subst hs, fglMap, model_map] at key
    unfold Formalism.L2.Th1.B.FI Formalism.InvariantFactorPaths.G7.at1
    rw [key]
    congr 2
    funext i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [PowerSeries.map_subst (HasSubst.X 1), MvPowerSeries.map_X, CurveSer.map_iSer, model_map]

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.BridgeK
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.A

theorem short_weierstrass_inverse : ShortInv := by
  unfold ShortInv
  intro K _ _ g2 g3
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [shortW, WeierstrassCurve.b₂]
    ring
  · unfold g₂
    simp only [shortW, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  · unfold g₃
    simp only [shortW, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    ring
  · simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring

namespace BridgeK

open Formalism.L2.Th1.CM

theorem cW_eq {K : Type} [Field K] (g2 g3 : K) (k : ℕ) :
    cW g2 g3 k = if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
      if 4 ≤ k then
        3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
          ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
      else 0 := by
  conv_lhs => unfold cW
  rw [Nat.strongRecOn_eq]
  simp only [dite_eq_ite]
  rfl

theorem cW_succ (hS : WpShape.{0}) (hR : WpRecursion.{0}) {K : Type} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (k : ℕ) :
    cW (g₂ W) (g₃ W) (k + 1) = coeff (2 * k) (wpReg W) := by
  obtain ⟨_, h0, _, h2, h4⟩ := hS K W
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · rw [cW_eq]
        simp [h0]
      · rw [cW_eq]
        simp [h2]
      · rw [cW_eq]
        simp [h4]
    · have hrec := hR K W k hk
      rw [cW_eq, if_neg (show k + 1 ≠ 2 by omega), if_neg (show k + 1 ≠ 3 by omega),
        if_pos (show 4 ≤ k + 1 by omega)]
      have hsum : (∑ m : Fin (k + 1 - 3), cW (g₂ W) (g₃ W) (m.val + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m.val + 2)))
          = ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W) := by
        rw [Fin.sum_univ_eq_sum_range (fun m => cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2)))
          (k + 1 - 3)]
        refine Finset.sum_nbij' (fun m => m + 1) (fun i => i - 1) ?_ ?_ ?_ ?_ ?_
        · intro a ha
          rw [Finset.mem_range] at ha
          rw [Finset.mem_Icc]
          omega
        · intro a ha
          rw [Finset.mem_Icc] at ha
          rw [Finset.mem_range]
          omega
        · intro a _
          show a + 1 - 1 = a
          omega
        · intro a ha
          rw [Finset.mem_Icc] at ha
          show a - 1 + 1 = a
          omega
        · intro m hm
          rw [Finset.mem_range] at hm
          show cW (g₂ W) (g₃ W) (m + 2) * cW (g₂ W) (g₃ W) (k + 1 - (m + 2))
            = coeff (2 * (m + 1)) (wpReg W) * coeff (2 * (k - 1 - (m + 1))) (wpReg W)
          rw [show m + 2 = m + 1 + 1 by omega, show k + 1 - (m + 1 + 1) = k - 2 - m + 1 by omega,
            ih (m + 1) (by omega), ih (k - 2 - m) (by omega), show k - 1 - (m + 1) = k - 2 - m by omega]
      rw [hsum]
      have hne1 : (2 * ((k : K) + 1) + 1) ≠ 0 := by
        have e : ((2 * k + 3 : ℕ) : K) = 2 * ((k : K) + 1) + 1 := by
          push_cast
          ring
        rw [← e]
        exact_mod_cast (show 2 * k + 3 ≠ 0 by omega)
      have hne2 : ((k : K) + 1 - 3) ≠ 0 := by
        have e : ((k - 2 : ℕ) : K) = (k : K) + 1 - 3 := by
          push_cast [Nat.cast_sub (show 2 ≤ k by omega)]
          ring
        rw [← e]
        exact_mod_cast (show k - 2 ≠ 0 by omega)
      push_cast
      rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero hne1 hne2)]
      linear_combination -hrec

end BridgeK

open BridgeK Formalism.L2.Th1.CM in
theorem wpNumEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : WpNumEq := by
  unfold WpNumEq
  intro K _ _ W
  obtain ⟨_, h0, hodd, _, _⟩ := hS K W
  constructor
  · ext n
    unfold wpNum
    rw [coeff_mk, map_add (f := _), coeff_one, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 1 with hj | hj
      · interval_cases j
        simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1)),
          if_neg (show 2 * (i + 1) ≠ 0 by omega), if_pos (show 2 ≤ 2 * (i + 1) by omega),
          Nat.mul_div_cancel_left (i + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1) - 2 = 2 * i by omega, cW_succ hS hR W i, zero_add]
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega), zero_add]
      split_ifs with h
      · rw [show 2 * j + 1 - 2 = 2 * (j - 1) + 1 by omega, hodd _ (odd_two_mul_add_one (j - 1))]
      · rfl
  · ext n
    unfold wpDen
    rw [coeff_mk, map_sub, coeff_one, mul_assoc (C (1 / 2 : K)) (X ^ 3) (derivative (wpReg W)),
      coeff_C_mul, coeff_X_pow_mul']
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · interval_cases j <;> simp
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by omega⟩
        rw [if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (even_two_mul (i + 1 + 1)),
          if_neg (show 2 * (i + 1 + 1) ≠ 0 by omega), if_pos (show 3 ≤ 2 * (i + 1 + 1) by omega),
          Nat.mul_div_cancel_left (i + 1 + 1) (by norm_num : 0 < 2),
          show 2 * (i + 1 + 1) - 3 = 2 * i + 1 by omega, coeff_derivative,
          show 2 * i + 1 + 1 = 2 * (i + 1) by ring, cW_succ hS hR W (i + 1)]
        push_cast
        ring
    · rw [if_neg (show 2 * j + 1 ≠ 0 by omega),
        if_neg (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one j)),
        if_neg (show 2 * j + 1 ≠ 0 by omega)]
      split_ifs with h
      · rw [show 2 * j + 1 - 3 = 2 * (j - 1) by omega, coeff_derivative,
          hodd _ (odd_two_mul_add_one (j - 1))]
        ring
      · ring

theorem uSerEq_of (hS : WpShape.{0}) (hR : WpRecursion.{0}) : USerEq := by
  intro K _ _ g2 g3
  obtain ⟨hb, hg2, hg3, -⟩ := short_weierstrass_inverse K g2 g3
  set W := shortW g2 g3 with hW
  obtain ⟨hnum, hden⟩ := wpNumEq_of hS hR K W
  rw [hg2, hg3] at hnum hden
  obtain ⟨hshape, -⟩ := hS K W
  obtain ⟨hd, -⟩ := wpODE.{0} K W
  obtain ⟨-, hfl⟩ := flowZ.{0} K W
  have hx : wpL W = xZ W := by
    rw [wpL, hb]; simp
  have ha1 : W.a₁ = 0 := rfl
  have ha3 : W.a₃ = 0 := rfl
  rw [ha1, ha3, map_zero, zero_mul, add_zero, add_zero] at hd

  have hrel : toL (expSer W) * dL (wpL W) = -2 * wpL W := by
    rw [hd, hx]; linear_combination 2 * hfl
  rw [hshape, map_add (f := _), dL_uPow, dL_toL] at hrel
  have h3 : (uPow (-2 - 1) : LaurentSeries K) * toL (X ^ 3) = 1 := by
    rw [← uPow_natCast]; exact uPow_neg_mul 3
  have h2 : (uPow (-2) : LaurentSeries K) * toL (X ^ 3) = toL X := by
    rw [← uPow_natCast, ← uPow_add, ← uPow_one]; norm_num
  have hC : (HahnSeries.C (((-2 : ℤ)) : K) : LaurentSeries K) = toL (C (-2 : K)) := by
    rw [toL_C]; norm_num
  have hps : expSer W * (C (-2 : K) + X ^ 3 * derivative (wpReg W)) =
      C (-2 : K) * (X + X ^ 3 * wpReg W) := by
    apply toL_injective
    have hm2 : (toL (C (-2 : K)) : LaurentSeries K) = -2 := by
      rw [map_neg C, map_neg toL]; congr 1
      rw [map_ofNat C, map_ofNat toL]
    simp only [map_mul, map_add (f := _)]
    rw [hC] at hrel
    linear_combination toL (X ^ 3) * hrel - toL (expSer W) * toL (C (-2 : K)) * h3 - 2 * h2
      - (toL X + toL (X ^ 3) * toL (wpReg W)) * hm2
  have hab : (C (1 / 2 : K) : K⟦X⟧) * C (-2 : K) = -1 := by
    rw [← map_mul]; norm_num
  have hcc : constantCoeff (CM.wpDen g2 g3) ≠ 0 := by
    rw [hden]; simp
  symm
  rw [CM.uSer, eq_mul_inv_iff_mul_eq hcc, hnum, hden]
  linear_combination -(C (1 / 2 : K) : K⟦X⟧) * hps + (expSer W - X - X ^ 3 * wpReg W) * hab

end Formalism.L2.Th1.A
end
end

