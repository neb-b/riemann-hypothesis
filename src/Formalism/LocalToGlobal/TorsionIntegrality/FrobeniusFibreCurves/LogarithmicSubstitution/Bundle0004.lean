module

public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Split

open Formalism.L2.Th1.C Formalism.L2.Th1.C.Pts Formalism.L2.Th1.C.Calc

variable {K : Type} [Field K] [CharZero K] {R : Subring K} {l linv ph : PowerSeries K}

theorem cong_smul {σ : Type} {z : K} (hz : IsBinomScalar R z) {f g : MvPowerSeries σ K}
    (h : Cong R f g) : Cong R (z • f) (z • g) := by
  have := lGBinom K R σ z hz _ h
  unfold Cong
  rwa [← smul_sub]

theorem lg_of_smul {σ : Type} {c : K} (hc : c ≠ 0) (hz : IsBinomScalar R c⁻¹)
    {f : MvPowerSeries σ K} (h : LG R (c • f)) : LG R f := by
  have := lGBinom K R σ _ hz _ h
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem biextension_formal_mul_mul (hF : Frame R l linv ph) {a b : K} (hN : PhNormAt R l linv ph a b)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y)) ((a * b) • be0 l linv ph x y) := by
  have e1 := phNorm_pt hF.1 hN (isPt_fadd hF.1 hF.2.1 hx hy)
  have e2 := phNorm_pt hF.1 hN hx
  have e3 := phNorm_pt hF.1 hN hy
  rw [fmul_fadd hF.1 a hx.1 hy.1] at e1
  have := cong_sub (cong_sub e1 e2) e3
  rw [← smul_sub, ← smul_sub] at this
  exact this

theorem biextension_vanishes_split (hF : Frame R l linv ph) {a b : K} (ha : EndInt R l linv a)
    (hB : IsBinomScalar R a) (hZ : ZLinAt R l linv ph a) (hN : PhNormAt R l linv ph a b)
    (hc : a * (a - b) ≠ 0) (hinv : IsBinomScalar R (a * (a - b))⁻¹)
    {σ : Type} {x y : MvPowerSeries σ K} (hx : IsPt R x) (hy : IsPt R y) :
    LG R (be0 l linv ph x y) := by
  have hax : IsPt R (fmul l linv a x) := isPt_fmul hF.1 ha hx
  have e1 : Cong R (be0 l linv ph (fmul l linv a x) (fmul l linv a y))
      (a • be0 l linv ph (fmul l linv a x) y) := hZ σ _ _ hax hy
  have e2 : Cong R (be0 l linv ph (fmul l linv a x) y) (a • be0 l linv ph x y) := by
    have := hZ σ y x hy hx
    rwa [addDefect_comm ph y (fmul l linv a x), addDefect_comm ph y x] at this
  have e3 : Cong R (a • a • be0 l linv ph x y) ((a * b) • be0 l linv ph x y) :=
    cong_trans (cong_symm (cong_trans e1 (cong_smul hB e2))) (biextension_formal_mul_mul hF hN hx hy)
  refine lg_of_smul hc hinv ?_
  have e : (a * (a - b)) • be0 l linv ph x y =
      a • a • be0 l linv ph x y - (a * b) • be0 l linv ph x y := by
    rw [smul_smul, ← sub_smul, mul_sub]
  rw [e]
  exact e3

theorem phNorm_one_iff (c : K) :
    PhNormAt R l linv ph c 1 ↔
      Cong R (PowerSeries.subst (fmul l linv c (PowerSeries.X : MvPowerSeries Unit K)) ph)
        (c • (ph : MvPowerSeries Unit K)) := by
  rw [PhNormAt, mulBy_eq_fmul, mul_one]

theorem phNorm_natCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℕ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  have hXs : PowerSeries.subst (PowerSeries.X : MvPowerSeries Unit K) ph = ph :=
    PowerSeries.X_subst ph
  rw [phNorm_one_iff]
  induction n with
  | zero =>
    rw [Nat.cast_zero, fmul_zero_left hF.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2,
      zero_smul]
    exact cong_refl _
  | succ n ih =>
    have k := key _ _ (isPt_fmul hF.1 (Clo.endInt_natCast hF.1 hF.2.1 n) hX) hX
    rw [be0, hXs] at k
    rw [Nat.cast_succ, fmul_add hF.1 _ _ hX.1, fmul_one hF.1 hX.1, add_smul, one_smul]
    have := lg_add k ih
    unfold Cong
    convert this using 1
    abel

theorem phNorm_intCast (hF : Frame R l linv ph)
    (key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y)) (n : ℤ) :
    PhNormAt R l linv ph (n : K) 1 := by
  have hX : IsPt R (PowerSeries.X : MvPowerSeries Unit K) := isPt_X
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [Int.cast_natCast]
    exact phNorm_natCast hF key m
  · rw [Int.cast_neg, Int.cast_natCast]
    have hm := Clo.endInt_natCast (R := R) hF.1 hF.2.1 m
    have k := key _ _ (isPt_fmul hF.1 hm hX) (isPt_fmul hF.1 (endInt_neg hF.1 hF.2.1 hm) hX)
    rw [be0, fadd_fmul_neg hF.1 _ hX.1, PowerSeries.subst_zero_of_constantCoeff_zero hF.2.2] at k
    have h1 := (phNorm_one_iff (R := R) (l := l) (linv := linv) (ph := ph) (m : K)).1
      (phNorm_natCast hF key m)
    rw [phNorm_one_iff, neg_smul]
    have := lg_neg (lg_add k h1)
    unfold Cong
    convert this using 1
    abel

theorem split_vanishing_at_two : Formalism.L2.Th1.G.SplitVanishTwo := by
  intro K _ _ _ _ R hR l linv ph a b hF hF1 ha hcl hN ha0 hab hb1 hi1 hi2
  have hl := hF.1.1
  have hli := hF.1.2.2.1
  have hph := hF.2.2
  have hB : IsBinomScalar R a := by
    refine closure_minimal ?_ (binomClosed K R hR) hcl
    rintro _ ⟨n, rfl⟩
    exact intBinomScalar K R n
  have hZ : ZLinAt R l linv ph a := by
    refine closure_minimal ?_ (zLinClosed K R hR l linv ph hl hli hph) hcl
    rintro _ ⟨n, rfl⟩
    exact zLinInt K R l linv ph hF hF1 n
  have key : ∀ x y : MvPowerSeries Unit K, IsPt R x → IsPt R y → LG R (be0 l linv ph x y) :=
    fun x y hx hy =>
      biextension_vanishes_split hF ha hB hZ hN (mul_ne_zero ha0 (sub_ne_zero.2 hab)) hi1 hx hy
  have hA : PhNormAt R l linv ph a 1 := by
    have hc : IsClosed {c : K | PhNormAt R l linv ph c 1} :=
      (phNormClosed K R hR l linv ph hl hli hph).preimage
        (continuous_id.prodMk continuous_const)
    refine closure_minimal ?_ hc hcl
    rintro _ ⟨n, rfl⟩
    exact phNorm_intCast hF key n
  refine lg_of_smul (mul_ne_zero ha0 (sub_ne_zero.2 (Ne.symm hb1))) hi2 ?_
  have e3 : Cong R ((a * 1) • (ph : MvPowerSeries Unit K)) ((a * b) • ph) :=
    cong_trans (cong_symm hA) hN
  have e : (a * (1 - b)) • (ph : MvPowerSeries Unit K) = (a * 1) • ph - (a * b) • ph := by
    rw [← sub_smul, mul_sub]
  rw [e]
  exact e3

end Formalism.L2.Th1.B.Split
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne
section
noncomputable section

namespace Formalism.L2.Th1.B.Crv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.L2.Th1.A (fgl iSer logSer wpReg g₂ g₃ IntModel xS bridgeWp bridgeLaw bridgeCurve)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem kap_eq (W : WeierstrassCurve K) (xT yT : K) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) :
    kapW W xT = 3 * xT ^ 2 + 2 * W.a₂ * xT + W.a₄ - W.a₁ * yT := by
  unfold kapW e1W g₂ WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
  linear_combination (W.a₁ / 2) * h2

theorem two_torsion_x_root_of_cubic (W : WeierstrassCurve K) (xT yT : K) (hE : W.toAffine.Equation xT yT)
    (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) :
    4 * e1W W xT ^ 3 - g₂ W * e1W W xT - g₃ W = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  unfold e1W g₂ g₃ WeierstrassCurve.c₄ WeierstrassCurve.c₆ WeierstrassCurve.b₂
    WeierstrassCurve.b₄ WeierstrassCurve.b₆
  linear_combination (2 * yT + W.a₁ * xT + W.a₃) * h2 - 4 * hE

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_add_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem norm_sub_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact norm_add_le_one ha (by rwa [norm_neg])

theorem norm_mul_le_one' {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg b) hb

theorem norm_kap [CharZero K] (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1) (hy : ‖yT‖ ≤ 1) :
    ‖kapW W xT‖ ≤ 1 := by
  obtain ⟨h1, h2', -, h4, -⟩ := hW
  rw [kap_eq W xT yT h2]
  have n3 : ‖(3 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 3
  have n2 : ‖(2 : K)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
  have hxx : ‖xT ^ 2‖ ≤ 1 := by
    rw [pow_two]
    exact norm_mul_le_one' hx hx
  exact norm_sub_le_one
    (norm_add_le_one
      (norm_add_le_one (norm_mul_le_one' n3 hxx) (norm_mul_le_one' (norm_mul_le_one' n2 h2') hx))
      h4)
    (norm_mul_le_one' h1 hy)

end Norm

theorem curve_sigma_function_holds : CurveSigma := by
  intro K _ _ W s2
  obtain ⟨h0, h1⟩ := phODef K s2 (wpReg W) (logSer W) (Formalism.L2.Th1.A.ZSer.log_cc W)
    (Formalism.L2.Th1.A.ZSer.log_one W)
  exact ⟨h0, h1, addSgStar K (g₂ W) (g₃ W) s2 (wpReg W) (bridgeWp K W)⟩

theorem curve_formal_first_level_holds : WeierstrassBiadditiveModEquiv := by
  intro K _ _ _ W s2 hW h2
  obtain ⟨hF, hi, -⟩ := bridgeLaw K W hW
  exact f1O K (g₂ W) (g₃ W) s2 (W.b₂ / 12) (wpReg W) (logSer W) (iSer W) (xS W) (fgl W)
    (bridgeWp K W) hF hi (bridgeCurve K W hW) h2

end Formalism.L2.Th1.B.Crv
end
end

