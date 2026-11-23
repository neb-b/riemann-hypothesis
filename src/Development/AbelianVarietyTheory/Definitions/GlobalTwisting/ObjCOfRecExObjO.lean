module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0137

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB.Bridge

theorem exists_T_of_over {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) (u : D.what₂.Word) :
    ∃ u', (D.mem u).A.T = Lv.T u' := by
  obtain ⟨sp, hT, hY, hA, hV, hz, X, h1, rfl⟩ := h
  have key : ∀ B : Pre, B = Pre.ofCh P Lv sp hT hY hA hV hz → ∀ v : B.Word, ∃ u', B.T v = Lv.T u' := by
    rintro B rfl v
    exact ⟨v, rfl⟩
  obtain ⟨u', hu⟩ := key X.B.toPre h1 u
  exact ⟨u', (X.C.A_T u).trans hu⟩

theorem scale_X'_le_of_log (eps cs : ℝ) (he : 0 < eps) (hc : 0 < cs) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (T : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 0 < T → cs * R.m * s.L ≤ Real.log T → s.X' ≤ T := by
  refine ⟨cs⁻¹ ^ ((2 * eps / 3)⁻¹), fun s R T hs hx hR hT h => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hm : (1 : ℝ) ≤ R.m := by
    refine le_trans ?_ hR.2.1.1
    rw [Real.one_le_sqrt, Scale.delta1, ← Real.rpow_one_add' hx0.le (by linarith)]
    exact Real.one_le_rpow hx1.le (by linarith)
  have h1 : cs⁻¹ ≤ s.x ^ (2 * eps / 3) := by
    have := Real.rpow_le_rpow (by positivity) hx (show 0 ≤ 2 * eps / 3 by positivity)
    rwa [Real.rpow_inv_rpow (by positivity) (by positivity)] at this
  have h2 : s.L = s.x ^ (2 * eps / 3) * s.x ^ (s.eps / 3) := by
    rw [Scale.L, ← Real.rpow_add hx0, hs]; congr 1; ring
  have h3 : 1 ≤ cs * s.x ^ (2 * eps / 3) := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  have h4 : 0 < s.x ^ (s.eps / 3) := by positivity
  have h5 : s.x ^ (s.eps / 3) ≤ cs * R.m * s.L := by
    have : cs * R.m * s.L = (cs * s.x ^ (2 * eps / 3) * R.m) * s.x ^ (s.eps / 3) := by rw [h2]; ring
    rw [this]
    exact le_mul_of_one_le_left h4.le (one_le_mul_of_one_le_of_one_le h3 hm)
  rw [Scale.X', ← Real.le_log_iff_exp_le hT]
  exact h5.trans h

theorem scale_one_le_w'' (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 1 ≤ s.w'' R.n := by
  obtain ⟨x0, h⟩ := GlobalTheory.scale_poly_comparison eps 0 1 he one_pos
  refine ⟨max x0 4, fun s R hs hx hR => ?_⟩
  have hx4 : 4 ≤ s.x := (le_max_right _ _).trans hx
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have h2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have h3 : (R.n : ℝ) ≤ s.x ^ (3 : ℝ) := by
    have a1 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have a2 : s.x ^ (3 : ℝ) = s.x ^ ((1 : ℝ) / 2) * s.x ^ ((5 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [a2]
    exact hR.1.2.trans (mul_le_mul h2 a1 (by positivity) (by positivity))
  have := ((h s hs ((le_max_left _ _).trans hx)).2.2.2.2.2.1 R.n hn h3).1
  simpa using this

end GlobalTheory.EX.OB.Bridge
