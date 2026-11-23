module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.DivLaw
section
noncomputable section

namespace Formalism.L2.Th1.B.LDiv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_mul' integral_one' integral_of_mul_eq_one)
open Formalism.L2.Th1.B.ParE (integral_add' integral_sub' integral_C')
open Formalism.G.LogP (hs2 subst2_subst subst_XX)

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem div_law {F G : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (hF : LawLog F l)
    (hi : IsInv l i) (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = F * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have ii : Integral (at1 (0 : Fin 2) i) := integral_series_at_variable 0 i hi.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst
      ![at1 (0 : Fin 2) i, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] F := ⟨_, rfl⟩
  have cD : MvPowerSeries.constantCoeff D = 0 := by
    rw [hD]
    exact law_constantCoeff_subst2 F hF.1 _ _ ci c1
  have iD : Integral D := by
    rw [hD]
    exact integral_subst_two_variables hF.2.1 _ _ ci c1 ii i1
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), D] G := ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ c0 cD i0 iD
  have hH0 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0 := by
    have hb := hs2 c0 cz
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, 0] F] G
      = 0
    rw [law_right_zero hF _ ci]
    exact hd
  have hdvd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis0 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 1 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 c0 hF.1
  refine ⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H1,
    integral_subst_two_variables iH1 _ _ c0 hF.1 i0 hF.2.1, ?_⟩
  have e3 : MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F =
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    refine law_eq_of_log hF _ _ _ ci hF.1 c1 ?_
    have e4 := law_subst hF (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) c0 c1
    rw [subst_XX] at e4
    rw [e4, log_subst_formal_inverse hi 0]
    change -at1 0 l + (at1 0 l + _) = _
    rw [neg_add_cancel_left]
  have e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H = G := by
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F] G
      = G
    rw [e3]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

theorem LDiv_of (hG : GCob) : LDiv := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hT1, hT2, nx, ny, na, -⟩ := hT
  have hep := hC.1
  have hep0 := hC.2.1
  have c0' : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1' : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)

  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hX3 : Integral (ι := Unit) (PowerSeries.X ^ 3 : PowerSeries K) := by
    rw [pow_succ]
    exact integral_mul' hX2 hX
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by simp [gT, hep0]
  have hgi : Integral (ι := Unit) (gT ep xT) :=
    integral_sub' hep (integral_mul' (integral_C' nx) hX2)
  have hinv : (gT ep xT)⁻¹ * gT ep xT = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hg0]; exact one_ne_zero)
  have hginv : Integral (ι := Unit) (gT ep xT)⁻¹ := integral_of_mul_eq_one hgi hg0 hinv
  have hth : Integral (ι := Unit) (thT ep xT yT) :=
    integral_mul' (integral_add' hep (integral_mul' (integral_C' ny) hX3)) hginv
  have hth0 : PowerSeries.constantCoeff (thT ep xT yT) = 1 := by
    have e := congrArg PowerSeries.constantCoeff hinv
    rw [map_mul, hg0, mul_one, map_one] at e
    unfold thT
    rw [map_mul, e]
    simp [hep0]
  have hL : Integral (LT ep xT yT a1) :=
    integral_sub' (integral_add' (integral_mul' i1 (integral_series_at_variable 0 _ hth))
      (integral_mul' i0 (integral_series_at_variable 1 _ hth)))
      (integral_mul' (integral_mul' (integral_C' na) i0) i1)

  have hb := hs2 c0' ci
  have eF : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] F = 0 := by
    refine law_eq_of_log hF _ _ 0 c0' ci cz ?_
    rw [law_subst_zero l hF.2.2.1, log_subst_formal_inverse hi 0]
    exact add_neg_cancel _
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] (LT ep xT yT a1) = 0 := by
    have e := congrArg (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i])
      (hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hT1 hT2)
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb,
      MvPowerSeries.subst_pow hb F, eF, psubst_msubst _ hF.1 hb, eF] at e
    have e5 : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (gT ep xT) ≠ 0 := by
      intro h
      rw [PowerSeries.subst_zero_eq_C_constantCoeff, hg0] at h
      simp at h
    rw [MvPowerSeries.subst_pow hb] at e
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at e
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h e5
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  obtain ⟨nu, hnu, e⟩ := div_law hF hi hL hd
  refine ⟨nu, hnu, ?_, e⟩

  have a0 : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 1 * n) =
      MvPowerSeries.constantCoeff n := by
    intro n
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1' : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 0 * n) = 0 := by
    intro n
    have hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 0 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  have h1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (LT ep xT yT a1) = 1 := by
    unfold LT
    have e6 : MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 =
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * (MvPowerSeries.C a1 * MvPowerSeries.X 1) := by
      ring
    rw [e6, map_sub, map_add (f := _), a0, a1', a1', add_zero, sub_zero]
    exact (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (thT ep xT yT)
      (b := fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (fun _ => c0')).trans hth0
  have h2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (F * nu) =
      MvPowerSeries.constantCoeff nu := by
    classical
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    simp [Finset.Nat.antidiagonal_succ, law_coeff_single hF 1, hF.1]
  rw [e, h2] at h1
  exact h1

end Formalism.L2.Th1.B.LDiv
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Iso

open PowerSeries
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv)

variable {K : Type} [Field K] [CharZero K]

theorem dz_rescale (a : K) (f : PowerSeries K) :
    dz (rescale a f) = C a * rescale a (dz f) := by
  ext n
  rw [dz, coeff_derivative, coeff_rescale, coeff_C_mul, coeff_rescale, coeff_derivative]
  ring

theorem second_derivative_rescale (a : K) (f : PowerSeries K) :
    dz (dz (rescale a f)) = C (a ^ 2) * rescale a (dz (dz f)) := by
  rw [dz_rescale, dz_mul, dz_C, dz_rescale, map_pow]
  ring

theorem rescale_C' (a c : K) : rescale a (C c : PowerSeries K) = C c := by
  ext n
  rw [coeff_rescale, coeff_C]
  split_ifs with h
  · rw [h, pow_zero, one_mul]
  · rw [mul_zero]

theorem dz_nsmul (n : ℕ) (f : PowerSeries K) : dz (n • f) = n • dz f := map_nsmul _ n f

theorem second_derivative_nsmul (n : ℕ) (f : PowerSeries K) : dz (dz (n • f)) = n • dz (dz f) := by
  rw [dz_nsmul, dz_nsmul]

theorem fExp_zero : fExp (0 : PowerSeries K) = 1 := by
  have h : fExp (0 : PowerSeries K) * fExp (0 : PowerSeries K) = fExp (0 : PowerSeries K) := by
    rw [← fExp_add (map_zero _) (map_zero _), add_zero]
  have h1 : constantCoeff (fExp (0 : PowerSeries K)) = 1 := constantCoeff_fExp (map_zero _)
  have hne : fExp (0 : PowerSeries K) ≠ 0 := ne_zero_of_constantCoeff (by rw [h1]; exact one_ne_zero)
  exact mul_left_cancel₀ hne (by rw [h, mul_one])

theorem fExp_nsmul {f : PowerSeries K} (hf : constantCoeff f = 0) (n : ℕ) :
    fExp (n • f) = fExp f ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, fExp_zero]
  | succ m ih =>
    have hm : constantCoeff (m • f) = 0 := by rw [map_nsmul, hf, smul_zero]
    rw [succ_nsmul, fExp_add hm hf, ih, pow_succ]

theorem fExp_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries K)
    (hf : ∀ i, constantCoeff (f i) = 0) : fExp (∑ i ∈ s, f i) = ∏ i ∈ s, fExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, fExp_zero]
  | insert a s ha ih =>
    have hs : constantCoeff (∑ i ∈ s, f i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.prod_insert ha, fExp_add (hf a) hs, ih]

theorem second_derivative_formal_log {f g : PowerSeries K} (hf : constantCoeff f = 1) (h : HasSecondLogDeriv f g) :
    dz (dz (fLog f)) = g := by
  have hne : f ≠ 0 := ne_zero_of_constantCoeff (by rw [hf]; exact one_ne_zero)
  have hL1 : f * dz (fLog f) = dz f := Sq.mul_dz_fLog hf
  have hL2 : f * dz (dz (fLog f)) + dz (fLog f) * dz f = dz (dz f) := by
    have := congrArg dz hL1
    rwa [dz_mul] at this
  have h' : dz (dz f) * f - dz f ^ 2 = g * f ^ 2 := h
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  linear_combination f * hL2 - dz f * hL1 + h'

theorem constantCoeff_wpShift (P : PowerSeries K) (c : K) : constantCoeff (wpShift P c) = 1 := by
  simp [wpShift]

theorem dz_X_sq : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
  have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this

theorem linear_coeff_log_shifted_weierstrass (P : PowerSeries K) (c : K) :
    constantCoeff (dz (fLog (wpShift P c))) = 0 := by
  have h := congrArg constantCoeff (Sq.mul_dz_fLog (constantCoeff_wpShift P c))
  rw [map_mul, constantCoeff_wpShift, one_mul] at h
  rw [h, wpShift, dz_add, dz_mul, dz_one, dz_X_sq]
  simp

theorem second_log_derivative_two_isogeny (g2 g3 e1 : K) (P : PowerSeries K) (hP : IsWp g2 g3 P)
    (he : 4 * e1 ^ 3 - g2 * e1 - g3 = 0) :
    HasSecondLogDeriv (wpShift P e1) (2 * P - 2 * (C e1 + C (3 * e1 ^ 2 - g2 / 4) * wOf e1 P)) := by
  obtain ⟨hF1, hF2⟩ := weierstrassReducedEquations K g2 g3 P hP
  have hZW : wpShift P e1 = 1 + X ^ 2 * P - C e1 * X ^ 2 := by rw [wpShift]; ring
  rw [hZW]
  set Ze : PowerSeries K := 1 + X ^ 2 * P - C e1 * X ^ 2 with hZe
  have hZ0 : constantCoeff Ze = 1 := by simp [hZe]
  have hZ0' : constantCoeff Ze ≠ 0 := by rw [hZ0]; exact one_ne_zero
  have hw : wOf e1 P * Ze = X ^ 2 := by
    unfold wOf
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ hZ0', mul_one]
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := dz_X_sq
  have hZ1 : dz Ze = X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X) := by
    rw [hZe]; simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2]; ring
  have hZ2 : dz (dz Ze) = X ^ 2 * dz (dz P) + 4 * X * dz P + 2 * P - 2 * C e1 := by
    rw [hZ1]; simp only [dz_sub, dz_add, dz_mul, dz_two, dz_X, dz_C, e2]; ring
  have c2 : 2 * (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 6 * C e1 ^ 2 - C (g2 / 2) := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; congr 1; ring
  have c3 : 2 * C (g2 / 2) = (C g2 : PowerSeries K) := by
    rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
  have he' : 4 * (C e1 : PowerSeries K) ^ 3 - C g2 * C e1 - C g3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_pow, ← map_sub]; rw [he, map_zero]
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at c2 ⊢
  have hB : Ze * dz (dz Ze) - dz Ze ^ 2 =
      (2 * P - 2 * C e1) * Ze ^ 2 - 2 * C kap * X ^ 2 * Ze := by
    rw [hZ2, hZ1, hZe]
    linear_combination (-1 : PowerSeries K) * hF1 + (1 + X ^ 2 * P - C e1 * X ^ 2) * hF2 -
      X ^ 4 * he' + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c2 -
      X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) * c3
  show dz (dz Ze) * Ze - dz Ze ^ 2 = _
  linear_combination hB + 2 * C kap * Ze * hw

theorem theta_zero_isogeny_holds : Th0Isogeny := by
  intro K _ _ g2 g3 s2 c0 xT al S P ι _ c wp wm hP he hF hS
  obtain ⟨hF1, hF2⟩ := hF
  have hD := second_log_derivative_two_isogeny g2 g3 (xT + c0) P hP he
  unfold thTw thZ sigma1
  generalize xT + c0 = e1 at *
  generalize 3 * e1 ^ 2 - g2 / 4 = kap at *
  generalize wOf e1 P = w at *
  set n : ℕ := Fintype.card ι with hn
  have hS1 : constantCoeff (sigmaOneSeries e1 kap w) = 0 := Sq.constantCoeff_sig1S _ _ _
  have hq : constantCoeff (-(C (s2 / 2) * X ^ 2) : PowerSeries K) = 0 := by simp
  rw [← fExp_add hS1 hq]
  set abelian₂ : PowerSeries K := sigmaOneSeries e1 kap w + -(C (s2 / 2) * X ^ 2) with hLam
  have hL0 : constantCoeff abelian₂ = 0 := by rw [hLam, map_add (f := _), hS1, hq, add_zero]
  have hL1 : dz abelian₂ = -prim (C e1 + C kap * w) - C s2 * X := by
    have c3 : 2 * C (s2 / 2) = (C s2 : PowerSeries K) := by
      rw [← map_ofNat (C (R := K)) 2, ← map_mul]; congr 1; ring
    rw [hLam, sigmaOneSeries]
    simp only [dz_add, dz_neg, dz_prim, dz_mul, dz_C, dz_X_sq]
    linear_combination (-X : PowerSeries K) * c3
  have hL2 : dz (dz abelian₂) = -(C e1 + C kap * w) - C s2 := by
    rw [hL1]
    simp only [dz_sub, dz_neg, dz_prim, dz_mul, dz_C, dz_X]
    ring
  have hL1c : constantCoeff (dz abelian₂) = 0 := by
    rw [hL1]; simp [constantCoeff_prim]
  have hR0 : constantCoeff (rescale al abelian₂) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, hL0,
      mul_zero]
  have hZ1 : ∀ a : K, constantCoeff (wpShift P a) = 1 := constantCoeff_wpShift P
  have hZl : ∀ a : K, constantCoeff (fLog (wpShift P a)) = 0 := fun a => constantCoeff_fLog (hZ1 a)
  clear_value abelian₂
  have key : rescale al abelian₂ + n • fLog (wpShift P e1) =
      (2 * n) • abelian₂ + ∑ Q, fLog (wpShift P (c Q)) := by
    refine derivative.ext (derivative.ext ?_ ?_) ?_
    · show dz (dz _) = dz (dz _)
      have hsum : dz (dz (∑ Q, fLog (wpShift P (c Q)))) = ∑ Q, (2 * P - wp Q - wm Q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dz, dz, map_sum, map_sum]
        exact Finset.sum_congr rfl fun Q _ => second_derivative_formal_log (hZ1 _) (hF1 Q)
      have hsum2 : ∑ Q, (2 * P - wp Q - wm Q) =
          (n : PowerSeries K) * (2 * P) - ∑ Q, (wp Q + wm Q) := by
        have : ∀ Q, 2 * P - wp Q - wm Q = 2 * P - (wp Q + wm Q) := fun Q => by ring
        rw [Finset.sum_congr rfl fun Q _ => this Q, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
      have hSC : C (al ^ 2) * C s2 - 2 * (n : PowerSeries K) * C s2 = C S := by
        rw [← hS, ← map_natCast (C (R := K)) n, ← map_ofNat (C (R := K)) 2]
        simp only [← map_mul, ← map_sub]
        congr 1; ring
      rw [dz_add, dz_add, dz_add, dz_add, hsum, hsum2, second_derivative_rescale, hL2, second_derivative_nsmul, second_derivative_nsmul, hL2,
        second_derivative_formal_log (hZ1 _) hD, map_sub, map_neg, rescale_C', nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      linear_combination (-1 : PowerSeries K) * hF2 - hSC
    · show constantCoeff (dz _) = constantCoeff (dz _)
      have hsum : constantCoeff (dz (∑ Q, fLog (wpShift P (c Q)))) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dz, map_sum, map_sum]
        exact Finset.sum_eq_zero fun Q _ => linear_coeff_log_shifted_weierstrass P _
      have hr : constantCoeff (rescale al (dz abelian₂)) = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply,
          hL1c, mul_zero]
      rw [dz_add, dz_add, map_add (f := _), map_add (f := _), hsum, dz_rescale, map_mul, hr, dz_nsmul, dz_nsmul,
        map_nsmul, map_nsmul, linear_coeff_log_shifted_weierstrass, hL1c]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_add (f := _), map_add (f := _), hR0, map_nsmul, map_nsmul, hZl, hL0, map_sum,
        Finset.sum_eq_zero fun Q _ => hZl _]
        simp
  rw [Sq.rescale_fExp al hL0]
  have e1' : wpShift P e1 ^ n = fExp (n • fLog (wpShift P e1)) := by
    rw [fExp_nsmul (hZl _), fExp_fLog (hZ1 _)]
  have e2' : ∏ Q, wpShift P (c Q) = fExp (∑ Q, fLog (wpShift P (c Q))) := by
    rw [fExp_sum _ _ (fun Q => hZl _)]
    exact Finset.prod_congr rfl fun Q _ => (fExp_fLog (hZ1 _)).symm
  have hn0 : constantCoeff (n • fLog (wpShift P e1)) = 0 := by rw [map_nsmul, hZl, smul_zero]
  have hn1 : constantCoeff ((2 * n) • abelian₂) = 0 := by rw [map_nsmul, hL0, smul_zero]
  have hn2 : constantCoeff (∑ Q, fLog (wpShift P (c Q))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_eq_zero fun Q _ => hZl _
  rw [e1', e2', ← fExp_nsmul hL0, ← fExp_add hR0 hn0, ← fExp_add hn1 hn2, key]

end Formalism.L2.Th1.B.Iso
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Nrm

open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift IsLogPair mulBy PhNormAt Cong LG IntMv IntPS mvExp IsOneUnit XIsWp)
open Formalism.L2.Th1.C.USideB

theorem PhENorm_of (hI : Th0Isogeny) : PhENorm := by
  intro K _ _ _ g2 g3 s2 c0 xT al albar S P l linv i ep F ι _ xQ wp wm hP hT hL hC hxT hxQ hZ hN hS
  have hl := hL.1
  have hsl := hs_of hl
  have hcv : PowerSeries.constantCoeff (mulBy l linv al) = 0 := cc_mulBy hL al
  have hsv := hs_of hcv
  have hS' : (al ^ 2 - 2 * (Fintype.card ι : K)) * s2 = S := by rw [← hN, ← hS]; ring
  have hF := hI K g2 g3 s2 c0 xT al S P ι (fun Q => xQ Q + c0) wp wm hP hT hZ hS'
  obtain ⟨hph0, hphd⟩ :=
    phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl
  generalize hn : Fintype.card ι = n at *
  have hthl : PowerSeries.subst l (thTw g2 s2 c0 xT P) = mvExp (-(phTw g2 s2 c0 xT P l)) := hphd
  have hph0' : PowerSeries.constantCoeff (phTw g2 s2 c0 xT P l) = 0 := hph0
  generalize phTw g2 s2 c0 xT P l = ph at *
  generalize thTw g2 s2 c0 xT P = th at *
  set v := mulBy l linv al with hv
  have hnph : PowerSeries.constantCoeff (-ph) = 0 := by simp [hph0']
  have hphv : PowerSeries.constantCoeff (PowerSeries.subst v ph) = 0 := cc_subst hcv hph0'
  have hnphv : PowerSeries.constantCoeff (-(PowerSeries.subst v ph)) = 0 := by simp [hphv]
  have hX : XIsWp P l ep c0 := by
    unfold XIsWp
    rw [Formalism.L2.Th1.C.USideA.subst_wpShift_zero hsl, hC.2.2.1]
    ring

  have h1 : PowerSeries.subst l (PowerSeries.rescale al th) =
      mvExp (-(PowerSeries.subst v ph)) := by
    rw [subst_rescale hL, hthl, Formalism.L2.Th1.C.subst_mvExp hnph hcv]
    have h3 : PowerSeries.subst v (-ph) = -(PowerSeries.subst v ph) := by
      rw [← PowerSeries.coe_substAlgHom hsv, map_neg]
    rw [h3]

  have h4 := congrArg (PowerSeries.subst l) hF
  rw [PowerSeries.subst_mul hsl, PowerSeries.subst_pow hsl, PowerSeries.subst_mul hsl,
    PowerSeries.subst_pow hsl, h1, hthl] at h4
  have h6 : PowerSeries.subst l (∏ Q, wpShift P (xQ Q + c0)) =
      ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) := by
    rw [← PowerSeries.coe_substAlgHom hsl, map_prod]
  rw [h6] at h4
  have h7 : PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0)) =
      (∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2)) * l ^ (2 * n) := by
    rw [pow_mul, pow_mul, ← hn, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun Q _ => subst_wpShift hl hX (xQ Q)
  have h8 := subst_wpShift hl hX xT
  set B : PowerSeries K := ∏ Q, (ep - PowerSeries.C (xQ Q) * PowerSeries.X ^ 2) with hB
  set G : PowerSeries K := ep - PowerSeries.C xT * PowerSeries.X ^ 2 with hG
  have hl0 : l ^ (2 * n) ≠ 0 := pow_ne_zero _ (l_ne_zero hL)
  have h9 : (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n =
      mvExp (-ph) ^ (2 * n) * B := by
    apply mul_right_cancel₀ hl0
    calc (mvExp (-(PowerSeries.subst v ph)) : PowerSeries K) * G ^ n * l ^ (2 * n)
        = mvExp (-(PowerSeries.subst v ph)) * (G * l ^ 2) ^ n := by
          rw [mul_pow, ← pow_mul, mul_assoc]
      _ = (mvExp (-(PowerSeries.subst v ph)) *
            PowerSeries.subst l (wpShift P (xT + c0)) ^ n) * PowerSeries.X ^ (2 * n) := by
          rw [← h8]; ring
      _ = mvExp (-ph) ^ (2 * n) *
            (PowerSeries.X ^ (2 * n) * ∏ Q, PowerSeries.subst l (wpShift P (xQ Q + c0))) := by
          rw [h4]; ring
      _ = _ := by rw [h7]; ring

  have hepi : ep ∈ intSub (unitBall K) := fun k => hC.1 (Finsupp.single () k)
  have hBi : B ∈ intSub (unitBall K) :=
    Subring.prod_mem _ fun Q _ => Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub (hxQ Q)) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hGi : G ∈ intSub (unitBall K) :=
    Subring.sub_mem _ hepi
      (Subring.mul_mem _ (C_mem_intSub hxT) (Subring.pow_mem _ (X_mem_intSub _) 2))
  have hB1 : PowerSeries.constantCoeff B = 1 := by
    rw [hB, map_prod]
    apply Finset.prod_eq_one
    intro Q _
    simp [hC.2.1]
  have hNph : (al * albar) • ph = ((2 * n : ℕ) : K) • ph := by rw [hN]; push_cast; rfl
  have hNph0 : PowerSeries.constantCoeff (((2 * n : ℕ) : K) • ph) = 0 := by simp [hph0']
  have h10 : (mvExp (PowerSeries.subst v ph - (al * albar) • ph) : PowerSeries K) * B = G ^ n := by
    rw [hNph, Formalism.L2.Th1.C.mvExp_sub hphv hNph0, ← smul_neg,
      Formalism.L2.Th1.C.mvExp_smul_nat hnph, mul_assoc, ← h9, ← mul_assoc,
      Formalism.L2.Th1.C.mvExp_mul_neg hphv, one_mul]
  have h11 : IntPS (unitBall K) (mvExp (PowerSeries.subst v ph - (al * albar) • ph)) :=
    int_of_mul ⟨hB1, hBi⟩ (Subring.pow_mem _ hGi n) h10
  refine ⟨?_, intMv_of_intPS h11⟩
  have : PowerSeries.constantCoeff (PowerSeries.subst v ph - (al * albar) • ph) = 0 := by
    simp [hphv, hph0']
  exact this

end Formalism.L2.Th1.B.Nrm
end
end

