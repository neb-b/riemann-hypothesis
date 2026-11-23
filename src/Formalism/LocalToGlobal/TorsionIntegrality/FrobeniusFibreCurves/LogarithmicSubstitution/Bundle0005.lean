module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementI

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.AtVariableWeierstrassDerivative
section
noncomputable section

namespace Formalism.L2.Th1.B.GCob

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)

section One

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

theorem wOf_mul (e1 : K) (P : PowerSeries K) :
    wOf e1 P * (1 + X ^ 2 * P - C e1 * X ^ 2) = X ^ 2 := by
  unfold wOf
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]

theorem dz_wOf (e1 : K) (P : PowerSeries K) :
    (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -(X * (-2 + X ^ 3 * dz P)) := by
  have h1 := wOf_mul e1 P
  have e2 : dz ((X : PowerSeries K) ^ 2) = 2 * X := by
    have := dz_X_pow (K := K) 1; push_cast at this; linear_combination this
  have hd := congrArg dz h1
  simp only [dz_sub, dz_add, dz_mul, dz_one, dz_C, e2] at hd
  linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd -
    (X ^ 2 * dz P + P * (2 * X) - C e1 * (2 * X)) * h1

theorem subst_wOf_mul (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    subst l (wOf e1 P) * (1 + l ^ 2 * subst l P - C e1 * l ^ 2) = l ^ 2 := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (wOf_mul e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add (f := _), map_one, map_pow] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

theorem subst_dz_wOf (e1 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) :
    (1 + l ^ 2 * subst l P - C e1 * l ^ 2) ^ 2 * subst l (dz (wOf e1 P)) =
      -(l * (-2 + l ^ 3 * subst l (dz P))) := by
  have hs : HasSubst l := HasSubst.of_constantCoeff_zero' hl
  have := congrArg (subst l) (dz_wOf e1 P)
  rw [← coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_add (f := _), map_one, map_pow, map_neg, map_ofNat] at this
  rw [coe_substAlgHom hs, subst_X hs, subst_C] at this
  exact this

theorem wl_mul_g {c0 xT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0) (hl0 : l ≠ 0)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2)) :
    subst l (wOf (xT + c0) P) * gT ep xT = X ^ 2 := by
  apply mul_right_cancel₀ (pow_ne_zero 2 hl0)
  unfold gT
  have hw' := subst_wOf_mul (xT + c0) P hl
  rw [map_add (f := _)] at hw'
  linear_combination X ^ 2 * hw' - subst l (wOf (xT + c0) P) * hcv

theorem constantCoeff_gT {ep : PowerSeries K} (xT : K) (hep : constantCoeff ep = 1) :
    constantCoeff (gT ep xT) = 1 := by
  simp [gT, hep]

theorem thT_mul {ep : PowerSeries K} (xT yT : K) (hep : constantCoeff ep = 1) :
    thT ep xT yT * gT ep xT = ep + C yT * X ^ 3 := by
  unfold thT
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_gT xT hep]; exact one_ne_zero),
    mul_one]

theorem wprime_core {c0 a1 a3 xT yT : K} {P l ep : PowerSeries K} (hl : constantCoeff l = 0)
    (hl0 : l ≠ 0) (hep : constantCoeff ep = 1)
    (hcv : X ^ 2 * (1 + l ^ 2 * subst l P) = l ^ 2 * (ep + C c0 * X ^ 2))
    (h3 : X ^ 3 * (-2 + l ^ 3 * subst l (dz P)) =
      l ^ 3 * (-2 * ep + C a1 * X * ep + C a3 * X ^ 3))
    (hT : 2 * yT + a1 * xT + a3 = 0) :
    X * subst l (dz (wOf (xT + c0) P)) =
      subst l (wOf (xT + c0) P) * (2 * thT ep xT yT - C a1 * X) := by
  have hWg := wl_mul_g (xT := xT) hl hl0 hcv
  have hth := thT_mul xT yT hep
  have hZ := subst_dz_wOf (xT + c0) P hl
  have hg0 : gT ep xT ≠ 0 :=
    ne_zero_of_constantCoeff (by rw [constantCoeff_gT xT hep]; exact one_ne_zero)
  have hT' : 2 * (C yT : PowerSeries K) + C a1 * C xT + C a3 = 0 := by
    simp only [← map_ofNat (C (R := K)), ← map_mul, ← map_add (f := _)]; rw [hT, map_zero]
  rw [map_add (f := _)] at hZ
  generalize subst l (dz (wOf (xT + c0) P)) = W' at hZ ⊢
  generalize subst l (wOf (xT + c0) P) = W at hWg ⊢
  generalize subst l (dz P) = B at hZ h3
  generalize subst l P = A at hZ hcv
  generalize thT ep xT yT = th at hth ⊢
  have hXZ : X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2) = l ^ 2 * gT ep xT := by
    unfold gT; linear_combination hcv
  have hXZ2 : (X ^ 2 * (1 + l ^ 2 * A - (C xT + C c0) * l ^ 2)) ^ 2 = (l ^ 2 * gT ep xT) ^ 2 := by
    rw [hXZ]
  have step1 : W' * gT ep xT ^ 2 = X * (2 * ep - C a1 * X * ep - C a3 * X ^ 3) := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 4 hl0) (pow_ne_zero 3 (PowerSeries.X_ne_zero (R := K))))
    linear_combination -X ^ 3 * W' * hXZ2 + X ^ 7 * hZ - X ^ 4 * l * h3
  apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
  simp only [gT] at hWg hth step1 ⊢
  linear_combination X * step1 -
    (2 * th * (ep - C xT * X ^ 2) - C a1 * X * (ep - C xT * X ^ 2)) * hWg - 2 * X ^ 2 * hth -
    X ^ 5 * hT'

end One

theorem ne_zero_of_law {K : Type} [NormedField K] {F : MvPowerSeries (Fin 2) K}
    {l : PowerSeries K} (hL : LawLog F l) : l ≠ 0 := by
  intro h
  have := hL.2.2.2.1
  rw [h] at this
  simp at this

theorem weierstrass_derivative_unit_holds : WPrimeU := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F _ hL hC hC3 hT
  exact wprime_core hL.2.2.1 (ne_zero_of_law hL) hC.2.1 hC.2.2.1 hC3.1 hT

section Two

variable {K : Type} [Field K] [CharZero K]

theorem subst_wg {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {W g : PowerSeries K} (h : W * g = PowerSeries.X ^ 2) :
    PowerSeries.subst U W * PowerSeries.subst U g = U ^ 2 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have := congrArg (PowerSeries.subst U) h
  rwa [PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs] at this

theorem at_variable_weierstrass_derivative {ι : Type} (x : ι) {W W' th : PowerSeries K} {a1 : K}
    (h : PowerSeries.X * W' = W * (2 * th - PowerSeries.C a1 * PowerSeries.X)) :
    MvPowerSeries.X x * at1 x W' =
      at1 x W * (2 * at1 x th - MvPowerSeries.C a1 * MvPowerSeries.X x) := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have := congrArg (PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K)) h
  rw [← PowerSeries.coe_substAlgHom hs] at this
  simp only [map_sub, map_mul, map_ofNat] at this
  rw [PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs, PowerSeries.subst_C] at this
  exact this

theorem hsL {l : PowerSeries K} (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.HasSubst (![at1 (0 : Fin 2) l, at1 1 l] : Fin 2 → MvPowerSeries (Fin 2) K) := by
  have h0 : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) l hl
  exact Formalism.G.LogP.hs2 h0 h1

theorem X_ne {ι : Type} (j : ι) : (MvPowerSeries.X j : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg (MvPowerSeries.pderiv (R := K) j) h
  rw [MvPowerSeries.pderiv_X_self, map_zero] at h2
  exact one_ne_zero h2

theorem four_ne {ι : Type} : (4 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have := congrArg MvPowerSeries.constantCoeff h
  rw [map_ofNat, map_zero] at this
  exact absurd this (by norm_num)

theorem subst_log_at_variable (f : PowerSeries K) (x : Fin 2) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (at1 x f) =
      at1 x (PowerSeries.subst l f) := by
  rw [subst_at_variable_eq_subst f x (hsL hl), ParE.subst_inVar x f hl]
  fin_cases x <;> rfl

theorem sub_atS (f : PowerSeries K) {l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l) :
    MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l] (atS f) =
      PowerSeries.subst F (PowerSeries.subst l f) := by
  rw [ParO.subst_atS f (hsL hl), PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' hl) (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    hFl]
  rfl

theorem wadd_law {kap : K} {w l : PowerSeries K} {F : MvPowerSeries (Fin 2) K}
    (hl : PowerSeries.constantCoeff l = 0) (hF : MvPowerSeries.constantCoeff F = 0)
    (hFl : PowerSeries.subst F l = at1 0 l + at1 1 l)
    (h : 4 * at1 0 w * at1 1 w * (1 - MvPowerSeries.C kap * at1 0 w * at1 1 w) ^ 2 * atS w =
      (at1 0 w * at1 1 (dz w) + at1 1 w * at1 0 (dz w)) ^ 2) :
    4 * at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l w) *
        (1 - MvPowerSeries.C kap * at1 0 (PowerSeries.subst l w) *
          at1 1 (PowerSeries.subst l w)) ^ 2 * PowerSeries.subst F (PowerSeries.subst l w) =
      (at1 0 (PowerSeries.subst l w) * at1 1 (PowerSeries.subst l (dz w)) +
        at1 1 (PowerSeries.subst l w) * at1 0 (PowerSeries.subst l (dz w))) ^ 2 := by
  have hb := hsL hl
  have e := congrArg (MvPowerSeries.subst ![at1 (0 : Fin 2) l, at1 1 l]) h
  rw [← MvPowerSeries.coe_substAlgHom hb] at e
  simp only [map_sub, map_mul, map_one, map_pow, map_add (f := _), map_ofNat] at e
  rw [MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_C] at e
  simp only [subst_log_at_variable _ _ hl, sub_atS _ hl hF hFl] at e
  exact e

theorem alg_core {R : Type} [CommRing R] [NoZeroDivisors R] (h4' : (4 : R) ≠ 0)
    {a b c Wa Wb Va Vb ta tb ga gb WF gF Fv d : R}
    (E1 : 4 * Wa * Wb * d ^ 2 * WF = (Wa * Vb + Wb * Va) ^ 2)
    (Ha : a * Va = Wa * (2 * ta - c * a)) (Hb : b * Vb = Wb * (2 * tb - c * b))
    (Ga : Wa * ga = a ^ 2) (Gb : Wb * gb = b ^ 2) (GF : WF * gF = Fv ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    gF * (b * ta + a * tb - c * a * b) ^ 2 = ga * gb * Fv ^ 2 * d ^ 2 := by
  have hWa : Wa ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Ga
    exact pow_ne_zero 2 ha Ga.symm
  have hWb : Wb ≠ 0 := by
    rintro rfl
    rw [zero_mul] at Gb
    exact pow_ne_zero 2 hb Gb.symm
  have H : a * b * (Wa * Vb + Wb * Va) = 2 * Wa * Wb * (b * ta + a * tb - c * a * b) := by
    linear_combination Wa * a * Hb + Wb * b * Ha
  have H2 : (a * b * (Wa * Vb + Wb * Va)) ^ 2 =
      (2 * Wa * Wb * (b * ta + a * tb - c * a * b)) ^ 2 := by rw [H]
  have h4 : (4 : R) * Wa ^ 2 * Wb ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero h4' (pow_ne_zero 2 hWa)) (pow_ne_zero 2 hWb)
  apply mul_left_cancel₀ h4
  linear_combination -gF * H2 - gF * a ^ 2 * b ^ 2 * E1 + 4 * a ^ 2 * b ^ 2 * Wa * Wb * d ^ 2 * GF -
    4 * Wa * Wb * Fv ^ 2 * d ^ 2 * (Wb * gb * Ga + a ^ 2 * Gb)

end Two

theorem GCob_of (hW : WAdd) (hP : WPrimeU) : GCob := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT he
  have hl := hL.2.2.1
  have hIW := wOfWp K g2 g3 (xT + c0) P hWp he
  have E1 := wadd_law hl hL.1 (ParO.log_law hL) (hW K _ _ _ hIW)
  have hp := hP K g2 g3 c0 a1 a3 xT yT P l i ep F hWp hL hC hC3 hT
  have hg := wl_mul_g (xT := xT) hl (ne_zero_of_law hL) hC.2.2.1
  unfold LT
  exact alg_core four_ne E1 (at_variable_weierstrass_derivative 0 hp) (at_variable_weierstrass_derivative 1 hp)
    (subst_wg (MvPowerSeries.constantCoeff_X (0 : Fin 2)) hg)
    (subst_wg (MvPowerSeries.constantCoeff_X (1 : Fin 2)) hg) (subst_wg hL.1 hg)
    (X_ne 0) (X_ne 1)

end Formalism.L2.Th1.B.GCob
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CocycleDiffExpEquiv
section
noncomputable section

namespace Formalism.L2.Th1.B.BeE

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem cob_sub {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f - g) = cob F f - cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_sub h0, PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_add h0, PowerSeries.subst_add (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_add (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_zero {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    cob F (0 : PowerSeries K) = 0 := by
  simpa using cob_sub hF (0 : PowerSeries K) 0

theorem cob_neg {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) : cob F (-f) = -cob F f := by
  have h := cob_sub hF (0 : PowerSeries K) f
  rwa [zero_sub, cob_zero hF, zero_sub] at h

theorem psubst_fLog {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.subst U (fLog g) = fLog (PowerSeries.subst U g) := by
  have hg1 : PowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  unfold fLog
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg1) hU',
    PowerSeries.subst_sub hU']
  congr 2
  rw [← map_one (PowerSeries.C (R := K)), PowerSeries.subst_C, map_one]

theorem cc_psubst {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} {c : K} (hg : PowerSeries.constantCoeff g = c) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = c := by
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hgc : PowerSeries.constantCoeff (g - PowerSeries.C c) = 0 := by simp [hg]
  have e : g = PowerSeries.C c + (g - PowerSeries.C c) := by ring
  rw [e, PowerSeries.subst_add hU', PowerSeries.subst_C, map_add (f := _),
    PowerSeries.constantCoeff_subst_eq_zero hU _ hgc]
  simp

theorem cob_fLog {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    cob F (fLog g) = fLog (PowerSeries.subst F g) - fLog (at1 0 g) - fLog (at1 1 g) := by
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  simp only [cob, at1]
  rw [psubst_fLog hF hg, psubst_fLog (hX 0) hg, psubst_fLog (hX 1) hg]

theorem two_ne {ι : Type} : (2 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg MvPowerSeries.constantCoeff h
  have e2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries ι K) = 2 := map_ofNat _ 2
  rw [e2, map_zero] at h2
  exact two_ne_zero h2

end Alg

theorem BeESim_of (hG : GCob) (hL : LDiv) : BeESim := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨nu, hnuI, hnu0, hLT⟩ := hL K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hy, hcub, hx, -, -, hk⟩ := hT
  have hGC := hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hy hcub
  have hF0 := hF.1
  have hce : c0 - (xT + c0) = -xT := by ring
  have hn : ‖c0 - (xT + c0)‖ ≤ 1 := by rw [hce, norm_neg]; exact hx
  have hg : ep + PowerSeries.C (c0 - (xT + c0)) * PowerSeries.X ^ 2 = gT ep xT := by
    rw [hce, map_neg, gT]; ring
  have hD := (diffPh K g2 g3 s2 c0 (xT + c0) P l i ep F hP hcub hF hC).1
  obtain ⟨hw, hwI⟩ := wIntegral K c0 (xT + c0) P l i ep F hF hC hn
  rw [hg] at hD hw
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by
    rw [gT, map_sub, hC.2.1]; simp
  have hw0 : PowerSeries.constantCoeff (PowerSeries.subst l (wOf (xT + c0) P)) = 0 := by
    have := congrArg PowerSeries.constantCoeff hw
    rw [map_mul, hg0, mul_one] at this
    rw [this]; simp
  generalize PowerSeries.subst l (wOf (xT + c0) P) = wl at hGC hwI hw0
  generalize phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l = ph' at hD ⊢
  generalize 3 * (xT + c0) ^ 2 - g2 / 4 = kap at hGC hk
  generalize phO s2 P l = ph at hD ⊢
  generalize gT ep xT = g at hGC hD hg0
  obtain ⟨d, hd⟩ : ∃ d : MvPowerSeries (Fin 2) K,
      d = 1 - MvPowerSeries.C kap * at1 0 wl * at1 1 wl := ⟨_, rfl⟩
  rw [← hd, hLT] at hGC
  have hdI : Integral d := by
    rw [hd]
    exact ParE.integral_sub' Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_one'
      (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (ParE.integral_C' hk)
        (integral_series_at_variable 0 wl hwI)) (integral_series_at_variable 1 wl hwI))
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, map_mul, constantCoeff_series_at_variable 0 wl hw0]; simp
  have hFne : F ≠ 0 := by
    intro h
    have := law_coeff_single hF 0
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hmain : PowerSeries.subst F g * (nu * nu) = at1 0 g * at1 1 g * (d * d) := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hFne) ?_
    linear_combination hGC
  have cF := cc_psubst hF0 hg0
  have cA : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have cB : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have hlog := congrArg fLog hmain
  rw [ParO.fLog_mul cF (by rw [map_mul, hnu0, mul_one]), ParO.fLog_mul hnu0 hnu0,
    ParO.fLog_mul (by rw [map_mul, cA, cB, mul_one]) (by rw [map_mul, hd0, mul_one]),
    ParO.fLog_mul cA cB, ParO.fLog_mul hd0 hd0] at hlog
  have h2 : cob F (2 * (ph' - ph)) = 2 * (cob F ph' - cob F ph) := by
    rw [two_mul, cob_add hF0, cob_sub hF0]; ring
  have h3 := congrArg (cob F) hD
  rw [h2, cob_neg hF0, cob_fLog hF0 hg0] at h3
  have e : cob F ph' - cob F ph = fLog nu - fLog d := by
    refine mul_left_cancel₀ (two_ne (K := K)) ?_
    linear_combination h3 - hlog
  have s := (simeqInt K (Fin 2) _ _ _ _ (simeqLog K (Fin 2) nu hnu0 hnuI).1
    (simeqLog K (Fin 2) d hd0 hdI).1).1
  unfold Simeq at s ⊢
  rw [e]
  simpa using s

theorem cocycle_diff_exp_equiv : CocycleDiffExpEquiv := by
  intro K _ _ _ F H H' hF0 hFi hHH'
  obtain ⟨-, -, -, -, hsub⟩ := equivalence_rules K (Fin 2)
  obtain ⟨hrefl, hsymm, -, hadd, -⟩ := equivalence_rules K (Fin 3)
  have hneg : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a b → Simeq (-a) (-b) := by
    intro a b h
    have h' := hadd b a (-a - b) (-a - b) (hsymm a b h) (hrefl _)
    have e1 : b + (-a - b) = -a := by ring
    have e2 : a + (-a - b) = -b := by ring
    rwa [e1, e2] at h'
  have hsub' : ∀ a b c d : MvPowerSeries (Fin 3) K, Simeq a b → Simeq c d → Simeq (a - c) (b - d) := by
    intro a b c d h1 h2
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact hadd _ _ _ _ h1 (hneg _ _ h2)
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have iX : ∀ j : Fin 3, Integral (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) :=
    fun j => integral_mvPowerSeries_X j
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := Formalism.L2.Th1.B.E2.constantCoeff_law_first_two_of_three hF0
  have i3 : Integral (in3 F) := integral_subst_two_variables hFi _ _ (hX 0) (hX 1) (iX 0) (iX 1)
  unfold d1
  refine hsub' _ _ _ _ (hsub' _ _ _ _ ?_ ?_) ?_
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [c3, i3, hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]

theorem CubeE_of (hB : BeESim) (hD : CocycleDiffExpEquiv) : CubeE := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  intro ph'
  have hl0 : PowerSeries.constantCoeff l = 0 := hLaw.2.2.1
  have hcc : PowerSeries.constantCoeff ph' = 0 :=
    (phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l ph' hLaw hcc
  have hO := (first_level_all_formal_groups K g2 g3 s2 c0 a1 a3 P l i ep F hW hLaw hI hC hC3).2.2.1
  have hBE := hB K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  have hDD := hD K F _ _ hLaw.1 hLaw.2.1 hBE
  obtain ⟨-, -, htrans, -, -⟩ := equivalence_rules K (Fin 3)
  have h3 : Simeq (d1 F (cob F ph')) 0 := htrans _ _ _ hDD hO
  exact ⟨hdiv, hsw, h3, by rw [hsw]; exact h3⟩

end Formalism.L2.Th1.B.BeE
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.Crv2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G (unitBall)
open Formalism.L2.Th1.C (wpShift HasSecondLogDeriv wTr IsLogPair mulBy EndInt PhNormAt IsBinomScalar)
open Formalism.L2.Th1.A (fgl iSer logSer expSer wpReg g₂ g₃ IntModel xS tS xPlus bridgeWp bridgeLaw
  bridgeCurve bridgeCurve3)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem logPair (W : WeierstrassCurve K) : IsLogPair (logSer W) (expSer W) :=
  (Formalism.L2.Th1.C.curveFrame K ⊤ W ⟨trivial, trivial, trivial, trivial, trivial⟩).1

end Alg

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem twoHyp (W : WeierstrassCurve K) (xT yT : K) (hW : IntModel W)
    (hE : W.toAffine.Equation xT yT) (h2 : 2 * yT + W.a₁ * xT + W.a₃ = 0) (hx : ‖xT‖ ≤ 1)
    (hy : ‖yT‖ ≤ 1) : TwoHyp (g₂ W) (g₃ W) (W.b₂ / 12) W.a₁ W.a₃ xT yT :=
  ⟨h2, Crv.two_torsion_x_root_of_cubic W xT yT hE h2, hx, hy, hW.1, Crv.norm_kap W xT yT hW h2 hx hy⟩

end Norm

end Formalism.L2.Th1.B.Crv2
end
end

