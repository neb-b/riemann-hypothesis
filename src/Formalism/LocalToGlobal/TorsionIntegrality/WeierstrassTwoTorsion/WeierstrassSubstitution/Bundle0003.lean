module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementZ
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveSer

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ConstCurveDL
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace Wp

variable {K : Type u} [Field K]

def sig {e : K⟦X⟧} (he : HasSubst e) : K⟦X⟧ →+* LaurentSeries K :=
  toL.comp (substAlgHom he : K⟦X⟧ →ₐ[K] K⟦X⟧).toRingHom

theorem sig_apply {e : K⟦X⟧} (he : HasSubst e) (f : K⟦X⟧) : sig he f = toL (f.subst e) := by
  simp [sig, PowerSeries.coe_substAlgHom]

theorem sig_X {e : K⟦X⟧} (he : HasSubst e) : sig he X = toL e := by
  rw [sig_apply, PowerSeries.subst_X he]

theorem sig_C {e : K⟦X⟧} (he : HasSubst e) (r : K) : sig he (C r) = HahnSeries.C r := by
  have h : (C r : K⟦X⟧).subst e = C r := by
    rw [← PowerSeries.coe_substAlgHom he]
    exact (PowerSeries.substAlgHom he).commutes r
  rw [sig_apply, h, HahnSeries.ofPowerSeries_C]

theorem isDer_dL' : IsDer (dL : LaurentSeries K → LaurentSeries K) := isDer_dL

theorem constCurve_dL (W : WeierstrassCurve K) : ConstCurve dL (curveL W) := by
  have h : ∀ c : K, dL (HahnSeries.C c : LaurentSeries K) = 0 := by
    intro c
    ext n
    simp [dL, HahnSeries.C_apply, HahnSeries.coeff_single]
  exact ⟨h _, h _, h _, h _, h _⟩

variable (W : WeierstrassCurve K) {e : K⟦X⟧} (he : HasSubst e)

theorem fwAt_sig : fwAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fw W) := by
  simp only [fwAt, fw, map_sub, map_mul, map_pow, map_one, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

theorem fuAt_sig : fuAt (curveL W) (sig he X) (sig he (wSer W)) = sig he (fu W) := by
  simp only [fuAt, fu, map_add (f := _), map_mul, map_pow, map_ofNat, sig_C,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]

theorem wEq_sig : WEq (curveL W) (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have h := congrArg (sig he) hw
  simp only [map_add (f := _), map_mul, map_pow, sig_C] at h
  simp only [WEq, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  exact h

theorem isFlowUW_sig (hc : ∀ f : K⟦X⟧, derivative (f.subst e) = (D W f).subst e) :
    IsFlowUW (curveL W) dL (sig he X) (sig he (wSer W)) := by
  have hw : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
      + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 :=
    (Formalism.ELL.wSeriesUnique K W).choose_spec.1.2
  have hd := congrArg PowerSeries.derivative hw
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, nsmul_eq_mul] at hd
  have hDw : D W (wSer W) = fu W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, fw, fu]
    linear_combination hd
  have hDX : D W X = fw W := by
    rw [D, Derivation.smul_apply, smul_eq_mul, PowerSeries.derivative_X, mul_one]
  refine ⟨wEq_sig W he, ?_, ?_⟩
  · have h2 : dL (sig he X) = sig he (fw W) := by
      have h1 := hc X
      rw [PowerSeries.subst_X he, hDX] at h1
      rw [sig_X, sig_apply, dL_toL, h1]
    rw [h2, fwAt_sig]
  · have h2 : dL (sig he (wSer W)) = sig he (fu W) := by
      rw [sig_apply, sig_apply, dL_toL, hc (wSer W), hDw]
    rw [h2, fuAt_sig]

theorem inv_mul_sig (hne : toL e ≠ 0) :
    (toL e)⁻¹ ^ 3 * sig he (xS W) * sig he (wSer W) = 1 := by
  have h1 : sig he (wU W) * sig he (xS W) = 1 := by rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  rw [CurveSer.wSer_eq, map_mul, map_pow, sig_X]
  calc (toL e)⁻¹ ^ 3 * sig he (xS W) * (toL e ^ 3 * sig he (wU W))
      = ((toL e)⁻¹ * toL e) ^ 3 * (sig he (wU W) * sig he (xS W)) := by ring
    _ = 1 := by rw [h1, h2, one_pow, one_mul]

include he in
theorem isFlow_sig (hc : ∀ f : K⟦X⟧, derivative (f.subst e) = (D W f).subst e)
    (hne : toL e ≠ 0) :
    IsFlow (curveL W) dL ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))
      ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) := by
  have h := chartFlowToFlow _ (curveL W) dL (sig he X) (sig he (wSer W))
    ((toL e)⁻¹ ^ 3 * sig he (xS W)) isDer_dL' (isFlowUW_sig W he hc) (inv_mul_sig W he hne)
  have h2 : (toL e)⁻¹ * toL e = 1 := inv_mul_cancel₀ hne
  have hx : sig he X * ((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) := by
    rw [sig_X, sig_apply]
    linear_combination (toL e)⁻¹ ^ 2 * toL ((xS W).subst e) * h2
  have hy : -((toL e)⁻¹ ^ 3 * sig he (xS W)) = (toL e)⁻¹ ^ 3 * toL ((yS W).subst e) := by
    rw [← sig_apply he (yS W), yS, map_neg, mul_neg]
  rwa [hx, hy] at h

include he in
theorem mul_yZ_sig (hne : toL e ≠ 0) :
    toL e * ((toL e)⁻¹ ^ 3 * toL ((yS W).subst e)) = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by
  have hy : (yS W).subst e = -((xS W).subst e) := by
    rw [yS, ← PowerSeries.coe_substAlgHom he, map_neg]
  rw [hy, map_neg]
  have ht : toL e * (toL e)⁻¹ = 1 := mul_inv_cancel₀ hne
  calc toL e * ((toL e)⁻¹ ^ 3 * -toL ((xS W).subst e))
      = -((toL e * (toL e)⁻¹) * ((toL e)⁻¹ ^ 2 * toL ((xS W).subst e))) := by ring
    _ = -((toL e)⁻¹ ^ 2 * toL ((xS W).subst e)) := by rw [ht, one_mul]

end Wp

open Wp

theorem flowZ_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : FlowZ.{u} := by
  intro K _ _ W
  obtain ⟨h0, h1, -, -, -⟩ := hE K W
  have he : HasSubst (expSer W) := HasSubst.of_constantCoeff_zero' h0
  have inj : Function.Injective (toL : K⟦X⟧ →+* LaurentSeries K) := HahnSeries.ofPowerSeries_injective
  have hne : toL (expSer W) ≠ 0 := by
    intro h
    have h' : expSer W = 0 := inj (by rw [h, map_zero])
    rw [h', map_zero] at h1
    exact zero_ne_one h1
  exact ⟨Wp.isFlow_sig W he (hC K W) hne, Wp.mul_yZ_sig W he hne⟩

theorem wpODE_of (hE : ExpSpec.{u}) (hC : ChainZ.{u}) : WpODE.{u} := by
  intro K _ _ W
  have hF := (flowZ_of hE hC K W).1
  have h6 : IsUnit (6 : LaurentSeries K) := by
    have h := (IsUnit.mk0 (6 : K) (by norm_num)).map (HahnSeries.C : K →+* LaurentSeries K)
    rwa [map_ofNat] at h
  have hb : 12 * (HahnSeries.C (W.b₂ / 12) : LaurentSeries K) = (curveL W).b₂ := by
    rw [WeierstrassCurve.map_b₂, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    field_simp
  have hg2 : 12 * (HahnSeries.C (g₂ W) : LaurentSeries K) = (curveL W).c₄ := by
    rw [WeierstrassCurve.map_c₄, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 12, ← map_mul]
    congr 1
    rw [g₂]
    field_simp
  have hg3 : 216 * (HahnSeries.C (g₃ W) : LaurentSeries K) = (curveL W).c₆ := by
    rw [WeierstrassCurve.map_c₆, ← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 216, ← map_mul]
    congr 1
    rw [g₃]
    field_simp
  obtain ⟨h1, h2, h3⟩ := flowWeierstrassForm _ (curveL W) dL (xZ W) (yZ W) (HahnSeries.C (W.b₂ / 12))
    (HahnSeries.C (g₂ W)) (HahnSeries.C (g₃ W)) isDer_dL' (constCurve_dL W) hF h6 hb hg2 hg3
  refine ⟨?_, h2, ?_⟩
  · simpa only [wpL, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] using h1
  · have hh : (HahnSeries.C (1 / 2 : K) : LaurentSeries K) * 2 = 1 := by
      rw [← map_ofNat (HahnSeries.C : K →+* LaurentSeries K) 2, ← map_mul, ← map_one HahnSeries.C]
      congr 1
      norm_num
    have hg : (HahnSeries.C (g₂ W / 2) : LaurentSeries K)
        = HahnSeries.C (1 / 2 : K) * HahnSeries.C (g₂ W) := by
      rw [← map_mul]
      congr 1
      ring
    rw [hg]
    change 2 * dL (dL (wpL W)) = 12 * wpL W ^ 2 - HahnSeries.C (g₂ W) at h3
    linear_combination HahnSeries.C (1 / 2 : K) * h3 - (dL (dL (wpL W)) - 6 * wpL W ^ 2) * hh

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.CurveL
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

namespace CurveL

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem DL_apply (f : LaurentSeries R) : DL W f = toL (fw W) * dL f := rfl

theorem isDer_DL : IsDer (DL W) := by
  unfold IsDer
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · simp only [DL, map_add (f := _), mul_add]
  · simp only [DL, dL_mul]
    ring

theorem DL_C (r : R) : DL W (HahnSeries.C r) = 0 := by
  simp only [DL, dL_C, mul_zero]

theorem constCurve_DL : ConstCurve (DL W) (curveL W) := ⟨DL_C W _, DL_C W _, DL_C W _, DL_C W _, DL_C W _⟩

theorem DL_toL (f : R⟦X⟧) : DL W (toL f) = toL (D W f) := by
  rw [DL_apply, dL_toL, CurveSer.D_apply, map_mul]

theorem fwAt_toL : fwAt (curveL W) (toL X) (toL (wSer W)) = toL (fw W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fwAt fw
  simp [h2, h3]

theorem fuAt_toL : fuAt (curveL W) (toL X) (toL (wSer W)) = toL (fu W) := by
  have h2 : toL (2 : R⟦X⟧) = 2 := by
    rw [show (2 : R⟦X⟧) = ((2 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  have h3 : toL (3 : R⟦X⟧) = 3 := by
    rw [show (3 : R⟦X⟧) = ((3 : ℕ) : R⟦X⟧) by norm_num, map_natCast]
    norm_num
  unfold fuAt fu
  simp [h2, h3]

theorem isFlowUW_toL : IsFlowUW (curveL W) (DL W) (toL X) (toL (wSer W)) := by
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    conv_lhs => rw [(CurveSer.wSer_fixed W).2]
    simp
  · rw [DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]
  · rw [DL_toL, CurveSer.D_apply, mul_comm (fw W), CurveSer.deriv_wSer_mul_fw, fuAt_toL]

theorem inv_mul_wSer : uPow (-3) * toL (xS W) * toL (wSer W) = 1 := by
  have e0 : toL (X ^ 3 : R⟦X⟧) = uPow 3 := by
    unfold uPow
    rw [HahnSeries.ofPowerSeries_X_pow]
    norm_num
  have e1 : uPow (-3) * toL (X ^ 3 : R⟦X⟧) = 1 := by
    rw [e0, ← uPow_add]
    show HahnSeries.single (-3 + 3 : ℤ) (1 : R) = 1
    rw [show (-3 + 3 : ℤ) = 0 by norm_num]
    first
      | rfl
      | simp
  have e2 : toL (wU W) * toL (xS W) = 1 := by
    rw [← map_mul, CurveSer.wU_mul_xS, map_one]
  rw [CurveSer.wSer_eq W, map_mul]
  linear_combination (toL (wU W) * toL (xS W)) * e1 + e2

theorem toL_X_mul_inv : toL X * (uPow (-3) * toL (xS W)) = xL W := by
  have e : toL (X : R⟦X⟧) * uPow (-3) = uPow (-2) := by
    have e0 : toL (X : R⟦X⟧) = uPow 1 := by
      unfold uPow
      exact HahnSeries.ofPowerSeries_X
    rw [e0, ← uPow_add]
    norm_num
  unfold xL
  rw [← mul_assoc, e]

theorem neg_inv : -(uPow (-3) * toL (xS W)) = yL W := by
  unfold yL yS
  rw [map_neg, mul_neg]

theorem isFlow_xL_yL : IsFlow (curveL W) (DL W) (xL W) (yL W) := by
  obtain ⟨hW, hDu, hDw⟩ := isFlowUW_toL W
  have hvw := inv_mul_wSer W
  have hD := isDer_DL W
  have h1 : DL W 1 = 0 := by simpa using DL_C W 1
  have hv := hD.2 (uPow (-3) * toL (xS W)) (toL (wSer W))
  rw [hvw, h1, hDw] at hv
  unfold fuAt at hv
  have hneg : ∀ f, DL W (-f) = -DL W f := fun f => by simp only [DL, map_neg, mul_neg]
  unfold IsFlow
  rw [← toL_X_mul_inv W, ← neg_inv W, hD.2, hDu, hneg]
  unfold fwAt
  unfold WEq at hW
  rw [WeierstrassCurve.Affine.equation_iff]
  set w := toL (wSer W) with hw
  set v := uPow (-3) * toL (xS W) with hv'
  set u := toL (X : R⟦X⟧) with hu
  set Dv := DL W v with hDv
  refine ⟨?_, ?_, ?_⟩
  · linear_combination v ^ 3 * hW + (-v ^ 2 + (curveL W).a₁ * u * v ^ 2
      + (curveL W).a₂ * u ^ 2 * v ^ 2 + (curveL W).a₃ * v * (w * v + 1)
      + (curveL W).a₄ * u * v * (w * v + 1) + (curveL W).a₆ * (w ^ 2 * v ^ 2 + w * v + 1)) * hvw
  · linear_combination 3 * v ^ 2 * hW + (-3 * v + 2 * (curveL W).a₁ * u * v
      + (curveL W).a₂ * u ^ 2 * v + (curveL W).a₃ * (3 * v * w + 1)
      + 2 * (curveL W).a₄ * u * v * w + 3 * (curveL W).a₆ * w * v * w - u * Dv) * hvw
      - u * v * hv
  · linear_combination ((curveL W).a₁ * v + 2 * (curveL W).a₂ * u * v
      + (curveL W).a₄ * (v * w + 1) + Dv) * hvw + v * hv

theorem toL_X_mul_yL : toL X * yL W = -xL W := by
  rw [← neg_inv W, ← toL_X_mul_inv W]
  ring

theorem toL_wSer_mul_yL : toL (wSer W) * yL W = -1 := by
  rw [← neg_inv W]
  linear_combination -(inv_mul_wSer W)

theorem toL_wSer_mul_xL : toL (wSer W) * xL W = toL X := by
  rw [← toL_X_mul_inv W]
  linear_combination toL (X : R⟦X⟧) * inv_mul_wSer W

end CurveL

open CurveL

theorem invariant_derivation_spec : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩

theorem invariant_flow : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩

end Formalism.L2.Th1.A
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.LogExp
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

section SlopeTestRemainingChoices

variable {R : Type u} [CommRing R]

theorem subst_neg' {a : R⟦X⟧} (ha : HasSubst a) (f : R⟦X⟧) : (-f).subst a = -f.subst a := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_neg _ f)
    | simp [PowerSeries.subst_neg ha]

theorem subst_one' {a : R⟦X⟧} (ha : HasSubst a) : (1 : R⟦X⟧).subst a = 1 := by
  first
    | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_one _)
    | simp

private theorem hasSubst_lemma {a : R⟦X⟧} (h : constantCoeff a = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero' h
  | exact HasSubst.of_constantCoeff_zero h
  | exact PowerSeries.HasSubst.of_constantCoeff_zero' h

private theorem powerSeries_subst_mul_of_hasSubst {a : R⟦X⟧} (ha : HasSubst a) (f g : R⟦X⟧) :
    (f * g).subst a = f.subst a * g.subst a := by
  first
  | exact PowerSeries.subst_mul ha f g
  | (rw [← PowerSeries.coe_substAlgHom ha]; exact map_mul _ f g)

private theorem constantCoeff_powerSeries_subst_eq_zero {a f : R⟦X⟧} (ha0 : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    constantCoeff (f.subst a) = 0 := by
  obtain ⟨h, rfl⟩ := (PowerSeries.X_dvd_iff).mpr hf
  rw [powerSeries_subst_mul_of_hasSubst (hasSubst_lemma ha0), PowerSeries.subst_X (hasSubst_lemma ha0), map_mul, ha0, zero_mul]

private theorem powerSeries_subst_subst_eq_subst_subst {a b f : R⟦X⟧} (ha : HasSubst a) (hb : HasSubst b) :
    PowerSeries.subst b (PowerSeries.subst a f : R⟦X⟧)
      = PowerSeries.subst (PowerSeries.subst b a : R⟦X⟧) f := by
  first
  | exact PowerSeries.subst_comp_subst_apply ha hb f
  | exact (PowerSeries.subst_comp_subst_apply ha hb f).symm
  | rw [PowerSeries.subst_comp_subst_apply ha hb]

theorem subst_injective_of_leftInverse {l e a b : R⟦X⟧} (hl : HasSubst l) (ha : HasSubst a)
    (hb : HasSubst b) (hel : e.subst l = X) (h : l.subst a = l.subst b) : a = b := by
  calc a = e.subst (l.subst a) := by
        rw [← powerSeries_subst_subst_eq_subst_subst hl ha, hel, PowerSeries.subst_X ha]
    _ = e.subst (l.subst b) := by rw [h]
    _ = b := by rw [← powerSeries_subst_subst_eq_subst_subst hl hb, hel, PowerSeries.subst_X hb]

end SlopeTestRemainingChoices

theorem logSpec_of (hI : IntegSpec.{u}) (hU : UnitSpec.{u}) : LogSpec.{u} := by
  intro K _ _ W
  obtain ⟨hc, hd, -⟩ := hI K (om W)
  obtain ⟨-, hfo, ho0, -⟩ := hU K W
  refine ⟨hc, ?_, hd, ?_⟩
  · simp only [logSer, integ, coeff_mk]
    simp [ho0]
  · simp only [D, logSer, Derivation.smul_apply, smul_eq_mul, hd, hfo]

theorem expSpec_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ExpSpec.{u} := by
  intro K _ _ W
  obtain ⟨hL0, hL1, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨-, hfo, -⟩ := hU K W
  obtain ⟨hE0, hLE, hEL, hcoef, -⟩ := hC K (logSer W) hL0 (by rw [hL1]; exact isUnit_one)
  have hE0' : constantCoeff (expSer W) = 0 := hE0
  have hLE' : (logSer W).subst (expSer W) = X := hLE
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0'
  refine ⟨hE0, ?_, hLE, hEL, ?_⟩
  · have h : coeff 1 (expSer W) * coeff 1 (logSer W) = 1 := hcoef
    rwa [hL1, mul_one] at h
  · have h1 := congrArg (fun f : K⟦X⟧ => PowerSeries.derivative (R := K) f) hLE'
    rw [derivative_subst hs, hLd, derivative_X] at h1
    have h2 : (fw W).subst (expSer W) * (om W).subst (expSer W) = 1 := by
      rw [← powerSeries_subst_mul_of_hasSubst hs, hfo, subst_one' hs]
    calc PowerSeries.derivative (R := K) (expSer W)
        = ((fw W).subst (expSer W) * (om W).subst (expSer W)) * PowerSeries.derivative (R := K) (expSer W) := by
          rw [h2, one_mul]
      _ = (fw W).subst (expSer W) := by rw [mul_assoc, h1, mul_one]

theorem chainZ_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u}) :
    ChainZ.{u} := by
  intro K _ _ W f
  obtain ⟨hE0, -, -, -, hEd⟩ := expSpec_of hI hC hU K W
  have hs : HasSubst (expSer W) := hasSubst_lemma hE0
  rw [derivative_subst hs, hEd]
  simp only [D, Derivation.smul_apply, smul_eq_mul]
  rw [powerSeries_subst_mul_of_hasSubst hs, mul_comm]

theorem logNeg_of (hI : IntegSpec.{u}) (hC : CompInvSpec.{u}) (hU : UnitSpec.{u})
    (hS : ISerSpec.{u}) : LogNeg.{u} := by
  intro K _ _ W
  obtain ⟨hL0, -, hLd, -⟩ := logSpec_of hI hU K W
  obtain ⟨hE0, -, hLE, hEL, -⟩ := expSpec_of hI hC hU K W
  obtain ⟨hi0, -, -, -, -, -, -, hiom⟩ := hS K W
  have hsi : HasSubst (iSer W) := hasSubst_lemma hi0
  have hsE : HasSubst (expSer W) := hasSubst_lemma hE0
  have hL' : (logSer W).subst (iSer W) = -logSer W := by
    obtain ⟨-, -, huniq⟩ := hI K (-om W)
    have e1 := huniq ((logSer W).subst (iSer W)) (constantCoeff_powerSeries_subst_eq_zero hi0 hL0)
      (by rw [derivative_subst hsi, hLd, hiom])
    have e2 := huniq (-logSer W) (by rw [map_neg, hL0, neg_zero]) (by rw [map_neg, hLd])
    rw [e1, e2]
  refine ⟨hL', ?_⟩
  have hnX0 : constantCoeff (-X : K⟦X⟧) = 0 := by simp
  have hsn : HasSubst (-X : K⟦X⟧) := hasSubst_lemma hnX0
  apply subst_injective_of_leftInverse (l := logSer W) (e := expSer W) (hasSubst_lemma hL0)
    (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hnX0 hE0)) (hasSubst_lemma (constantCoeff_powerSeries_subst_eq_zero hE0 hi0)) hEL
  rw [← powerSeries_subst_subst_eq_subst_subst hsE hsn, hLE, PowerSeries.subst_X hsn, ← powerSeries_subst_subst_eq_subst_subst hsi hsE, hL',
    subst_neg' hsE, hLE]

end Formalism.L2.Th1.A
end
end

