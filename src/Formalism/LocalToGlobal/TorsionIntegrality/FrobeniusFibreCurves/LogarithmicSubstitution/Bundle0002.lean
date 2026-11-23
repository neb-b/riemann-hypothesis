module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0001

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
section
noncomputable section

namespace Formalism.L2.Th1.B.Map

open Formalism.InvariantFactorPaths.G7 (at1 cob)

variable {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (j : K →+* K')

theorem map_psubst {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (MvPowerSeries.map j a) (PowerSeries.map j f) := by
  have ha' : MvPowerSeries.constantCoeff (MvPowerSeries.map j a) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, ha, map_zero]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hs' := PowerSeries.HasSubst.of_constantCoeff_zero ha'
  ext e
  rw [MvPowerSeries.coeff_map, PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs',
    map_finsum j (PowerSeries.coeff_subst_finite hs f e)]
  refine finsum_congr fun d => ?_
  rw [smul_eq_mul, smul_eq_mul, map_mul, PowerSeries.coeff_map, ← map_pow (MvPowerSeries.map j),
    MvPowerSeries.coeff_map]

theorem map_psubst' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0)
    (f : PowerSeries K) :
    PowerSeries.map j (PowerSeries.subst a f) =
      PowerSeries.subst (PowerSeries.map j a) (PowerSeries.map j f) :=
  map_psubst j (ι := Unit) ha f

theorem map_fExp {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.map j (fExp a) = fExp (MvPowerSeries.map j a) := by
  unfold Formalism.L2.Th1.B.fExp
  rw [map_psubst j ha, PowerSeries.map_exp]

theorem map_fExp' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.map j (fExp a) = fExp (PowerSeries.map j a) :=
  map_fExp j (ι := Unit) ha

theorem map_fLog {ι : Type} {a : MvPowerSeries ι K} (ha : MvPowerSeries.constantCoeff a = 1) :
    MvPowerSeries.map j (fLog a) = fLog (MvPowerSeries.map j a) := by
  have h' : MvPowerSeries.constantCoeff (a - 1) = 0 := by rw [map_sub, ha, map_one, sub_self]
  unfold Formalism.L2.Th1.B.fLog
  rw [map_psubst j h', map_sub, map_one, PowerSeries.map_log]

theorem map_fLog' {a : PowerSeries K} (ha : PowerSeries.constantCoeff a = 1) :
    PowerSeries.map j (fLog a) = fLog (PowerSeries.map j a) :=
  map_fLog j (ι := Unit) ha

theorem map_prim (f : PowerSeries K) :
    PowerSeries.map j (prim f) = prim (PowerSeries.map j f) := by
  ext n
  simp only [Formalism.L2.Th1.B.prim, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp [map_div₀, map_natCast]

theorem map_lU (l : PowerSeries K) :
    PowerSeries.map j (lU l) = lU (PowerSeries.map j l) := by
  ext n
  simp only [Formalism.L2.Th1.B.lU, PowerSeries.coeff_map, PowerSeries.coeff_mk]

private theorem powerSeries_constantCoeff_map' (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.map j f) = j (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map]

theorem map_inv' {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    PowerSeries.map j f⁻¹ = (PowerSeries.map j f)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map j f) ≠ 0 := by
    rw [powerSeries_constantCoeff_map']; exact (map_ne_zero j).mpr hf
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ hf, map_one]

theorem map_sigS (P : PowerSeries K) :
    PowerSeries.map j (sigS P) = sigS (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, map_prim, map_prim]

theorem cc_sigS (P : PowerSeries K) : PowerSeries.constantCoeff (sigS P) = 0 := by
  unfold Formalism.L2.Th1.B.sigS
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigmaOneSeries e1 kap w) = sigmaOneSeries (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, map_prim, map_prim, map_add (f := _), map_mul, PowerSeries.map_C,
    PowerSeries.map_C]

theorem cc_sig1S (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  unfold Formalism.L2.Th1.B.sigmaOneSeries
  rw [map_neg, Formalism.L2.Th1.B.constantCoeff_prim, neg_zero]

theorem map_sigma (P : PowerSeries K) :
    PowerSeries.map j (sigma P) = sigma (PowerSeries.map j P) := by
  unfold Formalism.L2.Th1.B.sigma
  rw [map_mul, PowerSeries.map_X, map_fExp' j (cc_sigS P),
    map_sigS]

theorem map_sgStar (s2 : K) (P : PowerSeries K) :
    PowerSeries.map j (sgStar s2 P) = sgStar (j s2) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0 := by
    simp
  unfold Formalism.L2.Th1.B.sgStar
  rw [map_mul, map_sigma, map_fExp' j hc, map_neg, map_mul, PowerSeries.map_C,
    map_pow, PowerSeries.map_X, map_div₀, map_ofNat]

theorem map_sigma1 (e1 kap : K) (w : PowerSeries K) :
    PowerSeries.map j (sigma1 e1 kap w) = sigma1 (j e1) (j kap) (PowerSeries.map j w) := by
  unfold Formalism.L2.Th1.B.sigma1
  rw [map_fExp' j (cc_sig1S e1 kap w), map_sig1S]

theorem map_wOf (e1 : K) (P : PowerSeries K) :
    PowerSeries.map j (wOf e1 P) = wOf (j e1) (PowerSeries.map j P) := by
  have hc : PowerSeries.constantCoeff
      (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) ≠ 0 := by
    simp
  unfold Formalism.L2.Th1.B.wOf
  rw [map_mul, map_inv' j hc]
  simp only [map_pow, map_sub, map_add (f := _), map_one, map_mul, PowerSeries.map_X, PowerSeries.map_C]

theorem map_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.map j (phO s2 P l) = phO (j s2) (PowerSeries.map j P) (PowerSeries.map j l) := by
  have hd : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU l) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.B.lU, PowerSeries.coeff_mk, zero_add, h1]
  unfold Formalism.L2.Th1.B.phO
  rw [map_sub, map_add (f := _), map_neg, map_psubst' j h0, map_sigS, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow, map_fLog' j hd, map_lU]

theorem map_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.map j (phE s2 e1 kap w l) =
      phE (j s2) (j e1) (j kap) (PowerSeries.map j w) (PowerSeries.map j l) := by
  unfold Formalism.L2.Th1.B.phE
  rw [map_add (f := _), map_neg, map_psubst' j h0, map_sig1S, map_mul,
    PowerSeries.map_C, map_div₀, map_ofNat, map_pow]

theorem map_inVar {ι : Type} (x : ι) (f : PowerSeries K) :
    MvPowerSeries.map j (at1 x f) = at1 x (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [map_psubst j (MvPowerSeries.constantCoeff_X x), MvPowerSeries.map_X]

theorem map_cob {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) :
    MvPowerSeries.map j (cob F f) = cob (MvPowerSeries.map j F) (PowerSeries.map j f) := by
  unfold Formalism.InvariantFactorPaths.G7.cob
  rw [map_sub, map_sub, map_psubst j hF, map_inVar, map_inVar]

theorem baseChangeCompatible : BaseChange := by
  intro K K' _ _ _ _ j s2 e1 kap P w l F h0 h1 hF
  exact ⟨map_sigma j P, map_sgStar j s2 P, map_sigma1 j e1 kap w,
    map_wOf j e1 P, map_phO j s2 P h0 h1,
    map_phE j s2 e1 kap w h0, fun f => map_cob j hF f⟩

end Formalism.L2.Th1.B.Map
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSig1S
section
noncomputable section

namespace Formalism.L2.Th1.B.Sq

open PowerSeries

variable {K : Type} [Field K] [CharZero K]

theorem rescale_fExp (a : K) {f : PowerSeries K} (hf : constantCoeff f = 0) :
    rescale a (fExp f) = fExp (rescale a f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst]
  have hφ : ∀ _ : Unit, MvPowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0 := by
    intro _
    show PowerSeries.constantCoeff (a • (PowerSeries.X : PowerSeries K)) = 0
    rw [PowerSeries.smul_eq_C_mul]
    simp
  exact subst_fExp (φ := fun _ => (a • PowerSeries.X : PowerSeries K)) hφ hf

theorem coeff_prim_succ (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (prim f) = coeff n f / ((n + 1 : ℕ) : K) := by
  simp [prim, PowerSeries.coeff_mk]

theorem coeff_zero_prim (f : PowerSeries K) : coeff 0 (prim f) = 0 := by
  simp [prim, PowerSeries.coeff_mk]

theorem constantCoeff_sigS (P : PowerSeries K) : constantCoeff (sigS P) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sigS, map_neg, coeff_zero_prim, neg_zero]

theorem constantCoeff_sig1S (e1 kap : K) (w : PowerSeries K) :
    constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, sigmaOneSeries, map_neg, coeff_zero_prim, neg_zero]

private theorem pd_unit_eq_dz (f : PowerSeries K) : pd () f = dz f := by
  ext n
  rw [PowerSeries.coeff_derivative,
    PowerSeries.coeff_def (s := Finsupp.single () n) (by simp), MvPowerSeries.coeff_pderiv,
    PowerSeries.coeff_def (s := Finsupp.single () (n + 1)) (by simp), ← Finsupp.single_add,
    Finsupp.single_eq_same]

theorem mul_dz_fLog {g : PowerSeries K} (hg : constantCoeff g = 1) : g * dz (fLog g) = dz g := by
  have h := mul_pd_fLog (ι := Unit) () (g := g) hg
  rwa [pd_unit_eq_dz, pd_unit_eq_dz] at h

private theorem dz_prim_eq_self (f : PowerSeries K) : dz (prim f) = f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_prim_succ]
  push_cast
  exact div_mul_cancel₀ _ (Nat.cast_add_one_ne_zero n)

private theorem eq_of_constantCoeff_eq_of_dz_eq {F G : PowerSeries K} (h0 : constantCoeff F = constantCoeff G)
    (hd : dz F = dz G) : F = G := by
  ext n
  rcases n with _ | m
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h := congrArg (coeff m) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at h
    exact mul_right_cancel₀ (Nat.cast_add_one_ne_zero m) h

theorem sigmaOneSquare : Sigma1Sq := by
  intro K _ _ g2 g3 e1 P hP hc
  obtain ⟨q, rfl⟩ : ∃ q, g2 = 4 * q := ⟨g2 / 4, by ring⟩
  have hk : (3 * e1 ^ 2 - 4 * q / 4 : K) = 3 * e1 ^ 2 - q := by ring
  rw [hk]
  obtain ⟨hR1, hR2⟩ := weierstrassReducedEquations K (4 * q) g3 P hP
  have h42 : (4 * q / 2 : K) = 2 * q := by ring
  rw [h42] at hR2
  have hcC : PowerSeries.C (4 * e1 ^ 3 - 4 * q * e1 - g3) = 0 := by rw [hc, map_zero]
  simp only [map_sub, map_mul, map_pow, map_ofNat] at hR1 hR2 hcC
  set w := wOf e1 P with hwdef
  set u : PowerSeries K := 1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2 with hudef
  have hu0 : constantCoeff u = 1 := by simp [hudef]
  have hwu : w * u = PowerSeries.X ^ 2 := by
    have e : w = PowerSeries.X ^ 2 * u⁻¹ := rfl
    rw [e, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hu0]; exact one_ne_zero), mul_one]
  set L : PowerSeries K := fLog u with hLdef
  have hL0 : constantCoeff L = 0 := constantCoeff_fLog hu0
  have huL : u * dz L = dz u := mul_dz_fLog hu0
  have hdu : dz u = 2 * PowerSeries.X * P + PowerSeries.X ^ 2 * dz P - 2 * PowerSeries.C e1 * PowerSeries.X := by
    simp [hudef, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      PowerSeries.derivative_C]
    ring
  have hddu : dz (dz u) = 2 * P + 4 * PowerSeries.X * dz P + PowerSeries.X ^ 2 * dz (dz P) -
      2 * PowerSeries.C e1 := by
    have hd2 : PowerSeries.derivative (R := K) (2 : PowerSeries K) = 0 := by
      rw [show (2 : PowerSeries K) = PowerSeries.C 2 from (map_ofNat _ 2).symm]
      exact PowerSeries.derivative_C
    rw [hdu]
    simp [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      PowerSeries.derivative_C, hd2]
    ring
  have hT : u * dz (dz u) - dz u ^ 2 =
      u ^ 2 * (2 * P - 2 * PowerSeries.C e1) -
        2 * (3 * PowerSeries.C e1 ^ 2 - PowerSeries.C q) * PowerSeries.X ^ 2 * u := by
    rw [hddu, hdu, hudef]
    linear_combination (1 + PowerSeries.X ^ 2 * P - PowerSeries.C e1 * PowerSeries.X ^ 2) * hR2 - hR1 -
      PowerSeries.X ^ 4 * hcC
  have hB : u * dz (dz L) + dz L * dz u = dz (dz u) := by
    have h := congrArg (PowerSeries.derivative (R := K)) huL
    rwa [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 (fun h => by rw [h] at hu0; simp at hu0)
  have hLdd : dz (dz L) = 2 * P - 2 * PowerSeries.C e1 - 2 * PowerSeries.C (3 * e1 ^ 2 - q) * w := by
    apply mul_left_cancel₀ hu2
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination u * hB - dz u * huL + hT + 2 * (3 * PowerSeries.C e1 ^ 2 - PowerSeries.C q) * u * hwu
  have hp0 : ∀ f : PowerSeries K, constantCoeff (prim f) = 0 := fun f => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact coeff_zero_prim f
  have hL1 : constantCoeff (dz L) = 0 := by
    have h := congrArg PowerSeries.constantCoeff huL
    rw [map_mul, hu0, one_mul, hdu] at h
    simpa using h
  have hs0 := constantCoeff_sigS P
  have hs10 := constantCoeff_sig1S e1 (3 * e1 ^ 2 - q) w
  have hkey : sigmaOneSeries e1 (3 * e1 ^ 2 - q) w + sigmaOneSeries e1 (3 * e1 ^ 2 - q) w = sigS P + sigS P + L := by
    apply eq_of_constantCoeff_eq_of_dz_eq
    · rw [map_add (f := _), map_add (f := _), map_add (f := _), hs0, hs10, hL0]; ring
    · apply eq_of_constantCoeff_eq_of_dz_eq
      · simp only [map_add (f := _), sigmaOneSeries, sigS, map_neg, dz_prim_eq_self, hp0, hL1]
        ring
      · simp only [map_add (f := _), sigmaOneSeries, sigS, map_neg, dz_prim_eq_self, hLdd]
        ring
  have hsq : fExp (sigmaOneSeries e1 (3 * e1 ^ 2 - q) w) ^ 2 = fExp (sigS P + sigS P) * u := by
    have hss : MvPowerSeries.constantCoeff (sigS P + sigS P) = 0 := by
      rw [map_add (f := _)]
      exact (show PowerSeries.constantCoeff (sigS P) + PowerSeries.constantCoeff (sigS P) = 0 by
        rw [hs0, add_zero])
    rw [sq, ← fExp_add hs10 hs10, hkey, fExp_add hss hL0, hLdef, fExp_fLog hu0]
  show PowerSeries.X ^ 2 * fExp (sigmaOneSeries e1 (3 * e1 ^ 2 - q) w) ^ 2 =
    (PowerSeries.X * fExp (sigS P)) ^ 2 * u
  rw [hsq, fExp_add hs0 hs0]
  ring

end Formalism.L2.Th1.B.Sq
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec
section
noncomputable section

namespace Formalism.L2.Th1.B.Ph

open PowerSeries

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem hs {l : PowerSeries K} (hl : constantCoeff l = 0) : HasSubst l := by
  exact HasSubst.of_constantCoeff_zero' hl

theorem psubst_neg {l : PowerSeries K} (hl : constantCoeff l = 0) (f : PowerSeries K) :
    subst l (-f) = -subst l f := by
  rw [← coe_substAlgHom (hs hl), map_neg]

theorem psubst_C_mul {l : PowerSeries K} (hl : constantCoeff l = 0) (c : K) (f : PowerSeries K) :
    subst l (C c * f) = C c * subst l f := by
  rw [subst_mul (hs hl), subst_C]
  rfl

theorem constantCoeff_psubst {l : PowerSeries K} (hl : constantCoeff l = 0) (g : PowerSeries K) :
    constantCoeff (subst l g) = constantCoeff g := by
  have h0 : constantCoeff (subst l (g - C (constantCoeff g))) = 0 :=
    constantCoeff_subst_eq_zero hl _ (by simp)
  have hg : g = C (constantCoeff g) + (g - C (constantCoeff g)) := by ring
  conv_lhs => rw [hg]
  rw [subst_add (hs hl), map_add (f := _), h0, subst_C, add_zero]
  rfl

theorem psubst_fExp {l f : PowerSeries K} (hl : constantCoeff l = 0) (hf : constantCoeff f = 0) :
    subst l (fExp f) = fExp (subst l f) := by
  unfold fExp
  exact subst_comp_subst_apply (hs hf) (hs hl) _

theorem psubst_fLog {l g : PowerSeries K} (hl : constantCoeff l = 0) (hg : constantCoeff g = 1) :
    subst l (fLog g) = fLog (subst l g) := by
  have h1 : constantCoeff (g - 1) = 0 := by rw [map_sub, hg, map_one, sub_self]
  unfold fLog
  rw [subst_comp_subst_apply (hs h1) (hs hl), subst_sub (hs hl), psubst_one (hs hl)]

theorem coeff_prim_succ (f : PowerSeries K) (n : ℕ) :
    coeff (n + 1) (prim f) = coeff n f / ((n + 1 : ℕ) : K) := by
  simp [prim]

theorem coeff_zero_prim (f : PowerSeries K) : coeff 0 (prim f) = 0 := by
  simp [prim]

theorem constantCoeff_sigS (P : PowerSeries K) : constantCoeff (sigS P) = 0 := by
  rw [sigS, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]

theorem constantCoeff_sig1S (e1 kap : K) (w : PowerSeries K) :
    constantCoeff (sigmaOneSeries e1 kap w) = 0 := by
  rw [sigmaOneSeries, map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_zero_prim, neg_zero]

theorem X_mul_lU {l : PowerSeries K} (hl : constantCoeff l = 0) : X * lU l = l := by
  ext n
  rcases n with _ | n
  · rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff_apply, hl]
  · rw [coeff_succ_X_mul, lU, coeff_mk]

theorem constantCoeff_lU (l : PowerSeries K) : constantCoeff (lU l) = coeff 1 l := by
  rw [← coeff_zero_eq_constantCoeff_apply, lU, coeff_mk]

theorem constantCoeff_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    constantCoeff (-(C c * l ^ 2)) = 0 := by
  simp [hl]

theorem psubst_gauss (c : K) {l : PowerSeries K} (hl : constantCoeff l = 0) :
    subst l (fExp (-(C c * X ^ 2))) = fExp (-(C c * l ^ 2)) := by
  rw [psubst_fExp hl (by simp), psubst_neg hl, psubst_C_mul hl, subst_pow (hs hl), subst_X (hs hl)]

theorem constantCoeff_phO (s2 : K) (P : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) (hl1 : coeff 1 l = 1) : constantCoeff (phO s2 P l) = 0 := by
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hF : constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  rw [phO, map_sub, map_add (f := _), map_neg, constantCoeff_psubst hl, constantCoeff_sigS, map_mul, map_pow, hl, hF]
  simp

theorem constantCoeff_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : constantCoeff l = 0) : constantCoeff (phE s2 e1 kap w l) = 0 := by
  rw [phE, map_add (f := _), map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, map_mul, map_pow, hl]
  simp

end Alg

theorem logSigmaPullbackSpec : PhODef := by
  intro K _ _ s2 P l hl hl1
  refine ⟨constantCoeff_phO s2 P hl hl1, ?_⟩
  have hlu : MvPowerSeries.constantCoeff (lU l) = 1 := by
    have := constantCoeff_lU l
    rw [hl1] at this
    exact this
  have hA : constantCoeff (fLog (lU l)) = 0 := constantCoeff_fLog hlu
  have hB : constantCoeff (subst l (sigS P)) = 0 := by rw [constantCoeff_psubst hl, constantCoeff_sigS]
  have hC : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  have hAB : constantCoeff (fLog (lU l) + subst l (sigS P)) = 0 := by rw [map_add (f := _), hA, hB, add_zero]
  have e : -phO s2 P l = fLog (lU l) + subst l (sigS P) + -(C (s2 / 2) * l ^ 2) := by
    rw [phO]
    ring
  rw [sgStar, sigma, subst_mul (hs hl), subst_mul (hs hl), subst_X (hs hl),
    psubst_fExp hl (constantCoeff_sigS P), psubst_gauss _ hl]
  calc l * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2))
      = X * fExp (fLog (lU l)) * fExp (subst l (sigS P)) * fExp (-(C (s2 / 2) * l ^ 2)) := by
        rw [fExp_fLog hlu, X_mul_lU hl]
    _ = X * fExp (-phO s2 P l) := by
        rw [e, fExp_add hAB hC, fExp_add hA hB]
        ring

theorem logSigmaOnePullbackSpec : PhEDef := by
  intro K _ _ s2 e1 kap w l hl
  refine ⟨constantCoeff_phE s2 e1 kap w hl, ?_⟩
  have hB : constantCoeff (-subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [map_neg, constantCoeff_psubst hl, constantCoeff_sig1S, neg_zero]
  have hC : constantCoeff (C (s2 / 2) * l ^ 2) = 0 := by simp [hl]
  have hB' : constantCoeff (subst l (sigmaOneSeries e1 kap w)) = 0 := by
    rw [constantCoeff_psubst hl, constantCoeff_sig1S]
  have hC' : constantCoeff (-(C (s2 / 2) * l ^ 2)) = 0 := constantCoeff_gauss _ hl
  rw [subst_mul (hs hl), sigma1, psubst_fExp hl (constantCoeff_sig1S _ _ _), psubst_gauss _ hl,
    ← fExp_add hB' hC']
  congr 1
  rw [phE]
  ring

section Parity

variable {K : Type} [Field K] [CharZero K]

end Parity


end Formalism.L2.Th1.B.Ph
end
end

