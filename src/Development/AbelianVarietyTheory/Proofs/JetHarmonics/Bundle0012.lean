module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffSubstEq
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FeUniq

variable {q : ℕ} [Fact q.Prime]

theorem intSer_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_C {c : ℂ_[q]} (hc : ‖c‖ ≤ 1) : Bd 1 (C c : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (q := q) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (P : Polynomial ℂ_[q]) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    Bd 1 (Polynomial.aeval h P) := by
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : ℂ_[q]⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : Bd 1 h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : ℂ_[q])‖ < 1) (hA : Bd 1 A)
    (hA0 : constantCoeff A = 1) (hB : Bd 1 B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A = f ^ N * B) : Bd 1 f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial ℂ_[q] := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : Bd 1 (P : ℂ_[q]⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : ℂ_[q]⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : ℂ_[q]⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : ℂ_[q]⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : ℂ_[q]⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : ℂ_[q]⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : ℂ_[q]⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : ℂ_[q]⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : ℂ_[q]⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : ℂ_[q]⟦X⟧) N
    rw [hQ] at this
    linear_combination (-B) * this
  have key := congrArg (coeff n) e
  rw [hL, hR, map_add (f := _), map_add (f := _), hX, hX] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_pow, map_sum, hA0, hB0, hf, hP0, hsQ, hQ0, h'0, one_pow, mul_one,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  have h1 := intSer_mul (intSer_aeval hh P hPi) hA n
  have h2 := intSer_mul (intSer_pow hPs N) hB n
  have k2 : (coeff 1 h ^ n - N) * coeff n f =
      coeff n ((P : ℂ_[q]⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : ℂ_[q])‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem subst_C_eq {h : ℂ_[q]⟦X⟧} (hs : HasSubst h) (c : ℂ_[q]) :
    (PowerSeries.subst h (C c : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C c := by
  rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp

theorem constantCoeff_subst_eq {h : ℂ_[q]⟦X⟧} (hh0 : constantCoeff h = 0) (Q : ℂ_[q]⟦X⟧) :
    constantCoeff (PowerSeries.subst h Q : ℂ_[q]⟦X⟧) = constantCoeff Q := by
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  obtain ⟨Q', hQ'⟩ : (X : ℂ_[q]⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
  have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
  conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
  rw [subst_C_eq hs]
  simp [hh0]

theorem exists_fac {f : ℂ_[q]⟦X⟧} (hf : f ≠ 0) :
    ∃ (n : ℕ) (Q : ℂ_[q]⟦X⟧), f = X ^ n * Q ∧ constantCoeff Q ≠ 0 :=
  ⟨f.order.toNat, divXPowOrder f, X_pow_order_mul_divXPowOrder.symm, by
    rw [Ne, constantCoeff_divXPowOrder_eq_zero_iff]; exact hf⟩

theorem const_of_funEq (e : ℂ_[q]⟦X⟧) (m : ℕ) (he0 : constantCoeff e = 0) (he1 : ‖coeff 1 e‖ = 1)
    (hm : ‖(m : ℂ_[q])‖ < 1) (h2 : 2 ≤ m) (ρ : ℂ_[q]⟦X⟧) (hρ : ρ ≠ 0) (h : ρ.subst e = ρ ^ m) :
    ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1 := by
  have hs : HasSubst e := HasSubst.of_constantCoeff_zero' he0
  obtain ⟨e', he'⟩ : (X : ℂ_[q]⟦X⟧) ∣ e := X_dvd_iff.2 he0
  have h'0 : constantCoeff e' = coeff 1 e := by
    rw [he', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have ha : coeff 1 e ≠ 0 := by
    intro h0; rw [h0, norm_zero] at he1; exact zero_ne_one he1
  have hsub : ∀ (n : ℕ) (Q : ℂ_[q]⟦X⟧), (PowerSeries.subst e (X ^ n * Q : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    intro n Q
    rw [subst_mul hs, subst_pow hs, subst_X hs]
    have : e ^ n = X ^ n * e' ^ n := by rw [he', mul_pow]
    rw [this]; ring
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hc : constantCoeff ρ ≠ 0 := by
    obtain ⟨n, Q, rfl, hQ⟩ := exists_fac hρ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hQ
    exfalso
    rw [hsub] at h
    have h3 : e' ^ n * PowerSeries.subst e Q = X ^ n * (Q * Q * (X ^ n * Q) ^ k) := by
      apply mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q])))
      rw [h]; ring
    have h4 := congrArg constantCoeff h3
    rw [map_mul, map_mul, map_pow, map_pow, constantCoeff_X, zero_pow hn.ne', zero_mul, h'0,
      constantCoeff_subst_eq he0] at h4
    exact mul_ne_zero (pow_ne_zero _ ha) hQ h4
  set c := constantCoeff ρ with hcd
  have hc1 : c ^ (k + 1) = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_pow, ← hcd] at h4
    apply mul_left_cancel₀ hc
    rw [mul_one]
    linear_combination -h4
  refine ⟨c, ?_, hc1⟩
  by_contra hne
  obtain ⟨n, Q, hf, hQ⟩ := exists_fac (sub_ne_zero.2 hne)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hQ
    rw [pow_zero, one_mul] at hf
    rw [← hf, map_sub, constantCoeff_C, ← hcd, sub_self]
  have hL : (PowerSeries.subst e ρ : ℂ_[q]⟦X⟧) = C c + X ^ n * (e' ^ n * PowerSeries.subst e Q) := by
    have : ρ = C c + X ^ n * Q := by rw [← hf]; ring
    conv_lhs => rw [this, subst_add hs, hsub, subst_C_eq hs]
  have hR : ρ ^ (k + 2) = C c +
      X ^ n * (Q * (∑ i ∈ Finset.range (k + 2), ρ ^ i * (C c : ℂ_[q]⟦X⟧) ^ (k + 2 - 1 - i))) := by
    have := geom_sum₂_mul ρ (C c : ℂ_[q]⟦X⟧) (k + 2)
    rw [hf] at this
    have h5 : (C c : ℂ_[q]⟦X⟧) ^ (k + 2) = C c := by
      rw [← map_pow, pow_succ, hc1, one_mul]
    rw [h5] at this
    linear_combination -this
  rw [hL, hR] at h
  have h3 := mul_left_cancel₀ (pow_ne_zero n (X_ne_zero (R := ℂ_[q]))) (add_left_cancel h)
  have h4 := congrArg constantCoeff h3
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_mul, map_pow, h'0, constantCoeff_subst_eq he0, map_sum,
    Finset.sum_congr rfl (g := fun _ => (1 : ℂ_[q])), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, mul_comm] at h4
  · have h5 := congrArg norm (mul_left_cancel₀ hQ h4)
    rw [norm_pow, he1, one_pow] at h5
    exact hm.ne' h5
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow, map_pow, constantCoeff_C, ← hcd, ← pow_add, ← hc1]
    congr 1; omega

theorem funEq_unique : ∀ (q : ℕ) [Fact q.Prime] (e : ℂ_[q]⟦X⟧) (m : ℕ), constantCoeff e = 0 → ‖coeff 1 e‖ = 1 → ‖(m : ℂ_[q])‖ < 1 → 2 ≤ m → (∀ ρ : ℂ_[q]⟦X⟧, ρ ≠ 0 → ρ.subst e = ρ ^ m → ∃ c : ℂ_[q], ρ = C c ∧ c ^ (m - 1) = 1) ∧ ∀ g ε : ℂ_[q]⟦X⟧, Bd 1 e → Bd 1 ε → constantCoeff g = 1 → g.subst e = g ^ m * ε → Bd 1 g := by
  intro q _ e m he0 he1 hm h2
  refine ⟨const_of_funEq e m he0 he1 hm h2, fun g ε he hε hg h => ?_⟩
  have hε0 : constantCoeff ε = 1 := by
    have h4 := congrArg constantCoeff h
    rw [constantCoeff_subst_eq he0, map_mul, map_pow, hg, one_pow, one_mul] at h4
    exact h4.symm
  have h1 : Bd 1 (1 : ℂ_[q]⟦X⟧) := by simpa using intSer_C (q := q) (c := 1) (by simp)
  exact intSer_of_funEq g e 1 ε m hg he he0 he1 hm h1 (by simp) hε hε0 (by rw [mul_one, h])

end GlobalTheory.MomOne.FeUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulSeries

variable {q : ℕ} [Fact q.Prime]

def zcHom : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq (a : ℤ_[q]) : zc a = zcHom a := rfl

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.norm_def]

theorem coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
  rw [DT, add_mul, one_mul, map_add (f := _), coeff_derivative]
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp

theorem coeff_one_add_mulS (a : ℤ_[q]) (n : ℕ) :
    coeff n (1 + mulS a : ℂ_[q]⟦X⟧) = zcHom (Ring.choose a n) := by
  cases n with
  | zero => simp [mulS]
  | succ n => simp [mulS, coeff_one, zc_eq]

theorem constantCoeff_mulS (a : ℤ_[q]) : constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 := by
  simp [mulS]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_mulS a)

theorem choose_step (c : ℤ_[q]) (n : ℕ) :
    Ring.choose c (n + 1) * (n + 1) + Ring.choose c n * n = c * Ring.choose c n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h0 : (n.factorial : ℤ_[q]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h1

theorem DT_one_add_mulS (a : ℤ_[q]) :
    DT (1 + mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  ext n
  rw [coeff_DT, coeff_C_mul, coeff_one_add_mulS, coeff_one_add_mulS, zc_eq]
  have := congrArg zcHom (choose_step a n)
  simpa using this

theorem DT_mulS (a : ℤ_[q]) : DT (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  rw [← DT_one_add_mulS]; simp [DT]

theorem ode_unique (c : ℂ_[q]) (h : ℂ_[q]⟦X⟧) {f g : ℂ_[q]⟦X⟧} (hf : DT f = C c * f + h)
    (hg : DT g = C c * g + h) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_DT, map_add (f := _), coeff_C_mul] at h1 h2
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [ih] at h1
    linear_combination h1 - h2

theorem DT_logS : DT (logS : ℂ_[q]⟦X⟧) = 1 := by
  ext n
  rw [coeff_DT]
  cases n with
  | zero => simp [logS]
  | succ n =>
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h4 : ((n : ℂ_[q]) + 1 + 1) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    simp only [logS, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
    push_cast
    field_simp
    ring

theorem DT_subst_mulS (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (f.subst (mulS a : ℂ_[q]⟦X⟧)) = C (zc a) * (DT f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  have hs := hasSubst_mulS a
  have h2 := DT_mulS a
  have h1 : (DT f).subst (mulS a : ℂ_[q]⟦X⟧) =
      (1 + mulS a) * (derivative f).subst (mulS a : ℂ_[q]⟦X⟧) := by
    rw [DT, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, substAlgHom_X]
  rw [h1]
  unfold DT at h2 ⊢
  rw [derivative_subst hs]
  linear_combination ((derivative f).subst (mulS a : ℂ_[q]⟦X⟧)) * h2

theorem constantCoeff_subst_mulS (a : ℤ_[q]) {f : ℂ_[q]⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (f.subst (mulS a : ℂ_[q]⟦X⟧)) = 0 := by
  have hs := hasSubst_mulS a
  obtain ⟨b, rfl⟩ : (X : ℂ_[q]⟦X⟧) ∣ f := X_dvd_iff.2 hf
  rw [← coe_substAlgHom hs, map_mul, substAlgHom_X, map_mul, constantCoeff_mulS, zero_mul]

theorem logS_subst (a : ℤ_[q]) :
    (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS := by
  have hs := hasSubst_mulS a
  have h0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  refine ode_unique 0 (C (zc a)) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_logS, ← coe_substAlgHom hs]; simp
  · have := DT_logS (q := q)
    unfold DT at this ⊢
    rw [Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero, map_zero, zero_mul, zero_add]
    linear_combination (C (zc a)) * this
  · rw [constantCoeff_subst_mulS a h0, map_mul, h0, mul_zero]

theorem mulS_subst (a b : ℤ_[q]) :
    (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b) := by
  have hs := hasSubst_mulS b
  have hz : zc (a * b) = zc a * zc b := by simp [zc_eq]
  refine ode_unique (zc (a * b)) (C (zc (a * b))) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_mulS, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, hz, map_mul]
    have : (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧) (C (zc a)) = C (zc a) :=
      (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧).commutes (zc a)
    rw [this]
    ring
  · rw [DT_mulS]; ring
  · rw [constantCoeff_subst_mulS b (constantCoeff_mulS a), constantCoeff_mulS]

theorem mulS_one : (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X := by
  refine ode_unique 1 1 ?_ ?_ ?_
  · rw [DT_mulS]; simp [zc_eq, add_comm]
  · simp [DT, add_comm]
  · simp [constantCoeff_mulS]

theorem bd_mulS (a : ℤ_[q]) : Bd 1 (mulS a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [mulS, coeff_mk]
  split_ifs
  · simp
  · rw [norm_zc]; exact PadicInt.norm_le_one _

theorem bd_one_pow {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (d : ℕ) : Bd 1 (h ^ d) := by
  induction d with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ d ih =>
    intro n
    rw [pow_succ, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hh _)

theorem bd_subst {f h : ℂ_[q]⟦X⟧} {A : ℝ} (hf : Bd A f) (hh : Bd 1 h) (h0 : constantCoeff h = 0) :
    Bd A (f.subst h) := by
  classical
  intro n
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' h0
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  rw [coeff_subst' hs, finsum_def]
  split_ifs
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hA fun d _ => ?_
    rw [smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (bd_one_pow hh d n)).trans (hf d)
  · simpa using hA

theorem bd_subst_mulS_iff (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ) (ha : ‖a‖ = 1) :
    Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f := by
  refine ⟨fun h => ?_, fun h => bd_subst h (bd_mulS a) (constantCoeff_mulS a)⟩
  obtain ⟨b, hb⟩ := (PadicInt.isUnit_iff.2 ha).exists_right_inv
  have h1 := bd_subst h (bd_mulS b) (constantCoeff_mulS b)
  rwa [subst_comp_subst_apply (hasSubst_mulS a) (hasSubst_mulS b), mulS_subst, hb, mulS_one,
    X_subst] at h1

theorem mulS_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) :=
  fun _ _ => ⟨fun a => ⟨bd_mulS a, constantCoeff_mulS a, by simp [mulS], logS_subst a⟩, mulS_subst,
    mulS_one, bd_subst_mulS_iff, DT_logS, norm_zc⟩

end GlobalTheory.MomOne.MulSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DvdAevalSubAevalTwo
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem dvd_aeval_sub_aeval_two {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (a u w u' w' : A) (hu : a ∣ u - u') (hw : a ∣ w - w') (P : MvPolynomial (Fin 2) K) :
    a ∣ MvPolynomial.aeval ![u, w] P - MvPolynomial.aeval ![u', w'] P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    have := dvd_add hp hr
    simp only [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p i hp =>
    have hi : a ∣ (![u, w] i) - (![u', w'] i) := by
      fin_cases i
      · simpa using hu
      · simpa using hw
    have := dvd_add (hp.mul_right (![u, w] i)) (hi.mul_left (MvPolynomial.aeval ![u', w'] p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem X_pow_succ_dvd_of_DT {q : ℕ} [Fact q.Prime] (f : ℂ_[q]⟦X⟧) (n : ℕ)
    (h0 : constantCoeff f = 0) (hD : (X : ℂ_[q]⟦X⟧) ^ n ∣ DT f) :
    (X : ℂ_[q]⟦X⟧) ^ (n + 1) ∣ f := by
  have hu : IsUnit (1 + X : ℂ_[q]⟦X⟧) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]; simp
  unfold DT at hD
  rw [hu.dvd_mul_left, X_pow_dvd_iff] at hD
  rw [X_pow_dvd_iff]
  intro m hm
  cases m with
  | zero => simpa using h0
  | succ k =>
    have := hD k (by omega)
    rw [coeff_derivative] at this
    have hk : ((k : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    exact (mul_eq_zero.mp this).resolve_right hk

theorem ode_unique : ∀ (q : ℕ) [Fact q.Prime] (P₁ P₂ : MvPolynomial (Fin 2) ℂ_[q]) (u w u' w' : ℂ_[q]⟦X⟧), DT u = MvPolynomial.aeval ![u, w] P₁ → DT w = MvPolynomial.aeval ![u, w] P₂ → DT u' = MvPolynomial.aeval ![u', w'] P₁ → DT w' = MvPolynomial.aeval ![u', w'] P₂ → constantCoeff u = constantCoeff u' → constantCoeff w = constantCoeff w' → u = u' ∧ w = w' := by
  intro q _ P₁ P₂ u w u' w' h1 h2 h3 h4 hu hw
  have hsub : ∀ f g : ℂ_[q]⟦X⟧, DT (f - g) = DT f - DT g := by
    intro f g
    unfold DT
    rw [map_sub, mul_sub]
  have key : ∀ n : ℕ, (X : ℂ_[q]⟦X⟧) ^ n ∣ u - u' ∧ (X : ℂ_[q]⟦X⟧) ^ n ∣ w - w' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      constructor
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hu, sub_self]
        · rw [hsub, h1, h3]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
      · apply X_pow_succ_dvd_of_DT
        · rw [map_sub, hw, sub_self]
        · rw [hsub, h2, h4]; exact dvd_aeval_sub_aeval_two _ _ _ _ _ ih.1 ih.2 _
  constructor
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).1 n (by omega)
  · rw [← sub_eq_zero]
    ext n
    simpa using X_pow_dvd_iff.mp (key (n + 1)).2 n (by omega)

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacterStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_poly_of_character' : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K), Function.Injective x → (∀ i j, χ (i + j) = χ i * χ j) → (∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  first | exact @GlobalTheory.ConvSer.exists_integral_poly_of_character | exact GlobalTheory.ConvSer.exists_integral_poly_of_character | (intros; apply GlobalTheory.ConvSer.exists_integral_poly_of_character <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLoweringStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  first | exact @GlobalTheory.WigSh.inv_sq_le_wM | exact GlobalTheory.WigSh.inv_sq_le_wM | (intros; apply GlobalTheory.WigSh.inv_sq_le_wM <;> assumption)
end

