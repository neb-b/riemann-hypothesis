module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonSubExpMemHodgeFiltration
section
noncomputable section

namespace GlobalTheory.ExpImage.TaylorEps

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open Polynomial
open scoped Formalism.Per

section poly
variable (K : Type) [Field K] [CharZero K]

def logT (M : ℕ) : K[X] := ∑ k ∈ Finset.range M, C ((-1) ^ k * ((k + 1 : ℕ) : K)⁻¹) * X ^ (k + 1)

theorem logT_deriv (M : ℕ) : (1 + X) * derivative (logT K M) = 1 - (-X) ^ M := by
  induction M with
  | zero => simp [logT]
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have e : derivative (C ((-1) ^ M * ((M + 1 : ℕ) : K)⁻¹) * X ^ (M + 1) : K[X]) = (-X) ^ M := by
      rw [derivative_C_mul, derivative_X_pow, ← mul_assoc, ← C_mul, mul_assoc, inv_mul_cancel₀ h,
        mul_one, neg_pow (X : K[X])]
      simp
    rw [logT, Finset.sum_range_succ, derivative_add, e, mul_add, ← logT, ih]
    ring

theorem X_dvd_logT (M : ℕ) : X ∣ logT K M :=
  Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (dvd_pow_self _ k.succ_ne_zero) _

theorem expT_deriv (L : K[X]) (M : ℕ) :
    derivative (∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j) =
      derivative L * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h : ((M + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast M.succ_ne_zero
    have h' : ((M.factorial : ℕ) : K) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
    have e : (((M + 1).factorial : ℕ) : K)⁻¹ * ((M + 1 : ℕ) : K) = ((M.factorial : ℕ) : K)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp
    rw [Finset.sum_range_succ, derivative_add, ih, Finset.sum_range_succ _ M, derivative_C_mul,
      derivative_pow, ← e, C_mul]
    simp only [Nat.add_sub_cancel]
    ring

theorem exp_log_dvd (M : ℕ) :
    X ^ M ∣ 1 + X - ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * logT K M ^ j := by
  rcases M with _ | M
  · simp
  set L := logT K (M + 1) with hL
  set D := 1 + X - ∑ j ∈ Finset.range (M + 1), C ((j.factorial : K)⁻¹) * L ^ j with hD
  have h1 : X ^ M ∣ X * derivative D + derivative D - D := by
    have e : X * derivative D + derivative D - D = C ((M.factorial : K)⁻¹) * L ^ M +
        (-X) ^ (M + 1) * ∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j := by
      have := logT_deriv K (M + 1)
      rw [← hL] at this
      rw [hD, derivative_sub, expT_deriv, Finset.sum_range_succ]
      simp only [derivative_add, derivative_one, derivative_X]
      linear_combination (-∑ j ∈ Finset.range M, C ((j.factorial : K)⁻¹) * L ^ j) * this
    rw [e]
    refine dvd_add (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (X_dvd_logT K _) M) _)
      (Dvd.dvd.mul_right ?_ _)
    rw [neg_pow, pow_succ X]
    exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
  have h0 : D.coeff 0 = 0 := by
    have hL0 : L.eval 0 = 0 := by
      rw [← coeff_zero_eq_eval_zero]; exact X_dvd_iff.1 (X_dvd_logT K _)
    rw [coeff_zero_eq_eval_zero, hD, Finset.sum_range_succ']
    simp [Polynomial.eval_finsetSum, hL0]
  rw [X_pow_dvd_iff] at h1 ⊢
  intro d
  induction d with
  | zero => exact fun _ => h0
  | succ d ih =>
    intro hd
    have a := ih (by omega)
    have b := h1 d (by omega)
    have c : (X * derivative D).coeff d = 0 := by
      rcases d with _ | d
      · simp
      · rw [coeff_X_mul, coeff_derivative, a, zero_mul]
    rw [coeff_sub, coeff_add, c, a, coeff_derivative, zero_add, sub_zero] at b
    exact (mul_eq_zero.1 b).resolve_right (by exact_mod_cast d.succ_ne_zero)

end poly

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem aeval_mem {x : P.R.BdR} (hx : x ∈ FilB P 0) (f : ℚ_[l][X]) : aeval x f ∈ FilB P 0 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial]
    exact qB_mul_mem a (by simpa using FilB_pow hx n)

theorem io_eq (T : LocTied l P AI) (a : Ainf l) :
    T.eD (io AI a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := GlobalTheory.ThetaTie.eD_ιA T a

theorem mu_mem (T : LocTied l P AI) : io AI (mu AI.ε) ∈ FilB P 1 := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : io AI (mu AI.ε) - tD P ∈ FilB P ((2 : ℕ) : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T 2 _).2 ⟨_, GlobalTheory.ThetaTie.log_mu (GlobalTheory.ThetaTie.isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, io_eq]
  have := add_mem (FilB_anti (a := 1) (by norm_num) h) (tD_mem (P := P))
  simpa using this

theorem t_sub_log (T : LocTied l P AI) (M : ℕ) :
    tD P - aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) ∈ FilB P (M : ℤ) := by
  obtain ⟨y, hy, e⟩ := T.t
  have h : (M.factorial : P.R.BdR) * tD P - ∑ k ∈ Finset.range M,
      (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : P.R.BdR) * io AI (mu AI.ε) ^ (k + 1) ∈
        FilB P (M : ℤ) := by
    refine (GlobalTheory.ThetaTie.fil_nat T M _).2 ⟨(M.factorial : Per.BdRp l) * y -
      algebraMap (Per.AinfP l) (Per.BdRp l) (∑ k ∈ Finset.range M,
        (-1) ^ k * ((M.factorial / (k + 1) : ℕ) : Per.AinfP l) *
          (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm AI.ε - 1)) ^ (k + 1)), ?_, ?_⟩
    · refine (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l M _).2 ?_
      rw [map_sub, GlobalTheory.ThetaTie.ev_alg, map_mul, map_natCast,
        GlobalTheory.CrisIncl.factorial_mul_ev l _ y (GlobalTheory.ThetaTie.isEps AI).1 hy M, sub_self]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sub, map_mul, map_natCast, map_sum, map_pow, map_neg, e, io_eq]
        simp only [map_one]
        simp only [aDp, mu, RingHom.comp_apply, map_sub, map_one]
  have h0 : ((M.factorial : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast M.factorial_ne_zero
  have := qB_mul_mem ((M.factorial : ℕ) : ℚ_[l])⁻¹ h
  convert this using 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_sub, ← mul_assoc, ← map_natCast (qB P), ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul,
    logT, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k + 1 ∣ M.factorial := Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk)
  have h1 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have e1 : ((k + 1 : ℕ) : ℚ_[l])⁻¹ =
      ((M.factorial : ℕ) : ℚ_[l])⁻¹ * ((M.factorial / (k + 1) : ℕ) : ℚ_[l]) := by
    rw [Nat.cast_div hk' h1]
    field_simp
  rw [map_mul, aeval_C, map_pow, aeval_X, e1]
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

theorem eps_sub_exp (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (M : ℕ) : io AI (WittVector.teichmuller l AI.ε) -
      ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hm := mu_mem T
  have hm0 := FilB_anti (a := 0) (by norm_num) hm
  have hL := aeval_mem hm0 (logT ℚ_[l] M)
  have ht := FilB_anti (a := 0) (by norm_num) (tD_mem (P := P))
  have hd := t_sub_log T M
  obtain ⟨Q, hQ⟩ := exp_log_dvd ℚ_[l] M
  have h1 := congrArg (aeval (io AI (mu AI.ε))) hQ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_add (f := _), map_one, aeval_X, map_sum, map_mul, aeval_C, map_pow] at h1
  have h2 := FilB_zero_mul (aeval_mem hm0 Q) (FilB_pow hm M)
  rw [mul_one, mul_comm, ← h1] at h2
  generalize aeval (io AI (mu AI.ε)) (logT ℚ_[l] M) = L at hL hd h2
  have h3 : ∀ j : ℕ, tD P ^ j - L ^ j ∈ FilB P (M : ℤ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have := add_mem (FilB_zero_mul ht ih)
        (FilB_zero_mul (x := L ^ j) (by simpa using FilB_pow hL j) hd)
      convert this using 1
      ring
  have h4 := Submodule.sum_mem (FilB P (M : ℤ)) (t := Finset.range M)
    fun j _ => qB_mul_mem ((j.factorial : ℚ_[l])⁻¹) (h3 j)
  have e : io AI (WittVector.teichmuller l AI.ε) = 1 + io AI (mu AI.ε) := by
    rw [mu, map_sub, map_one, add_sub_cancel]
  have := sub_mem h2 h4
  rw [e]
  convert this using 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.ExpImage.TaylorEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLaws
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Laws

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem sh_laws : ∀ (l : ℕ) [Fact l.Prime], sh (1 : Fl l) = 1 ∧ sh (0 : Fl l) = 0 ∧
    (∀ x y : Fl l, sh (x * y) = sh x * sh y) ∧ (∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n) ∧
    (∀ x : Fl l, ‖sh x‖ ≤ 1) ∧ (∀ c : ℂ_[l], ‖c‖ ≤ 1 → ∃ x : Fl l, sh x = c) ∧
    (∀ x y : Fl l, ‖sh (x + y) - sh x - sh y‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ x : Fl l, ‖sh (-x)‖ = ‖sh x‖) := by
  intro l _
  have hmul : ∀ x y : Fl l, sh (x * y) = sh x * sh y := fun x y => by
    simp only [sh, map_mul]; rfl
  have hpow : ∀ (x : Fl l) (n : ℕ), sh (x ^ n) = sh x ^ n := fun x n => by
    simp only [sh, map_pow]; norm_cast
  refine ⟨by simp [sh], by simp [sh, untilt_zero], hmul, hpow, fun x => (GlobalTheory.RingBasics.mem_OC _).1 (x.untilt).2,
    fun c hc => ?_, fun x y => ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l ⟨c, (GlobalTheory.RingBasics.mem_OC c).2 hc⟩
    exact ⟨x, by simp [sh, hx]⟩
  · have hm : (x + y).untilt - x.untilt - y.untilt ∈ Ideal.span {(l : OC l)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
        PreTilt.mk_untilt_eq_coeff_zero, PreTilt.mk_untilt_eq_coeff_zero, map_add]
      ring
    have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 _).1 (by rw [pow_one]; exact hm)
    simpa [sh] using this
  · have h2 : sh (-x) ^ 2 = sh x ^ 2 := by rw [← hpow, ← hpow, neg_sq]
    have h3 : ‖sh (-x)‖ ^ 2 = ‖sh x‖ ^ 2 := by rw [← norm_pow, ← norm_pow, h2]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h3

end GlobalTheory.PSer.Laws
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl

namespace GlobalTheory.HWL.TensorWitt

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W]

private theorem crd_tmul_lemma (i : I) (o : O) (v : W) :
    crd b i (o ⊗ₜ[Z] v) = b.coord i o • v := by
  simp only [crd, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lsmul_apply]

private theorem crd_mul_lemma_2 (i : I) (c : W) (y : O ⊗[Z] W) :
    crd b i ((1 : O) ⊗ₜ[Z] c * y) = c * crd b i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma]
    exact (mul_smul_comm _ _ _).symm
  | add y z hy hz => rw [mul_add, map_add (f := _), map_add (f := _), hy, hz, mul_add]

private theorem sum_basis_tmul_crd_eq (y : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    simp_rw [crd_tmul_lemma, Module.Basis.coord_apply, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add y z hy hz =>
    simp_rw [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 (j : I) (v : I → W) : crd b j (∑ i, b i ⊗ₜ[Z] v i) = v j := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, crd_tmul_lemma, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mem_pow_iff (w : W) (n : ℕ) (x : O ⊗[Z] W) :
    x ∈ Ideal.span {((1 : O) ⊗ₜ[Z] w) ^ n} ↔ ∀ i, crd b i x ∈ Ideal.span {w ^ n} := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Ideal.mem_span_singleton]
  simp_rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨crd b i y, crd_mul_lemma_2 b i _ y⟩
  · intro h
    choose c hc using h
    refine ⟨∑ i, b i ⊗ₜ[Z] c i, ?_⟩
    conv_lhs => rw [← sum_basis_tmul_crd_eq b x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Algebra.TensorProduct.tmul_mul_tmul, one_mul]


include b in
theorem complete_tensor (w : W) [h : IsAdicComplete (Ideal.span {w}) W] :
    IsAdicComplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
  have key : ∀ (n : ℕ) (x : O ⊗[Z] W),
      x ∈ (Ideal.span {(1 : O) ⊗ₜ[Z] w} ^ n • ⊤ : Submodule (O ⊗[Z] W) (O ⊗[Z] W)) ↔
        ∀ i, crd b i x ∈ (Ideal.span {w} ^ n • ⊤ : Submodule W W) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact mem_pow_iff b w n x
  have H1 : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun x hx => ?_⟩
    have hi : ∀ i, crd b i x = 0 := fun i =>
      IsHausdorff.haus h.toIsHausdorff _ fun n => by
        rw [SModEq.sub_mem, sub_zero]
        exact (key n x).1 (by simpa [SModEq.sub_mem] using hx n) i
    rw [← sum_basis_tmul_crd_eq b x]
    simp [hi]
  have H2 : IsPrecomplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun f hf => ?_⟩
    have hfi : ∀ i, ∃ L : W, ∀ n,
        crd b i (f n) ≡ L [SMOD (Ideal.span {w} ^ n • ⊤ : Submodule W W)] := fun i =>
      IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (key m _).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hfi
    refine ⟨∑ i, b i ⊗ₜ[Z] L i, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    rw [map_sub, crd_sum_lemma_4]
    exact SModEq.sub_mem.1 (hL i n)
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

end Coord

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) := by
  unfold inclW
  exact WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem tiltWitt_eq_zero_of_prime_mul_eq_zero (x : WCb l) (h : ((l : ℕ) : WCb l) * x = 0) : x = 0 := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  ext n
  have h1 := WittVector.mul_charP_coeff_succ (p := l) x n
  rw [mul_comm, h, WittVector.zero_coeff] at h1
  rw [WittVector.zero_coeff]
  exact (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero).1 h1.symm

theorem ainf_saturated_in_tiltWitt_prime (a : Loc.Ainf l) (w : WCb l) (h : inclW l a = ((l : ℕ) : WCb l) * w) :
    ∃ a', inclW l a' = w := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  refine ⟨WittVector.mk l fun n => (frobeniusEquiv (OCb l) l).symm (a.coeff (n + 1)), ?_⟩
  ext n
  have h1 := congrArg (fun z : WCb l => z.coeff (n + 1)) h
  simp only [inclW, WittVector.map_coeff] at h1
  rw [mul_comm, WittVector.mul_charP_coeff_succ] at h1
  apply frobenius_inj (Cb l) l
  simp only [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  rw [← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, h1, frobenius_def]

theorem not_isUnit_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    ¬ IsUnit (WittVector.teichmuller l e - 1 : Loc.Ainf l) := by
  intro hu
  apply he
  have h1 := hu.map (WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l)
  rwa [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h1

private theorem crd_tensorProduct_map_eq {Z O I W W' : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']
    (f : W →ₐ[Z] W') (i : I) (y : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f y) = f (crd b i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, crd_tmul_lemma, crd_tmul_lemma, map_smul]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]

private theorem tensor_eq_of_crd_eq {Z O I W : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] {y y' : O ⊗[Z] W}
    (h : ∀ i, crd b i y = crd b i y') : y = y' := by
  rw [← sum_basis_tmul_crd_eq b y, ← sum_basis_tmul_crd_eq b y']
  simp_rw [h]

private theorem exists_basis_padicInt_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    ∃ (I : Type) (_ : Fintype I), Nonempty (Module.Basis I ℤ_[l] ↥(OL LL)) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := .of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    refine h.imp (fun h => ?_) id
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h
  haveI : Module.Free ℤ_[l] ↥(OL LL) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  exact ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ_[l] ↥(OL LL)⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (Ideal.span {((l : ℕ) : RW LL)}) (RW LL) ∧
    (∀ x : RW LL, ((l : ℕ) : RW LL) * x = 0 → x = 0) ∧ Function.Injective (inclR LL) ∧
    (∀ (y : RA LL) (x : RW LL), inclR LL y = ((l : ℕ) : RW LL) * x → ∃ y', inclR LL y' = x) ∧
    ∀ e : OCb l, ¬ IsUnit (e - 1) →
      IsAdicComplete (Ideal.span {(1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)})
        (RA LL) := by
  intro l _ LL
  obtain ⟨I, _, ⟨b⟩⟩ := exists_basis_padicInt_OL l LL
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hl' : ∀ i (x : RW LL), crd b i (((l : ℕ) : RW LL) * x) = ((l : ℕ) : WCb l) * crd b i x := by
    intro i x
    rw [hl]
    exact crd_mul_lemma_2 b i _ x
  have hinc : ∀ (y : RA LL) i, crd b i (inclR LL y) = inclW l (crd b i y) := fun y i =>
    crd_tensorProduct_map_eq b (inclWA l) i y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    haveI : IsAdicComplete (Ideal.span {((l : ℕ) : WCb l)}) (WCb l) :=
      (GlobalTheory.Per.AinfComplete.witt_complete (p := l) (R := Cb l) ((l : ℕ) : WCb l)
        (fun c => ⟨c, fun n => by simp⟩)
        (fun x hx => by simpa using hx 1)).2
    exact complete_tensor b _
  · intro x hx
    refine tensor_eq_of_crd_eq b fun i => ?_
    rw [map_zero]
    exact tiltWitt_eq_zero_of_prime_mul_eq_zero _ (by rw [← hl', hx, map_zero])
  · intro y y' h
    exact tensor_eq_of_crd_eq b fun i => inclW_injective (by rw [← hinc, ← hinc, h])
  · intro y x hyx
    have hi : ∀ i, ∃ a' : Loc.Ainf l, inclW l a' = crd b i x := fun i =>
      ainf_saturated_in_tiltWitt_prime (crd b i y) (crd b i x)
        ((hinc y i).symm.trans ((congrArg (crd b i) hyx).trans (hl' i x)))
    choose a' ha' using hi
    refine ⟨∑ i, b i ⊗ₜ[ℤ_[l]] a' i, tensor_eq_of_crd_eq b fun i => ?_⟩
    exact (hinc _ i).trans ((congrArg (inclW l) (crd_sum_lemma_4 b i a')).trans (ha' i))
  · intro e he
    haveI : IsAdicComplete (Ideal.span {(WittVector.teichmuller l e - 1 : Ainf l)}) (Ainf l) :=
      (GlobalTheory.Per.AinfComplete.main l _ (not_isUnit_teich e he)).2
    exact complete_tensor b _

end GlobalTheory.HWL.TensorWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmPowDvd
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem tm_pow_dvd : ∀ (l : ℕ) [Fact l.Prime] (x : Fl l), ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ →
    (l : Acris l) ∣ algebraMap (Ainf l) (Acris l) (tm x) ^ l := by
  intro l _ x hx
  have hmem : x.untilt ∈ (Ideal.span {(l : OC l)}) ^ 1 := by
    rw [GlobalTheory.RingBasics.mem_span_pow_OC, pow_one]
    exact hx
  rw [pow_one] at hmem
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨z, hz⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l c
  have hk := GlobalTheory.MemLoc.FundOnto.dvd_pow_of_ker l (tm x - (l : Ainf l) * tm z) (by
    rw [map_sub, map_mul, map_natCast, GlobalTheory.MemLoc.FundOnto.theta_tm,
      GlobalTheory.MemLoc.FundOnto.theta_tm, hz, ← hc, mul_comm, sub_self])
  rw [map_sub, map_mul, map_natCast] at hk
  generalize algebraMap (Ainf l) (Acris l) (tm x) = X at hk ⊢
  generalize algebraMap (Ainf l) (Acris l) (tm z) = Z at hk
  have h1 : ((l : ℕ) : Acris l) ∣ X - (X - (l : Acris l) * Z) := ⟨Z, by ring⟩
  have h2 := h1.trans (sub_dvd_pow_sub_pow _ _ l)
  have := dvd_add h2 hk
  simpa using this

end GlobalTheory.PSer
end

