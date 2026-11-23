module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.ExistsFactorialMulEqPow
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.MapEqPadicPowCyclotomicCharacter

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.CrisTheta
section
noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)]

namespace AinfInv

theorem isUnit_factorial (n : ℕ) : IsUnit (n ! : AinfInv p R) :=
  IsUnit.natCast_factorial_of_algebra ℚ n


@[simp] theorem gamma_zero (x : AinfInv p R) : gamma 0 x = 1 := by simp [gamma]

@[simp] theorem gamma_one (x : AinfInv p R) : gamma 1 x = x := by simp [gamma]

end AinfInv

variable [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

theorem AinfInv.theta_gamma {n : ℕ} (hn : n ≠ 0) {x : AinfInv p R} (hx : AinfInv.theta p R x = 0) :
    AinfInv.theta p R (AinfInv.gamma n x) = 0 := by
  have h := congrArg (AinfInv.theta p R) (AinfInv.factorial_mul_gamma n x)
  rw [map_mul, map_pow, hx, zero_pow hn] at h
  exact (((AinfInv.isUnit_factorial n).map (AinfInv.theta p R)).mul_right_eq_zero).1 h

namespace AcrisZero


variable (p R) in
def pdIdeal : Ideal (AcrisZero p R) :=
  span {y | ∃ (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0), n ≠ 0 ∧ y = gamma n x hx}

theorem gamma_mem_pdIdeal {n : ℕ} (hn : n ≠ 0) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    gamma n x hx ∈ pdIdeal p R := subset_span ⟨n, x, hx, hn, rfl⟩

theorem algebraMap_mem_pdIdeal (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    algebraMap _ _ x ∈ pdIdeal p R := by
  have : algebraMap _ _ x = gamma 1 x hx := Subtype.ext (AinfInv.gamma_one _).symm
  rw [this]
  exact gamma_mem_pdIdeal one_ne_zero x hx

theorem exists_sub_mem_pdIdeal (y : AcrisZero p R) :
    ∃ a : Ainf p R, y - algebraMap _ _ a ∈ pdIdeal p R := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, rfl⟩ := hy
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨1, ?_⟩
      convert (pdIdeal p R).zero_mem
      rw [sub_eq_zero, map_one]
      exact Subtype.ext (AinfInv.gamma_zero _)
    · exact ⟨0, by rw [map_zero, sub_zero]; exact gamma_mem_pdIdeal hn x hx⟩
  | algebraMap r =>
    refine ⟨r, ?_⟩
    convert (pdIdeal p R).zero_mem
    rw [sub_eq_zero]
    rfl
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    convert add_mem ha hb using 1
    change (⟨x, hx'⟩ + ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_add (f := _)]; ring
  | mul x y hx' hy' hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    convert add_mem (Ideal.mul_mem_right ⟨y, hy'⟩ _ ha)
      (Ideal.mul_mem_left _ (algebraMap _ _ a) hb) using 1
    change (⟨x, hx'⟩ * ⟨y, hy'⟩ : AcrisZero p R) - _ = _
    rw [map_mul]; ring

theorem theta_eq_zero_of_mem_pdIdeal {y : AcrisZero p R} (hy : y ∈ pdIdeal p R) :
    AinfInv.theta p R y = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, x, hx, hn, rfl⟩ := hy
    exact AinfInv.theta_gamma hn (by rw [AinfInv.theta_algebraMap, hx, map_zero])
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [AddMemClass.coe_add, map_add (f := _), hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, MulMemClass.coe_mul, map_mul, hx, mul_zero]

theorem exists_theta_eq (y : AcrisZero p R) :
    ∃ r : R, algebraMap R (Localization.Away (p : R)) r = AinfInv.theta p R y := by
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h := theta_eq_zero_of_mem_pdIdeal ha
  rw [AddSubgroupClass.coe_sub, map_sub, sub_eq_zero, Subalgebra.coe_algebraMap,
    AinfInv.theta_algebraMap] at h
  exact ⟨_, h.symm⟩

end AcrisZero

variable [IsDomain R] [CharZero R] [IsDomain S] [CharZero S]

omit [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R] in
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (p : R))) :=
  IsLocalization.injective (M := Submonoid.powers (p : R)) _
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))

namespace AcrisZero


variable (p R) in
def theta : AcrisZero p R →+* R where
  toFun y := (exists_theta_eq y).choose
  map_one' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_mul' x y := algebraMap_away_injective (p := p) (by
    rw [map_mul, (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)
  map_zero' := algebraMap_away_injective (p := p) (by
    rw [(exists_theta_eq _).choose_spec]; simp)
  map_add' x y := algebraMap_away_injective (p := p) (by
    rw [map_add (f := _), (exists_theta_eq _).choose_spec, (exists_theta_eq _).choose_spec,
      (exists_theta_eq _).choose_spec]; simp)

theorem algebraMap_theta (y : AcrisZero p R) :
    algebraMap R (Localization.Away (p : R)) (theta p R y) = AinfInv.theta p R y :=
  (exists_theta_eq y).choose_spec

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x :=
  algebraMap_away_injective (p := p) (by
    rw [algebraMap_theta, Subalgebra.coe_algebraMap, AinfInv.theta_algebraMap])

theorem theta_eq_zero_iff (y : AcrisZero p R) : theta p R y = 0 ↔ y ∈ pdIdeal p R := by
  have key : ∀ y ∈ pdIdeal p R, theta p R y = 0 := fun y hy =>
    algebraMap_away_injective (p := p) (by
      rw [algebraMap_theta, theta_eq_zero_of_mem_pdIdeal hy, map_zero])
  refine ⟨fun h => ?_, key y⟩
  obtain ⟨a, ha⟩ := exists_sub_mem_pdIdeal y
  have h1 := key _ ha
  rw [RingHom.map_sub, h, theta_algebraMap, zero_sub, neg_eq_zero] at h1
  simpa using add_mem ha (algebraMap_mem_pdIdeal a h1)

end AcrisZero

namespace Acris


variable (p R) in
def theta : Acris p R →+* R :=
  (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm.toRingHom.comp
    (adicMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _))

@[simp] theorem theta_algebraMap_zero (a : AcrisZero p R) :
    theta p R (algebraMap _ _ a) = AcrisZero.theta p R a := by
  have h := adicMap_algebraMap _ _ (AcrisZero.theta p R) (span_natCast_le_comap p _) a
  refine (congrArg (AdicCompletion.ofAlgEquiv (span {(p : R)})).symm h).trans ?_
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = Ainf.theta p R x := by
  rw [IsScalarTower.algebraMap_apply (Ainf p R) (AcrisZero p R) (Acris p R), theta_algebraMap_zero,
    AcrisZero.theta_algebraMap]



end Acris

namespace BcrisPlus


variable (p R) in
def theta : BcrisPlus p R →+* Localization.Away (p : R) :=
  lift ((algebraMap R _).comp (Acris.theta p R))
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : R)) (p : R))

@[simp] theorem theta_algebraMap (x : Acris p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Acris.theta p R x) := lift_algebraMap _ _ x

end BcrisPlus

end Reformulated.AutPerF
end
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.DeRhamLog
section
noncomputable section

open Ideal Polynomial

namespace Reformulated.AutPerF

universe u v

section Trunc

variable {B : Type*} [CommRing B] [Algebra ℚ B]

theorem truncLog_zero (N : ℕ) : truncLog N (0 : B) = 0 := by simp [truncLog]

theorem derivative_truncLog_mul (N : ℕ) (z : B[X]) (hz : z ^ N = 0) :
    derivative (truncLog N z) * (1 + z) = derivative z := by
  have h1 : derivative (truncLog N z) = derivative z * ∑ k ∈ Finset.range N, (-z) ^ k := by
    rw [truncLog, derivative_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_smul, derivative_pow_succ, neg_pow z]
    have e : (C ((k : B) + 1) : B[X]) = algebraMap ℚ B[X] (k + 1) := by simp
    have e2 : ((-1 : B[X])) ^ k = algebraMap ℚ B[X] ((-1) ^ k) := by simp
    rw [e, e2, Algebra.smul_def, ← mul_assoc, ← mul_assoc, ← map_mul,
      div_mul_cancel₀ _ (by positivity)]
    ring
  have h2 := geom_sum_mul_neg (-z) N
  rw [neg_pow z N, hz, mul_zero, sub_zero, sub_neg_eq_add] at h2
  rw [h1, mul_assoc, h2, mul_one]

theorem truncLog_add {n : ℕ} {x y : B} (hx : x ^ n = 0) (hy : y ^ n = 0)
    (hxy : (x + y + x * y) ^ n = 0) :
    truncLog n (x + y + x * y) = truncLog n x + truncLog n y := by
  have hX : IsNilpotent (C x * X : B[X]) := ⟨n, by rw [mul_pow, ← C_pow, hx, C_0, zero_mul]⟩
  have hY : IsNilpotent (C y : B[X]) := ⟨n, by rw [← C_pow, hy, C_0]⟩
  obtain ⟨M, hM⟩ : IsNilpotent (C x * X + C y + C x * X * C y : B[X]) :=
    (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add hX hY)
      ((Commute.all _ _).isNilpotent_mul_left hY)
  set N := max M n
  have hM' := pow_eq_zero_of_le (le_max_left M n) hM
  have hX' : (C x * X : B[X]) ^ N = 0 := by
    rw [mul_pow, ← C_pow, pow_eq_zero_of_le (le_max_right M n) hx, C_0, zero_mul]
  have d1 := derivative_truncLog_mul N _ hM'
  have d2 := derivative_truncLog_mul N _ hX'
  have hu : IsUnit (1 + (C x * X + C y + C x * X * C y) : B[X]) :=
    IsNilpotent.isUnit_one_add ⟨M, hM⟩
  have hD : derivative (truncLog N (C x * X + C y + C x * X * C y) - truncLog N (C x * X)) = 0 := by
    refine hu.mul_right_cancel ?_
    rw [derivative_sub, sub_mul, d1, zero_mul,
      show (1 + (C x * X + C y + C x * X * C y) : B[X]) = (1 + C x * X) * (1 + C y) by ring,
      ← mul_assoc, d2]
    simp
    ring
  haveI : HasUniqueDiv B := HasUniqueDiv.of_module_rat B
  have hC := eq_C_of_derivative_eq_zero hD
  have e1 := congrArg (evalRingHom 1) hC
  have e0 := congrArg (evalRingHom 0) hC
  rw [map_sub, map_truncLog, map_truncLog] at e0 e1
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_X, mul_one, mul_zero, zero_add,
    zero_mul, add_zero, truncLog_zero, sub_zero] at e0 e1
  rw [← truncLog_eq_of_pow_eq_zero hx (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hy (le_max_right M n),
    ← truncLog_eq_of_pow_eq_zero hxy (le_max_right M n), e0, ← e1]
  ring

end Trunc

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]

namespace BdRPlus

theorem eval_pow_eq_zero {x : BdRPlus p R} (hx : theta p R x = 0) (n : ℕ) :
    eval p R n x ^ n = 0 := evalₐ_pow_eq_zero _ ((theta_eq_zero_iff x).1 hx) n

theorem log_congr {u v : BdRPlus p R} (h : u = v) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log u hu = log v hv := by subst h; rfl

theorem log_mul (u v : BdRPlus p R) (hu : theta p R u = 1) (hv : theta p R v = 1) :
    log (u * v) (by rw [map_mul, hu, hv, one_mul]) = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  have e : eval p R n (u * v - 1) =
      eval p R n (u - 1) + eval p R n (v - 1) + eval p R n (u - 1) * eval p R n (v - 1) := by
    rw [← map_mul, ← map_add (f := _), ← map_add (f := _)]; congr 1; ring
  rw [map_add (f := _), eval_log, eval_log, eval_log, e]
  refine truncLog_add (eval_pow_eq_zero (by simp [hu]) n) (eval_pow_eq_zero (by simp [hv]) n) ?_
  rw [← e]
  exact eval_pow_eq_zero (by simp [hu, hv]) n

theorem eval_two_log (u : BdRPlus p R) (hu : theta p R u = 1) :
    eval p R 2 (log u hu) = eval p R 2 (u - 1) := by
  rw [eval_log, truncLog, Finset.sum_range_succ, Finset.sum_range_one,
    eval_pow_eq_zero (x := u - 1) (by simp [hu]) 2]
  simp

def logTeich (η : tateModule p R) : BdRPlus p R :=
  log (algebraMap (Ainf p R) _ (Ainf.teich p η.1)) (by
    rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap,
      Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, map_one])

theorem p_mul_inv : (p : BdRPlus p R) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]

def teichDivP (ϖ : PFlat p R) : BdRPlus p R :=
  algebraMap (Ainf p R) _ (Ainf.teich p ϖ.1) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹

theorem theta_teichDivP (ϖ : PFlat p R) : theta p R (teichDivP ϖ) = 1 := by
  rw [teichDivP, map_mul, IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap,
    AinfInv.theta_algebraMap, Ainf.theta_teich, ϖ.2, map_natCast, ← map_natCast (theta p R),
    ← map_mul, p_mul_inv, map_one]

def logFlat (ϖ : PFlat p R) : BdRPlus p R := log (teichDivP ϖ) (theta_teichDivP ϖ)

theorem logFlat_twist (η : tateModule p R) (ϖ : PFlat p R) :
    logFlat (ϖ.twist η) = logTeich η + logFlat ϖ := by
  rw [logFlat, logFlat, logTeich, ← log_mul]
  exact log_congr (by simp [teichDivP, PFlat.twist, mul_assoc]) _ _

end BdRPlus

end Reformulated.AutPerF
end
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Period
section
noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v

section Poly

variable {A : Type u} [CommRing A]

theorem eq_C_of_derivative_eq_zero (h : ∀ n : ℕ, IsUnit ((n : A) + 1)) {f : Polynomial A}
    (hf : Polynomial.derivative f = 0) : f = Polynomial.C (f.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · have h1 := Polynomial.coeff_derivative f n
    rw [hf, Polynomial.coeff_zero] at h1
    rw [Polynomial.coeff_C_succ]
    exact (h n).mul_left_eq_zero.1 h1.symm

end Poly

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

open tateModule

theorem Acris.logTeich_padicPow (η : tateModule p R) (a : ℤ_[p]) :
    Acris.logTeich (padicPow η a) = algebraMap ℤ_[p] (Acris p R) a * Acris.logTeich η := by
  rw [← sub_eq_zero]
  refine Acris.eq_zero_of_forall_dvd fun k => ?_
  have h := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k a)
  obtain ⟨η', hη'⟩ := exists_padicPow_eq η h
  obtain ⟨b, hb⟩ := h
  refine ⟨Acris.logTeich η' - algebraMap ℤ_[p] (Acris p R) b * Acris.logTeich η, ?_⟩
  have ha : algebraMap ℤ_[p] (Acris p R) a =
      (a.appr k : Acris p R) + (p : Acris p R) ^ k * algebraMap ℤ_[p] (Acris p R) b := by
    conv_lhs => rw [← sub_add_cancel a (a.appr k), hb]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_comm]
  rw [hη', Acris.logTeich_mul, Acris.logTeich_pow, Acris.logTeich_pow, ha, Nat.cast_pow]
  ring


theorem Bcris.algebraMap_padicInt (a : ℤ_[p]) :
    algebraMap ℚ_[p] (Bcris p R) a =
      algebraMap (Acris p R) _ (algebraMap ℤ_[p] (Acris p R) a) :=
  congrArg (algebraMap (BcrisPlus p R) (Bcris p R)) (BcrisPlus.algebraMap_padicInt a)

section Good

variable [IsDomain R] [ValuationRing R] [IsAlgClosed (FractionRing R)] [CharZero R]

variable (p R)


variable {p R}

end Good

namespace Bst

open Polynomial

variable [IsDomain R] [CharZero R] [ValuationRing R]

variable [IsAlgClosed (FractionRing R)]




variable (p R) in
def u : Bst p R := logFlat (pflat (p := p) (R := R))

end Bst

end Reformulated.AutPerF
end
end

