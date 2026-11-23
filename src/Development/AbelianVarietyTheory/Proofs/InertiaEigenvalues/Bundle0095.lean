module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.StdChar

def qe (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

theorem qe_add (a b : ℚ) : qe (a + b) = qe a * qe b := by
  simp only [qe, Rat.cast_add, mul_add, Complex.exp_add]

theorem qe_int (n : ℤ) : qe n = 1 := by
  simp only [qe, Rat.cast_intCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem qe_eq_one {q : ℚ} (h : qe q = 1) : ∃ n : ℤ, q = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (q : ℂ) = n := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast this

def ce (z : AddCircle (1 : ℚ)) : ℂ :=
  Quotient.liftOn' z qe (fun a b h => by
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨n, hn⟩ := h
    have hb : b = a + n := by rw [zsmul_one] at hn; linarith
    rw [hb, qe_add, qe_int, mul_one])

theorem ce_coe (q : ℚ) : ce (q : AddCircle (1 : ℚ)) = qe q := rfl

theorem ce_add (a b : AddCircle (1 : ℚ)) : ce (a + b) = ce a * ce b := by
  induction a using QuotientAddGroup.induction_on with
  | H a =>
  induction b using QuotientAddGroup.induction_on with
  | H b =>
  rw [← QuotientAddGroup.mk_add]
  exact qe_add a b

theorem ce_zero : ce 0 = 1 := by
  rw [show (0 : AddCircle (1 : ℚ)) = ((0 : ℚ) : AddCircle (1 : ℚ)) by simp, ce_coe]
  simpa using qe_int 0

theorem ce_eq_one {z : AddCircle (1 : ℚ)} (h : ce z = 1) : z = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H q =>
  obtain ⟨n, hn⟩ := qe_eq_one h
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [hn]⟩

section Field
variable {F : Type} [NontriviallyNormedField F]

def intSub (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] : AddSubgroup F where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem mem_intSub [IsUltrametricDist F] {x : F} : x ∈ intSub F ↔ ‖x‖ ≤ 1 := Iff.rfl

def charOf (c : F →+ AddCircle (1 : ℚ)) : AddChar F ℂ where
  toFun x := ce (c x)
  map_zero_eq_one' := by simp [ce_zero]
  map_add_eq_mul' a b := by simp [ce_add]

theorem exists_unif [IsUltrametricDist F] [ProperSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨z, hz0, hz1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle z hz1
  rw [h, norm_zero] at this
  linarith

theorem exists_nat_norm_lt_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] :
    ∃ N : ℕ, 0 < N ∧ ‖(N : F)‖ < 1 := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq
    (x := fun n : ℕ => (n : F)) (fun n => by simpa using IsUltrametricDist.norm_natCast_le_one F n)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h := hM (M + 1) (by omega)
  have hlt : φ M < φ (M + 1) := hφ (by omega)
  refine ⟨φ (M + 1) - φ M, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le, ← dist_eq_norm]
  simpa using h

variable (F) in
theorem exists_stdChar [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by
  obtain ⟨ϖ, hϖ0, hϖ1, hle⟩ := exists_unif (F := F)
  have hpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hx : (QuotientAddGroup.mk ϖ⁻¹ : F ⧸ intSub F) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, mem_intSub, norm_inv, not_le]
    exact one_lt_inv_iff₀.2 ⟨hpos, hϖ1⟩
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : F →+ AddCircle (1 : ℚ) := AddMonoidHom.comp c (QuotientAddGroup.mk' (intSub F))
  refine ⟨charOf c', fun x hx1 => ?_, ϖ⁻¹, fun h => hc ?_, fun y hy => ?_⟩
  · show ce (c (QuotientAddGroup.mk x)) = 1
    rw [(QuotientAddGroup.eq_zero_iff x).2 hx1, map_zero, ce_zero]
  · exact ce_eq_one h
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hle y hy

end Field

section Props
variable {F : Type} [NontriviallyNormedField F]

theorem locConst [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun x' hx' => ?_⟩
  have h : ψ (x' - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx').le)
  calc ψ x' = ψ (x + (x' - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h, mul_one]

theorem norm_eq_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] {ψ : AddChar F ℂ}
    (hψ : IsStdChar ψ) (x : F) : ‖ψ x‖ = 1 := by
  obtain ⟨N, hN0, hN1⟩ := exists_nat_norm_lt_one (F := F)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxpos) hN1
  have h1 : ψ ((N ^ k : ℕ) • x) = 1 := by
    apply hψ.1
    rw [nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    exact (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)).trans (by rw [inv_mul_cancel₀ hxpos.ne'])
  rw [AddChar.map_nsmul_eq_pow] at h1
  have h2 : ‖ψ x‖ ^ (N ^ k) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hN0.ne')).1 h2

theorem conductor [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F) :
    (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy y⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy)
      rwa [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul] at this
    apply hx
    have := h (x * y⁻¹) (by rw [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  · intro hy e he
    exact hψ.1 _ (by rw [norm_mul]; exact mul_le_one₀ he (norm_nonneg _) hy)

end Props

section Ext
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem conductor_trace [hU : Unram F E]
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (he : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1)
    {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : E) :
    (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  haveI := hU.ultraE
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    obtain ⟨e₀, he₀, hsum⟩ := he
    obtain ⟨a, ha⟩ := hU.unram y
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ha1 : 1 < ‖a‖ := ha ▸ hy
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha1; linarith
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy a⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ha1)
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.2 ha0), one_mul] at this
      rwa [ha]
    have htr1 : Algebra.trace F E e₀ = 1 := by
      apply (algebraMap F E).injective
      rw [htr, hsum, map_one]
    apply hx
    have := h (algebraMap F E x * e₀ * y⁻¹) (by
      rw [norm_mul, norm_mul, norm_inv, norm_algebraMap', mul_inv_le_iff₀ hypos]
      calc ‖x‖ * ‖e₀‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left he₀ (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by rw [mul_one, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one, ← Algebra.smul_def, LinearMap.map_smul, htr1,
      smul_eq_mul, mul_one] at this
  · intro hy e he'
    apply hψ.1
    have hz : ‖e * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ he' (norm_nonneg _) hy
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz (by rw [hU.norm_star]; exact hz))

end Ext

theorem psi_conductor : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ →
    IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧
    (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧
    ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  intro F E _ _ _ _ hU
  haveI := hU.ultraF
  haveI := hU.charZero
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨htr, he, -⟩ := _root_.GlobalTheory.NTr.traceForm_perfect F E
  exact ⟨exists_stdChar F, fun ψ hψ => ⟨locConst hψ, norm_eq_one hψ, conductor hψ,
    conductor_trace htr he hψ⟩⟩

end GlobalTheory.StdChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionEisensteinPowIntegral
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.WDivE

theorem coeff_vanish_mul {K : Type} [CommRing K] {F G : K⟦X⟧} {a b : ℕ}
    (hF : ∀ k, a < k → coeff k F = 0) (hG : ∀ k, b < k → coeff k G = 0) (k : ℕ) (hk : a + b < k) :
    coeff k (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  by_cases h : a < p.1
  · rw [hF _ h, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem eq_sum_of_vanish {K : Type} [CommRing K] {P : K⟦X⟧} {N : ℕ}
    (hP : ∀ k, N ≤ k → coeff k P = 0) : P = ∑ k : Fin N, C (coeff (k : ℕ) P) * X ^ (k : ℕ) := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [coeff_C_mul_X_pow]
  by_cases hm : m < N
  · rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb; rw [if_neg]; intro h; exact hb (Fin.ext h.symm)
    · simp
  · rw [hP m (by omega), Finset.sum_eq_zero]
    intro b _; rw [if_neg]; omega

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

omit [CompleteSpace K] [NeZero e] in
theorem quotE_mem_A {f : K⟦X⟧} (hf : f ∈ A O K) : quotE l e f ∈ A O K := fun n => by
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact mul_le_one₀ (hf _) (by positivity) (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)

theorem div_E_step {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e * g :=
  ⟨f - E K l e * quotE l e f, quotE l e f,
    sub_mem hf (mul_mem (E_mem l e _) (quotE_mem_A l e hf)),
    fun k hk => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact coeff_sub_E_mul_quotE l e (A_le_Rpi l e hf) m,
    quotE_mem_A l e hf, by ring⟩

omit [IsUltrametricDist K] [CompleteSpace K] [IsUnitBall O K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem coeff_E_pow_vanish (n : ℕ) : ∀ k, e * n < k → coeff k (E K l e ^ n) = 0 := by
  induction n with
  | zero => intro k hk; simp [coeff_one]; omega
  | succ n ih =>
    intro k hk
    rw [pow_succ]
    refine coeff_vanish_mul ih (b := e) (fun j hj => ?_) k (by rw [Nat.mul_succ] at hk; exact hk)
    rw [E, map_add (f := _), coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
    rw [if_neg (by omega), if_neg (by omega), add_zero]

theorem div_E_pow (n : ℕ) {f : K⟦X⟧} (hf : f ∈ A O K) : ∃ P g, P ∈ A O K ∧
    (∀ k, e * n ≤ k → coeff k P = 0) ∧ g ∈ A O K ∧ f = P + E K l e ^ n * g := by
  induction n with
  | zero => exact ⟨0, f, zero_mem _, fun _ _ => by simp, hf, by simp⟩
  | succ n ih =>
    obtain ⟨P, g, hP, hPv, hg, rfl⟩ := ih
    obtain ⟨Q, h, hQ, hQv, hh, rfl⟩ := div_E_step l e hg
    refine ⟨P + E K l e ^ n * Q, h, add_mem hP (mul_mem (pow_mem (E_mem l e _) n) hQ),
      fun k hk => ?_, hh, by ring⟩
    have he := NeZero.pos e
    rw [map_add (f := _), hPv k (by rw [Nat.mul_succ] at hk; omega), zero_add]
    exact coeff_vanish_mul (coeff_E_pow_vanish l e n) (b := e - 1)
      (fun j hj => hQv j (by omega)) k (by rw [Nat.mul_succ] at hk; omega)

end GlobalTheory.WDivE

theorem GlobalTheory.weierstrassDiv_E_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) (f : K⟦X⟧), f ∈ A O K → ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧ f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g := by
  intro O K _ _ _ _ _ _ l e _ _ _ n f hf
  obtain ⟨P, g, hP, hPv, hg, rfl⟩ := GlobalTheory.WDivE.div_E_pow l e n hf
  choose c hc using fun k : Fin (e * n) => (IsUnitBall.mem_range_iff (O := O) (coeff (k : ℕ) P)).2 (hP k)
  refine ⟨c, g, hg, ?_⟩
  simp only [hc]
  rw [← GlobalTheory.WDivE.eq_sum_of_vanish hPv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowSummedRowPowEqAdditiveSystemPowerSum
section
open GlobalTheory.PMonE

open Finset
namespace GlobalTheory.PMonE.WinCoef
variable {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

noncomputable abbrev frobAut : RingAut F := frobeniusEquiv F p

theorem frob_pow_apply (n : ℕ) (x : F) : ((frobAut (F := F) p) ^ n) x = x ^ p ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, RingAut.mul_apply, ih]
    simp only [frobAut, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ]
    rw [mul_comm]

theorem frob_inv_pow_apply (n : ℕ) (x : F) :
    (((frobAut (F := F) p)⁻¹) ^ n) x = ((frobeniusEquiv F p).symm)^[n] x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ_apply, RingAut.mul_apply, ih, RingAut.inv_apply]

theorem pw_eq (k : ℤ) (x : F) : pw p k x = ((frobAut (F := F) p) ^ k) x := by
  unfold pw
  split_ifs with hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, frob_pow_apply]
    simp
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (le_of_lt (not_le.mp hk))
    subst hn
    rw [zpow_neg, zpow_natCast, ← inv_pow, frob_inv_pow_apply]
    simp

theorem pw_mul (k : ℤ) (a b : F) : pw p k (a * b) = pw p k a * pw p k b := by
  rw [pw_eq, pw_eq, pw_eq, map_mul]

theorem pw_win (h r L : ℕ) (hr : r ≤ h) (hL : 1 ≤ L) (n : ℤ) (hn : -(L : ℤ) ≤ n) (z : F) :
    pw p ((r : ℤ) + n * h) (z ^ (p ^ h) ^ (L - 1)) ^ p ^ (h - r) = z ^ (p ^ h) ^ ((n + L).toNat) := by
  have e1 : z ^ (p ^ h) ^ (L - 1) = ((frobAut (F := F) p) ^ (((h * (L - 1) : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e2 : z ^ (p ^ h) ^ ((n + L).toNat) =
      ((frobAut (F := F) p) ^ (((h * (n + L).toNat : ℕ)) : ℤ)) z := by
    rw [zpow_natCast, frob_pow_apply, pow_mul]
  have e3 : ∀ y : F, y ^ p ^ (h - r) = ((frobAut (F := F) p) ^ (((h - r : ℕ)) : ℤ)) y := fun y => by
    rw [zpow_natCast, frob_pow_apply]
  rw [e3, pw_eq, e1, e2, ← RingAut.mul_apply, ← RingAut.mul_apply, ← zpow_add, ← zpow_add]
  congr 2
  have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
  push_cast [Nat.cast_sub hr, Nat.cast_sub hL, ht]
  ring

end GlobalTheory.PMonE.WinCoef


open GlobalTheory.PMonE.WinCoef in
theorem GlobalTheory.PMonE.rowS_winPt_pow_eq_gsum_coefB (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ)
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ) : 1 ≤ L → ∀ (z : Fin h → F) (r : Fin h),
    (rowS p ϖ lam L U (winPt p π L z) r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) =
      gsum (p ^ h) (L + U) (coefB p ϖ lam π L U) z r := by
  intro hL z r
  have hr : (r : ℕ) ≤ h := r.isLt.le
  simp only [rowS, winPt, gsum, Finset.sum_apply, Matrix.mulVec, dotProduct, coefB, Matrix.of_apply]
  rw [Finset.sum_comm (s := Finset.range (L + U + 1)), Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div, sum_pow_char_pow]
  refine Finset.sum_nbij' (fun n => (n + L).toNat) (fun m => (m : ℤ) - L) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Icc, Finset.mem_range] at hm ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro m hm
    simp
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have ht : ((n + L).toNat : ℤ) = n + L := Int.toNat_of_nonneg (by omega)
    have hle : (n + L).toNat ≤ L + U := by omega
    have hsub : (((n + L).toNat : ℕ) : ℤ) - L = n := by omega
    rw [if_pos hle, hsub, term, term, winPt, pw_mul, ← pw_win p h r L hr hL n hn.1 (z j)]
    rw [show lam j * ϖ ^ (-n) * (pw p (↑↑r + n * ↑h) (π j) * pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1))) /
        (lam r * π r ^ p ^ (r : ℕ)) = (lam j * ϖ ^ (-n) * pw p (↑↑r + n * ↑h) (π j) / (lam r * π r ^ p ^ (r : ℕ))) *
        pw p (↑↑r + n * ↑h) (z j ^ (p ^ h) ^ (L - 1)) by ring, mul_pow]
end

