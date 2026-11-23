module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.SerRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_finsum_le {ι : Type*} (F : ι → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ᶠ i, F i‖ ≤ B := by
  refine finsum_induction (p := fun x => ‖x‖ ≤ B) (by simpa using hB) (fun x y hx hy => ?_) h
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem norm_coeff_mul_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hA

theorem norm_coeff_add_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f + g)‖ ≤ max A B := by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_sub_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f - g)‖ ≤ max A B := by
  rw [map_sub]
  exact (norm_sub_le_max' _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_C_le (c : K) (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.C c)‖ ≤ ‖c‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem intSer_mul {f g : PowerSeries K} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := fun n => by
  simpa using norm_coeff_mul_le f g 1 1 hf hg n

theorem intSer_pow {f : PowerSeries K} (hf : IntSer f) (d : ℕ) : IntSer (f ^ d) := by
  induction d with
  | zero => intro n; simpa using norm_coeff_C_le (1 : K) n
  | succ d ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_inv {f : PowerSeries K} (hf : IntSer f) (h0 : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · simp [h0]
    · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      split_ifs with hx
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hx)
      · simp

theorem norm_coeff_subst_le (f h : PowerSeries K) (B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hh : IntSer h) (h0 : PowerSeries.constantCoeff h = 0) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries K)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  refine norm_finsum_le _ hB fun d => ?_
  rw [smul_eq_mul, norm_mul]
  simpa using mul_le_mul (hf d) (intSer_pow hh d n) (norm_nonneg _) hB

theorem series_ring_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  intro p _
  refine ⟨fun f g hf hg => ⟨fun n => ?_, fun n => ?_, intSer_mul hf hg⟩,
    fun f g ⟨A, hf⟩ ⟨B, hg⟩ => ⟨⟨_, norm_coeff_add_le f g A B hf hg⟩, ⟨_, norm_coeff_sub_le f g A B hf hg⟩,
      ⟨_, norm_coeff_mul_le f g A B hf hg⟩⟩,
    fun c => ⟨⟨_, norm_coeff_C_le c⟩, fun hc n => (norm_coeff_C_le c n).trans hc⟩, fun n => ?_,
    fun f => intSer_inv, norm_coeff_subst_le, norm_coeff_mul_le⟩
  · simpa using norm_coeff_add_le f g 1 1 hf hg n
  · simpa using norm_coeff_sub_le f g 1 1 hf hg n
  · rw [PowerSeries.coeff_X]
    split_ifs <;> simp

end GlobalTheory.EvenTheta.SerRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOdd
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_two_Cp_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := (map_natCast _ 2).symm
  have h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p]) := by norm_num
  rw [h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp

theorem intSer_of_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff H = 1) (hH : IntSer (H ^ 2)) : IntSer H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf
    have hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q := by
      rw [pow_two, PowerSeries.coeff_mul]
    have m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    have m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n) := by
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]
      omega
    have c0 : PowerSeries.coeff 0 H = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
    set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS
    have hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S := by
      rw [hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
      simp only [hf, c0, one_mul, mul_one]
      ring
    have hSle : ‖S‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro q hq
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a, b⟩ := q
      simp only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3
      have ha : a < n := by omega
      have hb : b < n := by omega
      simp only [hf, norm_mul]
      exact mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)
    have h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖ := by
      rw [norm_mul, norm_two_Cp_eq_one p hp, one_mul]
    have e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S := by rw [hdec]; ring
    rw [← h2, e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)
    rw [norm_neg]; exact hSle

theorem intSer_of_sq_main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p],
    PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H :=
  fun p _ hp H h0 hH => intSer_of_sq p hp H h0 hH

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneFunctionalEquationPadic
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.FunEq

open PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : K⟦X⟧} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := by
  intro n
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

omit [IsUltrametricDist K] in
theorem intSer_C {c : K} (hc : ‖c‖ ≤ 1) : IntSer (C c : K⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact hc
  · simp

theorem intSer_pow {f : K⟦X⟧} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_C (K := K) (c := 1) (by simp)
  | succ n ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_aeval {h : K⟦X⟧} (hh : IntSer h) (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    IntSer (Polynomial.aeval h P) := by
  intro n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.aeval_eq_sum_range, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (intSer_pow hh i n)

theorem intSer_of_funEq (f h A B : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 1) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : ‖coeff 1 h‖ = 1) (hN : ‖(N : K)‖ < 1) (hA : IntSer A)
    (hA0 : constantCoeff A = 1) (hB : IntSer B) (hB0 : constantCoeff B = 1)
    (e : (PowerSeries.subst h f : K⟦X⟧) * A = f ^ N * B) : IntSer f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  set P : Polynomial K := trunc n f with hP
  have hPi : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    intro i
    rw [hP, coeff_trunc]
    split_ifs with hi
    · exact ih i hi
    · simp
  have hPs : IntSer (P : K⟦X⟧) := fun i => by rw [Polynomial.coeff_coe]; exact hPi i
  have hP0 : constantCoeff (P : K⟦X⟧) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hn,
      coeff_zero_eq_constantCoeff_apply, hf]
  obtain ⟨Q, hQ⟩ : (X : K⟦X⟧) ^ n ∣ f - P := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_pos hm, sub_self]
  have hX : ∀ g : K⟦X⟧, coeff n (X ^ n * g) = constantCoeff g := fun g => by
    simpa using coeff_X_pow_mul g n 0
  have hQ0 : constantCoeff Q = coeff n f := by
    rw [← hX, ← hQ, map_sub, Polynomial.coeff_coe, hP, coeff_trunc, if_neg (lt_irrefl n), sub_zero]
  obtain ⟨h', hh'⟩ : (X : K⟦X⟧) ∣ h := X_dvd_iff.2 hh0
  have h'0 : constantCoeff h' = coeff 1 h := by
    rw [hh', coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have hfe : f = (P : K⟦X⟧) + X ^ n * Q := by rw [← hQ]; ring
  have hsQ : constantCoeff (PowerSeries.subst h Q : K⟦X⟧) = constantCoeff Q := by
    obtain ⟨Q', hQ'⟩ : (X : K⟦X⟧) ∣ Q - C (constantCoeff Q) := X_dvd_iff.2 (by simp)
    have : Q = C (constantCoeff Q) + X * Q' := by rw [← hQ']; ring
    conv_lhs => rw [this, subst_add hs, subst_mul hs, subst_X hs]
    have hC : (PowerSeries.subst h (C (constantCoeff Q) : K⟦X⟧) : K⟦X⟧) = C (constantCoeff Q) := by
      rw [← Polynomial.coe_C, subst_coe hs, Polynomial.aeval_C]; simp
    rw [hC]
    simp [hh0]
  have hL : (PowerSeries.subst h f : K⟦X⟧) * A =
      Polynomial.aeval h P * A + X ^ n * (h' ^ n * PowerSeries.subst h Q * A) := by
    conv_lhs => rw [hfe, subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs]
    have : h ^ n = X ^ n * h' ^ n := by rw [hh', mul_pow]
    rw [this]; ring
  have hR : f ^ N * B = (P : K⟦X⟧) ^ N * B +
      X ^ n * (Q * (∑ i ∈ Finset.range N, f ^ i * (P : K⟦X⟧) ^ (N - 1 - i)) * B) := by
    have := geom_sum₂_mul f (P : K⟦X⟧) N
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
      coeff n ((P : K⟦X⟧) ^ N * B) - coeff n (Polynomial.aeval h P * A) := by
    linear_combination key
  have hu : ‖coeff 1 h ^ n - (N : K)‖ = 1 := by
    have hp : ‖coeff 1 h ^ n‖ = 1 := by rw [norm_pow, hh1, one_pow]
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hp, norm_neg]; exact hN.ne'), hp, norm_neg, max_eq_left hN.le]
  have := congrArg norm k2
  rw [norm_mul, hu, one_mul] at this
  rw [this, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (by rwa [norm_neg]))

theorem intSer_of_funEq_padic : ∀ (p : ℕ) [Fact p.Prime] (f h A B : PowerSeries ℂ_[p]) (N : ℕ), PowerSeries.constantCoeff f = 1 → IntSer h → PowerSeries.constantCoeff h = 0 → ‖PowerSeries.coeff 1 h‖ = 1 → ‖(N : ℂ_[p])‖ < 1 → IntSer A → PowerSeries.constantCoeff A = 1 → IntSer B → PowerSeries.constantCoeff B = 1 → (PowerSeries.subst h f : PowerSeries ℂ_[p]) * A = f ^ N * B → IntSer f :=
  fun _ _ f h A B N => intSer_of_funEq f h A B N

end GlobalTheory.EvenTheta.FunEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
section
open scoped BigOperators

noncomputable section
namespace GlobalTheory.RootInt

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem intSer_mul {f g : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (hg : GlobalTheory.EvenTheta.IntSer g) :
    GlobalTheory.EvenTheta.IntSer (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem intSer_pow {f : PowerSeries K} (hf : GlobalTheory.EvenTheta.IntSer f) (N : ℕ) :
    GlobalTheory.EvenTheta.IntSer (f ^ N) := by
  induction N with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ N ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_of_pow {N : ℕ} (hN : ‖(N : K)‖ = 1) {s : PowerSeries K}
    (hs0 : PowerSeries.constantCoeff s = 1) (hsN : GlobalTheory.EvenTheta.IntSer (s ^ N)) :
    GlobalTheory.EvenTheta.IntSer s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, norm_one]
  set a : PowerSeries K := PowerSeries.mk fun k => if k < n then PowerSeries.coeff k s else 0 with ha
  have hca : ∀ k, PowerSeries.coeff k a = if k < n then PowerSeries.coeff k s else 0 := fun k => by
    rw [ha, PowerSeries.coeff_mk]
  have hai : GlobalTheory.EvenTheta.IntSer a := fun k => by
    rw [hca]; split_ifs with h
    · exact ih k h
    · simp
  have hcb : ∀ k, PowerSeries.coeff k (s - a) = if k < n then 0 else PowerSeries.coeff k s := fun k => by
    rw [map_sub, hca]; split_ifs <;> simp
  set G : PowerSeries K := ∑ i ∈ Finset.range N, s ^ i * a ^ (N - 1 - i) with hG
  have hGN : G * (s - a) = s ^ N - a ^ N := geom_sum₂_mul s a N
  have ha0 : PowerSeries.constantCoeff a = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hca, if_pos hn,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]
  have hG0 : PowerSeries.coeff 0 G = N := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG, map_sum]
    simp [hs0, ha0]
  have key : PowerSeries.coeff n (G * (s - a)) = (N : K) * PowerSeries.coeff n s := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, n)]
    · rw [hG0, hcb, if_neg (lt_irrefl n)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hj : j < n := by
        rcases Nat.eq_zero_or_pos i with rfl | hi
        · exact absurd (by simp at hij; simp [hij]) hne
        · omega
      simp only
      rw [hcb, if_pos hj, mul_zero]
    · intro h; exact absurd (by simp) h
  have h1 : ‖(N : K) * PowerSeries.coeff n s‖ ≤ 1 := by
    rw [← key, hGN, map_sub]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hsN n) ?_)
    rw [norm_neg]; exact intSer_pow hai N n
  rwa [norm_mul, hN, one_mul] at h1

end GlobalTheory.RootInt

theorem GlobalTheory.RootInt.intSer_root : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  intro p _ N _ hcop s hs0 hsN
  refine GlobalTheory.RootInt.intSer_of_pow ?_ hs0 hsN
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact hcop.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalPair
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.VacInt

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  exact h1 ▸ (h 1).2

theorem vac_mem_TT (hg : admG1 D) (crv : Crv D cc δ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) :
    e0 ∈ TT D (tor0 D cc δ) a d := by
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hg cc δ crv a d _ (Or.inr ⟨_, _, sd_std D a, sd_std D d, rfl⟩)).2.1 x hx]
  exact funext (he.2 x hx)

theorem om_vac_norm (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : k ∈ intG D a) (hk' : k' ∈ intG D d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0 := by
  obtain ⟨x, x', -, -, h⟩ := om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk')
  refine ⟨_, ?_, h⟩
  simp [W.chV.unitary, W.chV'.unitary]

theorem om_vac_fix (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) (hu : ∀ u, IntU D u → W.chV'.f u = 1) {k : GA D a} (hk : k ∈ intG D a) :
    W.Om k 1 e0 = e0 := by
  obtain ⟨x, hx, h⟩ := om_vac_left he hT W (AdLattice.intG_of_mem D a k hk)
  rw [h, hu x hx]
  simp

def sphericalPair (hg : admG1 D) (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (had : a ≤ d) (hd : Even d)
    (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 had hd vac W n wt (fun _ hk => om_vac_fix vac.1 (vac_mem_TT hg crv vac.1) W hu hk)
    (fun _ hj => om_vac_norm vac.1 (vac_mem_TT hg crv vac.1) W (one_mem _) hj)

theorem vacuum_eigen : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (a d : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), ∀ W : WeilO D cc δ a d e0,
      e0 ∈ TT D (tor0 D cc δ) a d ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
        W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0) ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → ∀ k ∈ intG D a, W.Om k 1 e0 = e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → a ≤ d → Even d → ∀ t0 : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
        oddE0 D cc δ t0 a d e0 → ∀ n : D.what₂.Tau → ℕ, (∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) →
        ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ HEq P.e0 e0 ∧ HEq P.W W ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 ∧
          P.J = intG D P.d) := by
  intro D hg cc δ crv a d e0 he W
  have hT := vac_mem_TT hg crv he
  exact ⟨hT, fun k hk k' hk' => om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk'),
    fun _ hk _ hk' => om_vac_norm he hT W hk hk', fun hu _ hk => om_vac_fix he hT W hu hk,
    fun hu had hd t0 pt0 vac n wt => ⟨sphericalPair hg crv pt0 had hd vac W n wt hu, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl,
      W.nz, rfl⟩⟩

end GlobalTheory.NormSum.VacInt
end
end

