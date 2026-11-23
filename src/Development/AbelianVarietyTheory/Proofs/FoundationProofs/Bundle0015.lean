module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesTaylorSubstFirstOrder
section
open Polynomial

namespace GlobalTheory

namespace TaylorSubst

variable {k : Type} [Field k]

theorem subst_decomp (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    (χ.subst u : PowerSeries k) =
      u * ((PowerSeries.mk fun p => PowerSeries.coeff (p + 1) χ).subst u : PowerSeries k)
        + PowerSeries.C (PowerSeries.constantCoeff χ) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const χ]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_X hs,
    PowerSeries.subst_C]
  rfl

theorem constantCoeff_subst_eq (χ u : PowerSeries k) (hu : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (χ.subst u : PowerSeries k) = PowerSeries.constantCoeff χ := by
  rw [subst_decomp χ u hu]
  simp [hu]

theorem X_pow_dvd_sub_trunc (χ : PowerSeries k) (n : ℕ) :
    (PowerSeries.X : PowerSeries k) ^ n ∣ χ - (PowerSeries.trunc n χ : PowerSeries k) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hi]

theorem X_pow_dvd_subst_sub (χ u v : PowerSeries k) (n : ℕ)
    (hu : PowerSeries.constantCoeff u = 0) (hv : PowerSeries.constantCoeff v = 0)
    (huv : (PowerSeries.X : PowerSeries k) ^ n ∣ u - v) :
    (PowerSeries.X : PowerSeries k) ^ n ∣
      (χ.subst u : PowerSeries k) - (χ.subst v : PowerSeries k) := by
  have hsu := PowerSeries.HasSubst.of_constantCoeff_zero' hu
  have hsv := PowerSeries.HasSubst.of_constantCoeff_zero' hv
  obtain ⟨ρ, hρ⟩ := X_pow_dvd_sub_trunc χ n
  have hχ : χ = (PowerSeries.trunc n χ : PowerSeries k) + PowerSeries.X ^ n * ρ := by
    rw [← hρ]; ring
  rw [hχ, PowerSeries.subst_add hsu, PowerSeries.subst_add hsv, PowerSeries.subst_mul hsu,
    PowerSeries.subst_mul hsv, PowerSeries.subst_pow hsu, PowerSeries.subst_pow hsv,
    PowerSeries.subst_X hsu, PowerSeries.subst_X hsv, PowerSeries.subst_coe hsu,
    PowerSeries.subst_coe hsv]
  have hXu : (PowerSeries.X : PowerSeries k) ∣ u := PowerSeries.X_dvd_iff.mpr hu
  have hXv : (PowerSeries.X : PowerSeries k) ∣ v := PowerSeries.X_dvd_iff.mpr hv
  have h1 : (PowerSeries.X : PowerSeries k) ^ n ∣
      (Polynomial.aeval u (PowerSeries.trunc n χ) : PowerSeries k)
        - Polynomial.aeval v (PowerSeries.trunc n χ) := by
    refine dvd_trans huv ?_
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, ← Polynomial.eval_map]
    exact Polynomial.sub_dvd_eval_sub u v _
  have h2 : (PowerSeries.X : PowerSeries k) ^ n ∣
      u ^ n * (ρ.subst u : PowerSeries k) - v ^ n * (ρ.subst v : PowerSeries k) :=
    dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXu n) _)
      (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hXv n) _)
  have := dvd_add h1 h2
  convert this using 1
  ring

end TaylorSubst

theorem taylor_subst_first_order : ∀ (k : Type) [Field k] (φ a b : PowerSeries k) (m : ℕ), 1 ≤ m → PowerSeries.constantCoeff a = 0 →
 PowerSeries.constantCoeff (φ.subst a : PowerSeries k) = PowerSeries.constantCoeff φ ∧
 (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ (φ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - φ.subst a - PowerSeries.X ^ m * PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
  intro k _ φ a b m hm ha
  refine ⟨TaylorSubst.constantCoeff_subst_eq φ a ha, ?_⟩
  set ψ : PowerSeries k := PowerSeries.mk fun p => PowerSeries.coeff (p + 1) φ with hψ
  have ha' : PowerSeries.constantCoeff (a + PowerSeries.X ^ m * b) = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp [ha, pow_succ]
  rw [TaylorSubst.subst_decomp φ _ ha', TaylorSubst.subst_decomp φ _ ha]
  rw [← hψ]
  have hψ0 : PowerSeries.constantCoeff ψ = PowerSeries.coeff 1 φ := by
    rw [hψ, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  have hA : (PowerSeries.X : PowerSeries k) ∣
      b * (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k)
        - PowerSeries.C (PowerSeries.constantCoeff b * PowerSeries.coeff 1 φ) := by
    rw [PowerSeries.X_dvd_iff, map_sub, map_mul, TaylorSubst.constantCoeff_subst_eq ψ _ ha',
      hψ0, PowerSeries.constantCoeff_C, sub_self]
  have hB : (PowerSeries.X : PowerSeries k) ^ m ∣
      (ψ.subst (a + PowerSeries.X ^ m * b) : PowerSeries k) - ψ.subst a :=
    TaylorSubst.X_pow_dvd_subst_sub ψ _ a m ha' ha (by simp)
  have hXa : (PowerSeries.X : PowerSeries k) ∣ a := PowerSeries.X_dvd_iff.mpr ha
  have h := dvd_add (mul_dvd_mul_left ((PowerSeries.X : PowerSeries k) ^ m) hA)
    (mul_dvd_mul hB hXa)
  rw [← pow_succ] at h
  convert h using 1
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeEqBotOrMaximalIdealOfIsFieldAway
section
namespace GlobalTheory

open IsLocalRing

section

variable {B : Type*} [CommRing B] [IsDomain B]

variable [IsNoetherianRing B] [IsLocalRing B]

theorem prime_eq_bot_or_maximalIdeal_of_forall_mem {f : B} (hf : f ≠ 0)
    (H : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → f ∈ p) {p : Ideal B} (hp : p.IsPrime) :
    p = ⊥ ∨ p = maximalIdeal B := by
  classical
  refine or_iff_not_imp_left.mpr fun hp0 => ?_
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hmin : ∀ q : Ideal B, q.IsPrime → q ≠ ⊥ →
      ∃ P ∈ (Ideal.span {f}).minimalPrimes, P ≤ q := fun q hq hq0 =>
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem q).mpr (H q hq hq0))

  have hcover : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ P ∈ (hfin.toFinset : Set (Ideal B)), ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.Finite.coe_toFinset, id, Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := hmin p hp hp0
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem (maximalIdeal B)).mpr hx)
    haveI hQp : Q.IsPrime := hQ.1.1
    have hxQ : x ∈ Q := (Ideal.span_singleton_le_iff_mem Q).mp hQ.1.2
    have hQ0 : Q ≠ ⊥ := fun h => hx0 (by simpa [h] using hxQ)
    have hQ1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
    obtain ⟨P, hP, hPQ⟩ := hmin Q hQp hQ0
    haveI hPp : P.IsPrime := hP.1.1
    have hfP : f ∈ P := (Ideal.span_singleton_le_iff_mem P).mp hP.1.2
    refine ⟨P, hP, ?_⟩
    rcases hPQ.eq_or_lt with h | h
    · exact h ▸ hxQ
    · have h1 : P.height < 1 := (Ideal.height_strict_mono_of_isPrime h).trans_le hQ1
      rw [ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at h1
      exact absurd (by simpa [h1] using hfP) hf
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime (⊥ : Ideal B) ⊥ fun P hP _ _ =>
    ((Set.Finite.mem_toFinset hfin).mp hP).1.1).mp hcover
  have hP' := (Set.Finite.mem_toFinset hfin).mp hP
  have hpm : p ≤ maximalIdeal B := le_maximalIdeal hp.ne_top
  exact le_antisymm hpm (hmP.trans (hP'.2
    ⟨hp, (Ideal.span_singleton_le_iff_mem p).mpr (H p hp hp0)⟩ (hpm.trans hmP)))

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
section
open Filter Topology

namespace GlobalTheory

theorem one_div_succ_rpow_one_add_le_telescope {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    1 / (x + 1) ^ (1 + s) ≤ (1 / x ^ s - 1 / (x + 1) ^ s) / s := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1) / x := div_pos hx1 hx
  have h1 : 1 - ((x + 1) / x)⁻¹ ≤ Real.log ((x + 1) / x) := Real.one_sub_inv_le_log_of_pos hq
  have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
  have h3 : 1 + s * (1 / (x + 1)) ≤ ((x + 1) / x) ^ s := by
    rw [Real.rpow_def_of_pos hq]
    have h4 := Real.add_one_le_exp (Real.log ((x + 1) / x) * s)
    have h5 : s * (1 / (x + 1)) ≤ Real.log ((x + 1) / x) * s := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (h2 ▸ h1) hs.le
    linarith
  rw [Real.div_rpow hx1.le hx.le] at h3
  rw [Real.rpow_add hx1, Real.rpow_one]
  have hA : 0 < x ^ s := Real.rpow_pos_of_pos hx _
  have hB : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hx1 _
  generalize x ^ s = A at *
  generalize (x + 1) ^ s = B at *
  rw [le_div_iff₀ hs]
  have h6 : (1 + s * (1 / (x + 1))) / B ≤ B / A / B := by gcongr
  have h7 : B / A / B = 1 / A := by field_simp
  have h8 : (1 + s * (1 / (x + 1))) / B = 1 / B + 1 / ((x + 1) * B) * s := by field_simp
  linarith

theorem sum_range_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s)
      ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := by
  induction k with
  | zero =>
    have : (1 + s) ≠ 0 := by linarith
    simp [Finset.sum_range_succ, Real.zero_rpow this]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
    have h := one_div_succ_rpow_one_add_le_telescope (x := (k : ℝ) + 1) hs (by positivity)
    have e : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
    have e' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [e, e']
    have : (1 - 1 / ((k : ℝ) + 1 + 1) ^ s) / s = (1 - 1 / ((k : ℝ) + 1) ^ s) / s
        + (1 / ((k : ℝ) + 1) ^ s - 1 / ((k : ℝ) + 1 + 1) ^ s) / s := by ring
    linarith

theorem tsum_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s) ≤ 1 + 1 / s := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun k => ?_
  calc ∑ n ∈ Finset.range k, 1 / (n : ℝ) ^ (1 + s)
      ≤ ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => by positivity)
    _ ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := sum_range_one_div_rpow_one_add_le hs k
    _ ≤ 1 + 1 / s := by
        have : 0 ≤ 1 / ((k : ℝ) + 1) ^ s := by positivity
        gcongr
        linarith

theorem prod_primesBelow_inv_one_sub_one_div_rpow_le :
    ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  intro s hs N
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hE := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) (by simp)
    (fun {m n} _ => by
      simp only [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div])
    hsum.norm N
  have hP : ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹
      = ∏ p ∈ N.primesBelow, ∑' e : ℕ, 1 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) := Real.one_lt_rpow hp1 (by linarith)
    rw [← tsum_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 h1)]
    refine tsum_congr fun e => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) e, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast, one_div_pow]
  rw [hP, hE]
  exact (Summable.tsum_subtype_le _ _ (fun n => by positivity) hsum).trans
    (tsum_one_div_rpow_one_add_le hs)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwo
section
open Filter Topology

namespace GlobalTheory

theorem prod_Ico_inv_one_sub_inv_sq (M : ℕ) :
    ∏ n ∈ Finset.Ico 2 (M + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ = 2 * ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2 := by
      field_simp; ring
    rw [h3]
    field_simp
    ring

theorem one_le_inv_one_sub_inv_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n:ℝ)^2 := by positivity
  have hlt : 1 / (n:ℝ)^2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact one_le_inv₀ (by linarith) |>.mpr (by linarith)

theorem factor_le (s : ℝ) (hs : 0 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1:ℝ) ≤ p := by linarith
  have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  rw [Real.rpow_two] at hle
  have hsq : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hlt : 1 / (p:ℝ)^2 < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply inv_anti₀
  · linarith
  · have : 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2 :=
      one_div_le_one_div_of_le (by positivity) hle
    linarith

theorem prod_primesBelow_zeta_two_add_le_two :
    ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  intro s hs N
  have hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hmem : ∀ p ∈ N.primesBelow, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹
      ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have := one_le_inv_one_sub_inv_sq (hmem p hp)
          have h2 := factor_le s hs (hmem p hp)

          have hp' : (2:ℝ) ≤ p := by exact_mod_cast hmem p hp
          have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hpos : 0 < (p:ℝ) ^ (2 * (1 + s)) := by positivity
          have hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1 := by
            rw [div_lt_one hpos]; rw [Real.rpow_two] at hle; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp; exact factor_le s hs (hmem p hp)
    _ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
          Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))
        have h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
          apply Finset.one_le_prod₀
          intro n hn
          exact one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1
        nlinarith
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N
    _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinConvolutionCoeff
section
open Complex Filter Topology

namespace GlobalTheory

theorem rankin_convolution_coeff_of_squareSupported (e : ℕ) (χ ψ θ g b z : ℕ → ℂ)
    (hψ : ∀ m n, ψ (m * n) = ψ m * ψ n) (hθ : ∀ m n, θ (m * n) = θ m * θ n)
    (hg : ∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2))
    (hb : ∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2)
    (hz : ∀ a, z a = if Nat.sqrt a * Nat.sqrt a = a then χ (Nat.sqrt a) * ψ (Nat.sqrt a) * θ (Nat.sqrt a) * (Nat.sqrt a : ℂ) ^ (3 * e - 1) else 0)
    (n : ℕ) (hn : n ≠ 0) :
    LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n
      = LSeries.convolution z (fun n : ℕ => g n * b n) n := by
  simp only [LSeries.convolution_def]
  have hL : ∀ p ∈ n.divisorsAntidiagonal, (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2)
      = ∑ δ ∈ (Nat.gcd p.1 p.2).divisors, χ δ * (δ:ℂ)^(2*e) * ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * g (n / δ^2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h1 : 0 < p.1 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, zero_mul]))
    have h2 : 0 < p.2 := Nat.pos_of_ne_zero (fun h => hn (by rw [← hp.1, h, mul_zero]))
    rw [show (ψ p.1 * (p.1:ℂ)^(e-1) * g p.1) * (θ p.2 * g p.2) = ψ p.1 * (p.1:ℂ)^(e-1) * θ p.2 * (g p.1 * g p.2) by ring, hg _ _ h1 h2, Finset.mul_sum, hp.1]
    exact Finset.sum_congr rfl (fun δ _ => by ring)
  have hR : ∀ p ∈ n.divisorsAntidiagonal, z p.1 * (g p.2 * b p.2)
      = ∑ q ∈ p.2.divisorsAntidiagonal, z p.1 * g p.2 * (ψ q.1 * (q.1:ℂ)^(e-1) * θ q.2) := by
    intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have h2 : p.2 ≠ 0 := fun h => hn (by rw [← hp.1, h, mul_zero])
    rw [hb _ h2, ← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_sigma', Finset.sum_sigma']
  have key : ∀ s x y : ℕ, 0 < s → s * s * (x * y) = n →
      z (s * s) * g (x * y) * (ψ x * (x:ℂ)^(e-1) * θ y)
        = χ s * (s:ℂ)^(2*e) * ψ (s * x) * ((s * x : ℕ):ℂ)^(e-1) * θ (s * y) * g (n / s^2) := by
    intro s x y hs hn'
    have hsq : Nat.sqrt (s * s) = s := Nat.sqrt_eq s
    have hdiv : n / s^2 = x * y := by
      rw [← hn', sq, Nat.mul_div_cancel_left _ (Nat.mul_pos hs hs)]
    have hpow : (s:ℂ)^(2*e) * (s:ℂ)^(e-1) = (s:ℂ)^(3*e-1) := by
      rw [← pow_add]; congr 1; omega
    rw [hz, hsq, if_pos rfl, hdiv, hψ, hθ, ← hpow]
    push_cast
    rw [mul_pow]
    ring
  have dec : ∀ a : (_ : ℕ × ℕ) × (ℕ × ℕ), a ∈ n.divisorsAntidiagonal.sigma (fun p => p.2.divisorsAntidiagonal) →
      z a.1.1 * g a.1.2 * (ψ a.2.1 * (a.2.1:ℂ)^(e-1) * θ a.2.2) ≠ 0 →
      ∃ s x y : ℕ, 0 < s ∧ s * s * (x * y) = n ∧ a = ⟨(s * s, x * y), (x, y)⟩ := by
    rintro ⟨⟨a, c⟩, ⟨x, y⟩⟩ hmem hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hmem
    obtain ⟨⟨hac, -⟩, hxy, -⟩ := hmem
    have h : Nat.sqrt a * Nat.sqrt a = a := by
      by_contra h
      apply hne
      simp only [hz, if_neg h, zero_mul]
    have ha : a ≠ 0 := fun h0 => hn (by rw [← hac, h0, zero_mul])
    refine ⟨Nat.sqrt a, x, y, Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero ha), by rw [h, hxy, hac], ?_⟩
    rw [h, hxy]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => (⟨(Nat.sqrt a.1.1 * a.2.1, Nat.sqrt a.1.1 * a.2.2), Nat.sqrt a.1.1⟩ : (_ : ℕ × ℕ) × ℕ)) ?_ ?_ ?_ ?_
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    have hx : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; apply hn; rw [← hn']; ring)
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors, Nat.sqrt_eq]
    refine ⟨⟨by rw [← hn']; ring, hn⟩, Nat.dvd_gcd (dvd_mul_right s x) (dvd_mul_right s y),
      (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hs hx)).ne'⟩
  · intro a1 h11 h12 a2 h21 h22 heq
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a1 h11 h12
    obtain ⟨t, u, v, ht, hn'', rfl⟩ := dec a2 h21 h22
    simp only [Nat.sqrt_eq, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at heq
    obtain ⟨⟨h1, h2⟩, h3⟩ := heq
    subst h3
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h1
    obtain rfl := Nat.eq_of_mul_eq_mul_left hs h2
    rfl
  · rintro ⟨⟨x, y⟩, δ⟩ hb0 hne
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors] at hb0
    obtain ⟨⟨hxy, -⟩, hδ, hg0⟩ := hb0
    have hδ0 : 0 < δ := Nat.pos_of_dvd_of_pos hδ (Nat.pos_of_ne_zero hg0)
    obtain ⟨x', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_left x y)
    obtain ⟨y', rfl⟩ := dvd_trans hδ (Nat.gcd_dvd_right (δ * x') y)
    have hn'' : δ * δ * (x' * y') = n := by rw [← hxy]; ring
    have hxy0 : x' * y' ≠ 0 := fun h0 => hn (by rw [← hn'', h0, mul_zero])
    refine ⟨⟨(δ * δ, x' * y'), (x', y')⟩, ?_, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨hn'', hn⟩, trivial, hxy0⟩
    · intro h0
      apply hne
      refine Eq.trans ?_ h0
      exact (key δ x' y' hδ0 hn'').symm
    · simp only [Nat.sqrt_eq]
  · intro a ha hne
    obtain ⟨s, x, y, hs, hn', rfl⟩ := dec a ha hne
    simp only [Nat.sqrt_eq]
    exact key s x y hs hn'

theorem rankin_convolution_coeff : ∀ (e : ℕ) (χ ψ θ g b : ℕ → ℂ), (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → ∀ n : ℕ, n ≠ 0 → LSeries.convolution (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (fun n : ℕ => θ n * g n) n = LSeries.convolution (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (fun n : ℕ => g n * b n) n := by
  intro e χ ψ θ g b hψ hθ hg hb n hn
  exact rankin_convolution_coeff_of_squareSupported e χ ψ θ g b _ hψ hθ hg hb (fun _ => rfl) n hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedFibresAlmostAll
section
open Polynomial

attribute [local instance] FractionRing.liftAlgebra

namespace GlobalTheory

theorem reduced_fibres_almost_all (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
    [Module.Finite k[X] A] [Module.Free k[X] A] :
    ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal →
      algebraMap k[X] A (X - C α) ∉ Q ^ 2 := by
  haveI : Module.IsTorsionFree k[X] A := inferInstance
  haveI : FaithfulSMul k[X] A := inferInstance
  haveI : Algebra.IsSeparable (FractionRing k[X]) (FractionRing A) := inferInstance
  have hD := differentIdeal_ne_bot (A := k[X]) (B := A)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  have hc := Ideal.comap_ne_bot_of_integral_mem hd0 hd (Algebra.IsIntegral.isIntegral (R := k[X]) d)
  obtain ⟨δ, hδ, hδ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨δ, hδ0, fun α hα Q hQ hmem => hα ?_⟩
  set p : Ideal k[X] := Ideal.span {X - C α} with hpdef
  haveI hpmax : p.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C α)
  have hp0 : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero α
  have hP : Q ^ 2 ∣ p.map (algebraMap k[X] A) := by
    rw [Ideal.dvd_iff_le, hpdef, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy; exact hmem
  have hdiv := pow_sub_one_dvd_differentIdeal (A := k[X]) (B := A) Q 2 hp0 hP
  rw [show 2 - 1 = 1 from rfl, pow_one, Ideal.dvd_iff_le] at hdiv
  have hδQ : δ ∈ Q.comap (algebraMap k[X] A) := hdiv hδ
  have hXQ : X - C α ∈ Q.comap (algebraMap k[X] A) :=
    Ideal.mem_comap.mpr (Ideal.pow_le_self two_ne_zero hmem)
  have hle : p ≤ Q.comap (algebraMap k[X] A) := by
    rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]; exact hXQ
  have heq : p = Q.comap (algebraMap k[X] A) :=
    hpmax.eq_of_le (hQ.isPrime.comap _).ne_top hle
  rw [← heq, hpdef, Ideal.mem_span_singleton, dvd_iff_isRoot] at hδQ
  exact hδQ

end GlobalTheory
end

