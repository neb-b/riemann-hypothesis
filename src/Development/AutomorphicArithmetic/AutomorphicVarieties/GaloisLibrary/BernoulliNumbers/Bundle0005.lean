module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BLval
section
open Finset UpperTheory.V.Bern

private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]
    simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]
    push_cast
    ring

theorem UpperTheory.V.Bern.b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k → ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1) := by
    rw [show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0:ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a:ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hq]
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.DirichletCharacterLevelRaising
section
open Finset UpperTheory.V.Bern

private theorem valuation_power_identity {R : Type} [CommRing R] {N p : ℕ} (χ : DirichletCharacter R N) (hp : p.Prime) (a : ℕ) :
    DirichletCharacter.changeLevel (dvd_mul_right N p) χ (a : ZMod (N * p))
      = χ (a : ZMod N) - if p ∣ a then χ (a : ZMod N) else 0 := by
  by_cases hc : a.Coprime (N * p)
  · have hpa : ¬ p ∣ a := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_mul_left_right hc).symm h
    rw [if_neg hpa, sub_zero]
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_right N p) (ZMod.unitOfCoprime a hc)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_right N p)] at this
    exact this
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    split_ifs with h
    · simp
    · have : ¬ a.Coprime N := fun h' => hc (Nat.Coprime.mul_right h' ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm)
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), sub_zero]

private theorem sum_divisible_eq_sum_mul {R : Type} [AddCommMonoid R] {N p : ℕ} (hp : 0 < p) (f : ℕ → R) :
    ∑ a ∈ Icc 1 (N * p), (if p ∣ a then f a else 0) = ∑ b ∈ Icc 1 N, f (p * b) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun b _ => p * b) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [mem_Icc, mem_filter] at hb ⊢
    refine ⟨⟨Nat.mul_pos hp hb.1, ?_⟩, dvd_mul_right _ _⟩
    rw [mul_comm]; exact Nat.mul_le_mul_right _ hb.2
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro a ha
    simp only [mem_Icc, mem_filter] at ha
    obtain ⟨⟨h1, h2⟩, b, rfl⟩ := ha
    refine ⟨b, ?_, rfl⟩
    simp only [mem_Icc]
    constructor
    · exact Nat.pos_of_mul_pos_left h1
    · rw [mul_comm] at h2; exact Nat.le_of_mul_le_mul_right h2 hp
  · intro _ _; rfl

theorem UpperTheory.V.Bern.b_step :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N p : ℕ} (k : ℕ) (χ : DirichletCharacter R N), 0 < N → p.Prime → 1 ≤ k → genB k (DirichletCharacter.changeLevel (dvd_mul_right N p) χ : ZMod (N * p) → R) = (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) * genB k χ := by
  intro R _ _ N p k χ hN hp hk
  have hc := b_comp (dvd_mul_right N p) k (χ : ZMod N → R) (Nat.mul_pos hN hp.pos)
  rw [sub_mul, one_mul]
  nth_rewrite 1 [← hc]
  unfold genB
  simp only [valuation_power_identity χ hp, map_natCast, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  congr 1
  rw [sum_divisible_eq_sum_mul hp.pos (fun a => χ (a : ZMod N) * algebraMap ℚ R (bcoef (N * p) k a)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs := (b_shift N k b hN).2.1 p hp.pos
  have e : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [e, zpow_natCast, mul_comm p N] at hs
  rw [hs, Nat.cast_mul, map_mul, map_mul, map_pow, map_natCast (algebraMap ℚ R)]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
section
open Finset UpperTheory.V.Bern

private theorem dirichletCharacter_unit_isIntegral {R : Type} [CommRing R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (u : (ZMod N)ˣ) : IsIntegral ℤ (χ u) := by
  have hpos : 0 < orderOf u := orderOf_pos u
  refine IsIntegral.of_pow hpos ?_
  have h1 : χ (u : ZMod N) ^ orderOf u = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [h1]
  exact isIntegral_one

theorem UpperTheory.V.Bern.b_primmem :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (∀ A : Subalgebra ℚ R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → Bprim k χ ∈ A) ∧ (∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A) ∧ IsIntegral ℤ ((den N k : R) * Bprim k χ) ∧ IsIntegral ℤ ((den N k : R) * genB k χ) := by
  intro R _ _ N _ k χ
  have hN : N ≠ 0 := NeZero.ne N
  have hc : 0 < χ.conductor :=
    Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have hdvd : den χ.conductor k ∣ den N k := den_dvd χ.conductor_dvd_level k
  have hB : Bprim k χ = genB k (⇑χ.primitiveCharacter) := rfl
  have hint : ∀ a : ZMod N, IsIntegral ℤ (χ a) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      exact dirichletCharacter_unit_isIntegral χ u
    · rw [MulChar.map_nonunit χ ha]
      exact isIntegral_zero
  have part2 : ∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A := by
    intro A hA
    obtain ⟨m, hm⟩ := hdvd
    have hmem : (den χ.conductor k : R) * genB k (⇑χ.primitiveCharacter) ∈ A := by
      refine b_denchar k _ A hc ?_
      intro x
      rcases b_primval χ x with h | ⟨u, h⟩
      · rw [h]; exact A.zero_mem
      · rw [h]; exact hA u
    rw [hB, hm, Nat.cast_mul, mul_comm ((den χ.conductor k : ℕ) : R) (m : R), mul_assoc]
    exact A.mul_mem (natCast_mem A m) hmem
  refine ⟨?_, part2, ?_, ?_⟩
  · intro A hA
    rw [hB]
    refine genB_mem k _ A ?_
    intro x
    rcases b_primval χ x with h | ⟨u, h⟩
    · rw [h]; exact A.zero_mem
    · rw [h]; exact hA u
  · have := part2 (integralClosure ℤ R).toSubring (fun u => dirichletCharacter_unit_isIntegral χ u)
    exact this
  · have := b_denchar k (⇑χ) (integralClosure ℤ R).toSubring (Nat.pos_of_ne_zero hN) (fun a => hint a)
    exact this
end

