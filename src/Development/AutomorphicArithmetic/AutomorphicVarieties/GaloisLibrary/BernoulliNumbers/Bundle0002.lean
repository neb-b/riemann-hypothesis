module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Polybound
section
open Finset UpperTheory.V.Bern

private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

private theorem polybound_norm_fourier (n : ℤ) (y : UnitAddCircle) : ‖fourier n y‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier,
          polybound_norm_fourier]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  refine hbound.trans ?_
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem UpperTheory.V.Bern.b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 → |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by
        rw [le_div_iff₀ hpi]
        nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primden
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primden :
    ∀ (k j : ℕ), j ≤ k → ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  intro k j hjk
  have hdvd : ∀ p : ℕ, p.Prime → p ≤ k + 1 → p ∣ primorial (k + 1) := by
    intro p hp hpk
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z0, hz0⟩ := Bernoulli.vonStaudt_clausen m
    have h2 : m + m = 2 * m := by ring
    rw [h2]
    have hB : bernoulli (2 * m) = (z0 : ℚ) - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, (1 : ℚ) / p := by
      rw [hz0]; ring
    refine ⟨(primorial (k + 1) : ℤ) * z0 - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, ((primorial (k + 1) / p : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hB, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpd : p ∣ primorial (k + 1) := hdvd p hp.2.1 (by omega)
    rw [Nat.cast_div hpd (Nat.cast_ne_zero.2 hp.2.1.ne_zero)]
    ring
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact ⟨0, by rw [bernoulli_eq_zero_of_odd hodd h1]; simp⟩
    · have hj : j = 1 := by
        obtain ⟨r, rfl⟩ := hodd
        omega
      subst hj
      obtain ⟨t, ht⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(t : ℤ), ?_⟩
      rw [bernoulli_one, ht]
      push_cast
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primeq
section
open Finset UpperTheory.V.Bern

private theorem key_primeq {R : Type} [CommRing R] [Algebra ℚ R] {M c c' : ℕ} [NeZero M] (k : ℕ)
    (ψ : DirichletCharacter R c) (ψ' : DirichletCharacter R c') (e : c = c') (h : c ∣ M) (h' : c' ∣ M)
    (hψ : DirichletCharacter.changeLevel h ψ = DirichletCharacter.changeLevel h' ψ') :
    genB k (ψ : ZMod c → R) = genB k (ψ' : ZMod c' → R) ∧ ∀ a : ℕ, ψ (a : ZMod c) = ψ' (a : ZMod c') := by
  subst e
  have hψψ : ψ = ψ' := DirichletCharacter.changeLevel_injective h hψ
  subst hψψ
  exact ⟨rfl, fun _ => rfl⟩

theorem UpperTheory.V.Bern.b_primeq :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (χ.IsPrimitive → Bprim k χ = genB k χ ∧ ∀ a : ℕ, primVal χ a = χ (a : ZMod N)) ∧ ∀ (M : ℕ) [NeZero M] (h : N ∣ M), Bprim k (DirichletCharacter.changeLevel h χ) = Bprim k χ ∧ ∀ a : ℕ, primVal (DirichletCharacter.changeLevel h χ) a = primVal χ a := by
  intro R _ _ N _ k χ
  refine ⟨fun hp => ?_, fun M _ h => ?_⟩
  · exact key_primeq k χ.primitiveCharacter χ hp χ.conductor_dvd_level (dvd_refl N)
      (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_self])
  · refine key_primeq k (DirichletCharacter.changeLevel h χ).primitiveCharacter χ.primitiveCharacter
      (DirichletCharacter.conductor_changeLevel χ h) (DirichletCharacter.conductor_dvd_level _)
      (χ.conductor_dvd_level.trans h) ?_
    rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_trans _ χ.conductor_dvd_level h,
      DirichletCharacter.changeLevel_primitiveCharacter]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primval
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left
    exact MulChar.map_nonunit _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M), ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  intro M _ N _ G
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N)) (fun x : ZMod N => if x.val = 0 then N else x.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro x _
    have hx := ZMod.val_lt x
    refine Finset.mem_Icc.2 ?_
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hx.le⟩
  · intro a ha
    have ha' := Finset.mem_Icc.1 ha
    simp only [ZMod.val_natCast]
    rcases Nat.lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    · have hEq : a = N := by omega
      subst hEq
      simp
  · intro x _
    split_ifs with h0
    · rw [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero x).1 h0).symm
    · exact ZMod.natCast_zmod_val x
  · intro a _
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumval
section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]
        rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply h
        simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Termsum
section
open Finset UpperTheory.V.Bern

private theorem hasSum_hurwitzZeta (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n : ℝ) + x : ℝ) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) := by
  convert HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨h0, h1⟩ hs using 1
  ext1 n
  rw [Complex.cpow_neg, one_div]
  push_cast
  rfl

theorem UpperTheory.V.Bern.b_termsum :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ s : ℂ, 1 < s.re → ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ)) := by
  intro x hx0 hx1 s hs
  have hA := hasSum_hurwitzZeta x hx0.le hx1 s hs
  have hB := hasSum_hurwitzZeta 1 zero_le_one le_rfl s hs
  have hC : HasSum (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    have e1 : (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) = fun n : ℕ => (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
      funext n
      congr 1
      push_cast
      ring
    have e2 : ∑ i ∈ range 1, (((((i : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = 1 := by
      simp
    rw [e1, ← e2]
    exact h
  have hT := (hA.sub hB).sub ((hB.sub hC).mul_left (1 - (x : ℂ)))
  rw [hT.tsum_eq]
  ring
end

