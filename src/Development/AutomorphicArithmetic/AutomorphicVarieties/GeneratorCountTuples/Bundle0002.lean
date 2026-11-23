module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumFin
section
open NumberField UpperTheory.V UpperTheory.V.K

theorem UpperTheory.V.K.numFin :
    ∀ C : ℝ, ∃ CK : ℝ, 0 < CK ∧ ∀ e n D : ℕ, 1 ≤ e → 1 ≤ n → 1 ≤ D → 4 * (n : ℝ) * Real.log (2 * (D : ℝ)) * ((2 * (e : ℝ)) * (2 * (e : ℝ) + 3)) * Real.log ((n : ℝ) + 1) + kBound C e n D ≤ kBound CK e n D := by
  intro C
  refine ⟨max C 0 + 9, by positivity, ?_⟩
  intro e n D he hn hD
  simp only [UpperTheory.V.kBound]
  have he' : (1:ℝ) ≤ e := by exact_mod_cast he
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (1:ℝ) ≤ D := by exact_mod_cast hD
  have hL : 0 ≤ Real.log (2 * (D:ℝ)) := Real.log_nonneg (by linarith)
  have hlog : Real.log ((n:ℝ) + 1) ≤ n := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < n + 1 by positivity)
    linarith
  have hx2 : (2:ℝ) ≤ 2 * e * n := by nlinarith
  have hx1 : (1:ℝ) ≤ 2 * e * n := by linarith
  have hC : (2 * (e:ℝ) * n) ^ C ≤ (2 * (e:ℝ) * n) ^ (max C 0) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hC1 : 1 ≤ (2 * (e:ℝ) * n) ^ (max C 0) := Real.one_le_rpow hx1 (le_max_right _ _)
  have h9 : (2 * (e:ℝ) * n) ^ (max C 0 + 9)
      = (2 * (e:ℝ) * n) ^ (max C 0) * (2 * (e:ℝ) * n) ^ (9:ℕ) := by
    rw [Real.rpow_add (by linarith), show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  rw [h9]
  have hQ1 : 4 * (n:ℝ) * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * Real.log ((n:ℝ) + 1)
      ≤ 4 * (n:ℝ) * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * n :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have hQ2 : 4 * (n:ℝ) * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * n
      ≤ 4 * (n:ℝ) * ((2 * (e:ℝ)) * (5 * (e:ℝ))) * n := by
    have h5 : 2 * (e:ℝ) + 3 ≤ 5 * e := by linarith
    have : (2 * (e:ℝ)) * (2 * (e:ℝ) + 3) ≤ (2 * (e:ℝ)) * (5 * (e:ℝ)) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have := mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 4 * n by positivity)
    nlinarith
  set x := 2 * (e:ℝ) * n with hx
  set L := Real.log (2 * (D:ℝ)) with hLdef
  set p := x ^ (max C 0) with hp
  have hQ3 : 4 * (n:ℝ) * ((2 * (e:ℝ)) * (5 * (e:ℝ))) * n = 10 * x ^ 2 := by
    rw [hx]; ring
  have hx7 : (2:ℝ) ^ 7 ≤ x ^ 7 := by gcongr
  have hx9 : 10 * x ^ 2 ≤ x ^ 9 - 1 := by
    have e9 : x ^ 9 = x ^ 2 * x ^ 7 := by ring
    have hsq : 4 ≤ x ^ 2 := by nlinarith
    rw [e9]
    nlinarith
  have hA : 4 * (n:ℝ) * L * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * Real.log ((n:ℝ) + 1)
      ≤ (x ^ 9 - 1) * (p * L) := by
    have e1 : 4 * (n:ℝ) * L * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * Real.log ((n:ℝ) + 1)
        = (4 * (n:ℝ) * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * Real.log ((n:ℝ) + 1)) * L := by ring
    rw [e1]
    have hQ : 4 * (n:ℝ) * ((2 * (e:ℝ)) * (2 * (e:ℝ) + 3)) * Real.log ((n:ℝ) + 1) ≤ x ^ 9 - 1 := by
      linarith
    have hpL : L ≤ p * L := by nlinarith
    have hx90 : 0 ≤ x ^ 9 - 1 := by nlinarith
    calc _ ≤ (x ^ 9 - 1) * L := mul_le_mul_of_nonneg_right hQ hL
      _ ≤ (x ^ 9 - 1) * (p * L) := mul_le_mul_of_nonneg_left hpL hx90
  have hexp1 : Real.exp (x ^ C * L) ≤ Real.exp (p * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hC hL)
  have key : Real.exp (p * L) + (x ^ 9 - 1) * (p * L) ≤ Real.exp (p * x ^ 9 * L) := by
    have e2 : p * x ^ 9 * L = p * L + (x ^ 9 - 1) * (p * L) := by ring
    rw [e2, Real.exp_add]
    have hpL0 : 0 ≤ p * L := mul_nonneg (by linarith) hL
    have h1 : 1 ≤ Real.exp (p * L) := Real.one_le_exp hpL0
    have h2 := Real.add_one_le_exp ((x ^ 9 - 1) * (p * L))
    have h3 : 0 ≤ (x ^ 9 - 1) * (p * L) := mul_nonneg (by nlinarith) hpL0
    nlinarith
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumGens
section
open NumberField UpperTheory.V UpperTheory.V.K

theorem UpperTheory.V.K.numGens :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] (a : ℕ), a ≤ classNumber L * l ^ Module.finrank ℚ L → Real.log a ≤ 4 * (Module.finrank ℚ L : ℝ) * Real.log (2 * ((discr L).natAbs : ℝ)) * Real.log l := by
  intro l hl L _ _ a ha
  have hp := hl.out
  have hn1 : (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := L)
  have hDcast : (((discr L).natAbs : ℕ) : ℝ) = |((discr L : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hD1 : (1 : ℝ) ≤ |((discr L : ℤ) : ℝ)| := by
    rw [← hDcast]
    exact Nat.one_le_cast.2 (Int.natAbs_pos.2 (discr_ne_zero L))
  have hX : 0 ≤ Real.log |((discr L : ℤ) : ℝ)| := Real.log_nonneg hD1
  have hY : Real.log (2 * |((discr L : ℤ) : ℝ)|) = Real.log 2 + Real.log |((discr L : ℤ) : ℝ)| :=
    Real.log_mul (by norm_num) (by linarith)
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hp.two_le
  have hlam : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
  have hlog2 := Real.log_two_gt_d9
  have hcl := KStar.IdealCounting.log_classNumber_le L
  have hlog1 : Real.log (1 + Real.log |((discr L : ℤ) : ℝ)| / 2) ≤ Real.log |((discr L : ℤ) : ℝ)| / 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log |((discr L : ℤ) : ℝ)| / 2 by linarith)
    linarith
  have hh : 0 < classNumber L := classNumber_pos L
  have hmain : Real.log a ≤ Real.log (classNumber L) + (Module.finrank ℚ L : ℝ) * Real.log l := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · rw [Nat.cast_zero, Real.log_zero]
      exact add_nonneg (Real.log_natCast_nonneg _) (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
    · calc Real.log a ≤ Real.log ((classNumber L : ℝ) * (l : ℝ) ^ Module.finrank ℚ L) :=
            Real.log_le_log (by exact_mod_cast ha0) (by exact_mod_cast ha)
        _ = _ := by
          rw [Real.log_mul (by exact_mod_cast hh.ne') (by positivity), Real.log_pow]
  rw [hDcast, hY]
  set X := Real.log |((discr L : ℤ) : ℝ)|
  set lam := Real.log (l : ℝ)
  set n := (Module.finrank ℚ L : ℝ)
  have hlam0 : 0 ≤ lam := by linarith
  have ha1 : X / 2 ≤ X * lam := by nlinarith
  have ha2 : X * lam ≤ n * (X * lam) := by nlinarith [mul_nonneg hX hlam0]
  have ha3 : n * Real.log (1 + X / 2) ≤ n * (X / 2) := mul_le_mul_of_nonneg_left hlog1 (by linarith)
  have ha4 : n * lam ≤ 4 * n * Real.log 2 * lam := by nlinarith [mul_nonneg (show (0:ℝ) ≤ n by linarith) hlam0]
  nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
section
open NumberField UpperTheory.V UpperTheory.V.K

theorem UpperTheory.V.K.primeLe :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L], HasMuQ l L → l ≤ Module.finrank ℚ L + 1 := by
  intro l hl L _ _ hL
  obtain ⟨ζ, hζ⟩ := hL
  have hp := hl.out
  by_cases h2 : l = 2
  · subst h2
    have := Module.finrank_pos (R := ℚ) (M := L)
    omega
  · rw [if_neg h2] at hζ
    have hdeg := minpoly.natDegree_le (A := ℚ) ζ
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hp.pos, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime hp] at hdeg
    omega
end

