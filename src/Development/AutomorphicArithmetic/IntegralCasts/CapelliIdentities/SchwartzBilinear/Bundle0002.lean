module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Imports
section
namespace UpperTheory.Reformulated.B.P6.r08a

theorem GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep :
    ∀ {K : Type} [inst : AddCommGroup K] (H : AddSubgroup K) (T : Finset K), ∃ Rep ⊆ T, (∀ x ∈ T, ∃ r ∈ Rep, x - r ∈ H) ∧ ∀ r ∈ Rep, ∀ r' ∈ Rep, r - r' ∈ H → r = r' := by
  intro K inst H T
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · intro r hr
      exact absurd hr (Finset.notMem_empty r)
  · intro a S _ha ih
    obtain ⟨Rep, hsub, hcov, hsep⟩ := ih
    by_cases h : ∃ r ∈ Rep, a - r ∈ H
    · refine ⟨Rep, hsub.trans (Finset.subset_insert a S), ?_, hsep⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · rw [hxa]
        exact h
      · exact hcov x hx
    · have h' : ∀ r ∈ Rep, a - r ∉ H := fun r hr har => h ⟨r, hr, har⟩
      refine ⟨insert a Rep, Finset.insert_subset_insert a hsub, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hx
        · refine ⟨a, Finset.mem_insert_self a Rep, ?_⟩
          rw [hxa, sub_self]
          exact H.zero_mem
        · obtain ⟨r, hr, hxr⟩ := hcov x hx
          exact ⟨r, Finset.mem_insert_of_mem hr, hxr⟩
      · intro r hr r' hr' hrr
        rcases Finset.mem_insert.mp hr with hra | hr
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hra, hr'a]
          · rw [hra] at hrr
            exact absurd hrr (h' r' hr')
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hr'a] at hrr
            have hn := H.neg_mem hrr
            rw [neg_sub] at hn
            exact absurd hn (h' r hr)
          · exact hsep r hr r' hr' hrr

end UpperTheory.Reformulated.B.P6.r08a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.IntegerSmulEqAlgebraMapSmul
section
namespace UpperTheory.Reformulated.B.P6.r03a

theorem integer_smul_eq_algebraMap_smul {K : Type} [Field K] [NumberField K] {n : ℕ}
    (r : NumberField.RingOfIntegers K) (x : Fin n → K) :
    r • x = (algebraMap (NumberField.RingOfIntegers K) K r) • x :=
  (algebraMap_smul K r x).symm

theorem GlobalTheory.CompanionTheory.Adelic.SatLine.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {n : ℕ} (M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)) {x : Fin n → K}, x ∈ Submodule.span K (SetLike.coe M) → ∃ (c : NumberField.RingOfIntegers K), c ≠ OfNat.ofNat (nat_lit 0) ∧ c • x ∈ M := by
  intro K _ _ n M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨c1, hc1, h1⟩ := hy
    obtain ⟨c2, hc2, h2⟩ := hz
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    have e : (c1 * c2) • (y + z) = c2 • (c1 • y) + c1 • (c2 • z) := by
      rw [smul_add, mul_smul c1 c2 z, mul_comm c1 c2, mul_smul c2 c1 y]
    rw [e]
    exact M.add_mem (M.smul_mem c2 h1) (M.smul_mem c1 h2)
  | smul a y _ hy =>
    obtain ⟨c, hc, h⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨(q : NumberField.RingOfIntegers K) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have hpq' : a * algebraMap (NumberField.RingOfIntegers K) K (q : NumberField.RingOfIntegers K)
        = algebraMap (NumberField.RingOfIntegers K) K p := hpq
    have e : ((q : NumberField.RingOfIntegers K) * c) • (a • y) = p • (c • y) := by
      rw [integer_smul_eq_algebraMap_smul ((q : NumberField.RingOfIntegers K) * c) (a • y), integer_smul_eq_algebraMap_smul p (c • y),
        integer_smul_eq_algebraMap_smul c y, smul_smul, smul_smul, map_mul, ← hpq']
      congr 1
      ring
    rw [e]
    exact M.smul_mem p h

end UpperTheory.Reformulated.B.P6.r03a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.InvNormSmulMemSphere
section
namespace UpperTheory.Reformulated.B.P6.r24a

theorem quadratic_form_smul_re {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ) (x : V) :
    (Q (c • x) (c • x)).re = c ^ 2 * (Q x x).re := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, Complex.smul_re, smul_eq_mul]
  ring

theorem inv_norm_smul_mem_sphere {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']

theorem PositivityTheory.Rg.Sw.Glob.GCSchH.coercive_of_pos :
    ∀ {V : Type} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ), (∀ (x : V), x ≠ OfNat.ofNat (nat_lit 0) → OfNat.ofNat (nat_lit 0) < (DFunLike.coe (DFunLike.coe Q x) x).re) → ∃ (κ : ℝ), OfNat.ofNat (nat_lit 0) < κ ∧ ∀ (x : V), κ * ‖x‖ ^ OfNat.ofNat (nat_lit 2) ≤ (DFunLike.coe (DFunLike.coe Q x) x).re := by
  intro V _ _ _ Q hQ
  have hcont : Continuous fun x : V => (Q x x).re :=
    Complex.continuous_re.comp (Q.continuous.clm_apply continuous_id)
  by_cases hne : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn hne hcont.continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(Q x0 x0).re, hQ x0 hx0ne, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx
      simp
    · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨y, hyd⟩ : ∃ y : V, y = ‖x‖⁻¹ • x := ⟨_, rfl⟩
      have hy : y ∈ Metric.sphere (0 : V) 1 := hyd ▸ inv_norm_smul_mem_sphere x hx
      have h1 : (Q x0 x0).re ≤ (Q y y).re := hmin hy
      have h2 : ‖x‖ • y = x := by
        rw [hyd, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      have h3 : (Q x x).re = ‖x‖ ^ 2 * (Q y y).re := by
        have := quadratic_form_smul_re Q ‖x‖ y
        rw [h2] at this
        exact this
      rw [h3, mul_comm (‖x‖ ^ 2)]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · refine ⟨1, one_pos, fun x => ?_⟩
    have hx : x = 0 := by
      by_contra hx
      exact hne ⟨_, inv_norm_smul_mem_sphere x hx⟩
    subst hx
    simp

end UpperTheory.Reformulated.B.P6.r24a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.LargePrimeDivisors
section
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors

open scoped Int LT OfNat Polynomial Dvd

open Polynomial in
theorem mul_sub_mul_add_ne_zero (f : Polynomial ℤ) (hf : 0 < f.natDegree) (c : ℤ) :
    f * (f - C c) * (f + C c) ≠ 0 := by
  have h1 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have h2 : f - C c ≠ 0 := by
    intro h
    have h' : f = C c := sub_eq_zero.mp h
    rw [h', natDegree_C] at hf
    exact lt_irrefl _ hf
  have h3 : f + C c ≠ 0 := by
    intro h
    have h' : f = -C c := eq_neg_of_add_eq_zero_left h
    rw [h', natDegree_neg, natDegree_C] at hf
    exact lt_irrefl _ hf
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

theorem exists_nat_eval_mul_ne_zero (P : Polynomial ℤ) (hP : P ≠ 0) (a : ℤ) (ha : a ≠ 0) :
    ∃ t : ℕ, P.eval (a * (t : ℤ)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => a * (t : ℤ))
  · intro x y hxy
    have h2 : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ ha hxy
    exact_mod_cast h2
  · intro t
    exact h t

theorem exists_prime_gt_dvd_eval_of_natDegree_pos (f : Polynomial ℤ) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ (p : ℤ) ∣ Polynomial.eval m f := by
  by_cases hc : f.eval 0 = 0
  · obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p, p, hp, by omega, ?_⟩
    have h1 := Polynomial.sub_dvd_eval_sub (p : ℤ) 0 f
    rw [hc, sub_zero, sub_zero] at h1
    exact h1
  · have hM0 : ((N.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    have hcM : f.eval 0 * (N.factorial : ℤ) ≠ 0 := mul_ne_zero hc hM0
    obtain ⟨t, ht⟩ := exists_nat_eval_mul_ne_zero _ (mul_sub_mul_add_ne_zero f hf (f.eval 0)) _ hcM
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_C] at ht
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) 0 f
    have hw : f.eval (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) =
        f.eval 0 * (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) := by
      linear_combination hk
    rw [hw] at ht
    have hv0 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 0 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv1 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ -1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hna : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs ≠ 1 := by
      intro h0
      rcases Int.natAbs_eq_iff.mp h0 with h | h
      · exact hv1 (by exact_mod_cast h)
      · exact hv2 (by rw [h]; norm_num)
    have hp : Nat.Prime ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) :=
      Nat.minFac_prime hna
    have hpv : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
        (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) :=
      Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
    refine ⟨_, f.eval 0 * (N.factorial : ℤ) * (t : ℤ), hp, ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have hpN : ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) ∣ N.factorial :=
        Nat.dvd_factorial hp.pos hle
      have hpN' : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
          (N.factorial : ℤ) * ((t : ℤ) * k) :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpN) _
      have h1 : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣ 1 :=
        (dvd_add_left hpN').mp hpv
      have h2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac ∣ 1 := by
        exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · rw [hw]
      exact Dvd.dvd.mul_left hpv _

theorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval :
    ∀ (f : Polynomial ℤ), OfNat.ofNat (nat_lit 0) < f.natDegree → ∀ (N : ℕ), ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ p.cast ∣ Polynomial.eval m f := by
  intro f hf N
  exact exists_prime_gt_dvd_eval_of_natDegree_pos f hf N

end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.OneAddPowMulExpLe
section
namespace UpperTheory.Reformulated.B.P6.r22b

theorem one_add_pow_mul_exp_neg_le_of_mul_le (K : ℕ) {a β s : ℝ} (ha : 0 < a) (hKa : (K : ℝ) * a ≤ β) (hs : 0 ≤ s) :
    (1 + s) ^ K * Real.exp (-β * s) ≤ (1 + 1 / a) ^ K := by
  have e : 1 / a * (a * s) = s := by
    rw [← mul_assoc, one_div_mul_cancel ha.ne', one_mul]
  have has : 0 ≤ a * s := mul_nonneg ha.le hs
  have hia : 0 < 1 / a := one_div_pos.mpr ha
  have h1 : 1 + s ≤ (1 + 1 / a) * (1 + a * s) := by
    calc 1 + s ≤ 1 + a * s + 1 / a + 1 / a * (a * s) := by rw [e]; linarith
      _ = (1 + 1 / a) * (1 + a * s) := by ring
  have h2 : 1 + a * s ≤ Real.exp (a * s) := by
    linarith [Real.add_one_le_exp (a * s)]
  have h3 : (1 + s) ^ K ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K := by
    rw [← mul_pow]
    have h4 : 1 + s ≤ (1 + 1 / a) * Real.exp (a * s) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (by linarith))
    exact pow_le_pow_left₀ (by linarith) h4 K
  have h5 : Real.exp (a * s) ^ K * Real.exp (-β * s) ≤ 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    rw [Real.exp_le_one_iff]
    have : (K : ℝ) * (a * s) = ((K : ℝ) * a) * s := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hKa hs]
  have hc : 0 ≤ (1 + 1 / a) ^ K := pow_nonneg (by linarith) K
  have hE : 0 ≤ Real.exp (-β * s) := (Real.exp_pos _).le
  calc (1 + s) ^ K * Real.exp (-β * s)
      ≤ (1 + 1 / a) ^ K * Real.exp (a * s) ^ K * Real.exp (-β * s) :=
        mul_le_mul_of_nonneg_right h3 hE
    _ = (1 + 1 / a) ^ K * (Real.exp (a * s) ^ K * Real.exp (-β * s)) := by ring
    _ ≤ (1 + 1 / a) ^ K * 1 := mul_le_mul_of_nonneg_left h5 hc
    _ = (1 + 1 / a) ^ K := mul_one _

theorem PositivityTheory.Rg.Sw.FFTSteps.SecondLineEstimates.pow_mul_exp_le :
    ∀ (K : ℕ) {β : ℝ}, OfNat.ofNat (nat_lit 0) < β → ∃ (M : ℝ), ∀ (s : ℝ), OfNat.ofNat (nat_lit 0) ≤ s → (OfNat.ofNat (nat_lit 1) + s) ^ K * Real.exp (-β * s) ≤ M := by
  intro K β hβ
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have ha : 0 < β / ((K : ℝ) + 1) := div_pos hβ hK
  have hKa : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ β := by
    have e : ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) = β := by field_simp
    have : (K : ℝ) * (β / ((K : ℝ) + 1)) ≤ ((K : ℝ) + 1) * (β / ((K : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) ha.le
    linarith
  exact ⟨_, fun s hs => one_add_pow_mul_exp_neg_le_of_mul_le K ha hKa hs⟩

end UpperTheory.Reformulated.B.P6.r22b
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.PowMulExpLeHalfExp
section
namespace UpperTheory.Reformulated.B.P6.r23b

theorem pow_mul_exp_le_half_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by
  refine ⟨(2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2), by positivity, ?_⟩
  intro x hx
  have hy : 0 ≤ a / 2 * (1 + x) := by positivity
  have h1 : (a / 2 * (1 + x)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a / 2 * (1 + x)) := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + x)) (n := N) hy
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1' : (a / 2 * (1 + x)) ^ N ≤ Real.exp (a / 2 * (1 + x)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have h2 : (1 + x) ^ N = (2 / a) ^ N * (a / 2 * (1 + x)) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hp : (0 : ℝ) ≤ (2 / a) ^ N := by positivity
  have h3 : (1 + x) ^ N ≤ (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x)) := by
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1' hp
    linarith [this]
  have h4 : Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x)) =
      Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + x) ^ N * Real.exp (-(a * x))
      ≤ ((2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x))) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / a) ^ N * (N.factorial : ℝ) * (Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x))) := by ring
    _ = (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
        rw [h4]; ring

theorem PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp :
    ∀ (N : ℕ) (a : ℝ), OfNat.ofNat (nat_lit 0) < a → ∃ (C : ℝ), OfNat.ofNat (nat_lit 0) ≤ C ∧ ∀ (x : ℝ), OfNat.ofNat (nat_lit 0) ≤ x → (OfNat.ofNat (nat_lit 1) + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / OfNat.ofNat (nat_lit 2) * x)) := by
  intro N a ha
  exact pow_mul_exp_le_half_exp N a ha

end UpperTheory.Reformulated.B.P6.r23b
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.PowTwoPowSubOneGrowth
section
namespace UpperTheory.Reformulated.B.P6.r25a

theorem sq_sub_one_lower_bound (w : ℂ) (hw : ‖w - 1‖ < 1 / 2) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (w + 1) - (w - 1) = (2 : ℂ) := by ring
  have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have h := norm_sub_le (w + 1) (w - 1)
    rwa [h2] at h
  have h4 : ‖(2 : ℂ)‖ = 2 := by simp
  have h5 : (3 / 2 : ℝ) ≤ ‖w + 1‖ := by linarith
  have h6 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  have h7 : ‖w - 1‖ * (3 / 2) ≤ ‖w - 1‖ * ‖w + 1‖ := mul_le_mul_of_nonneg_left h5 h6
  rw [h1, norm_mul]
  linarith

theorem pow_two_pow_sub_one_growth (z : ℂ) (hz : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) = (z ^ (2 ^ k)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    have hs := sq_sub_one_lower_bound (z ^ (2 ^ k)) (hz _)
    calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2) ^ k * ‖z - 1‖) := by ring
      _ ≤ (3 / 2) * ‖z ^ (2 ^ k) - 1‖ := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ ‖(z ^ (2 ^ k)) ^ 2 - 1‖ := hs
      _ = ‖z ^ (2 ^ (k + 1)) - 1‖ := by rw [e]

theorem Tw.HeisLatVac.lc_pow_near_one :
    ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - OfNat.ofNat (nat_lit 1)‖ < OfNat.ofNat (nat_lit 1) / OfNat.ofNat (nat_lit 2)) → z = OfNat.ofNat (nat_lit 1) := by
  intro z hz
  have hz' : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2 := hz
  have hstep := pow_two_pow_sub_one_growth z hz'
  have hd : ‖z - 1‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖z - 1‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
    have h1 := hstep k
    have h2 := hz' (2 ^ k)
    have h2d : (0 : ℝ) < 2 * ‖z - 1‖ := by positivity
    rw [div_lt_iff₀ h2d] at hk
    have h3 : (3 / 2 : ℝ) ^ k * (2 * ‖z - 1‖) = 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
    linarith
  have hz1 : z - 1 = 0 := norm_eq_zero.mp hd
  exact sub_eq_zero.mp hz1

end UpperTheory.Reformulated.B.P6.r25a
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.QuotientOutRightInvariant
section
namespace UpperTheory.Reformulated.B.P6.r20a

theorem finsum_const_eq_card_mul {α : Type} [Finite α] (c : ℂ) : ∑ᶠ _ : α, c = (Nat.card α : ℂ) * c := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem quotient_out_right_invariant {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ (x k : H), k ∈ K → u (x * k) = u x) (x : H) :
    u (Quotient.out (x : H ⧸ K)) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]
  exact hu x k k.2

theorem PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le :
    ∀ {H : Type} [inst : Group H] {S T : Subgroup H}, S ≤ T → ∀ (u : H → ℂ), (∀ (x t : H), t ∈ T → u (x * t) = u x) → S.relIndex T ≠ OfNat.ofNat (nat_lit 0) → (Function.support fun (q : H ⧸ S) ↦ u (Quotient.out q)).Finite → ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = (S.relIndex T).cast * ∑ᶠ (q : H ⧸ T), u (Quotient.out q) := by
  intro H _ S T hST u hu hidx hfin
  have huS : ∀ (x s : H), s ∈ S → u (x * s) = u x := fun x s hs => hu x s (hST hs)
  set e := Subgroup.quotientEquivProdOfLE hST with he
  have hfst : ∀ x : H, (e (x : H ⧸ S)).1 = (x : H ⧸ T) := fun x => rfl
  have key : ∀ q : H ⧸ S, u (Quotient.out q) = u (Quotient.out (e q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hfst x, quotient_out_right_invariant S u huS x, quotient_out_right_invariant T u hu x]
  have hcard : S.relIndex T = Nat.card (T ⧸ S.subgroupOf T) := rfl
  haveI : Finite (T ⧸ S.subgroupOf T) := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hidx)
  set F : (H ⧸ T) × (T ⧸ S.subgroupOf T) → ℂ := fun pr => u (Quotient.out pr.1) with hF
  have h1 : ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = ∑ᶠ (q : H ⧸ S), F (e q) :=
    finsum_congr key
  have h2 : ∑ᶠ (q : H ⧸ S), F (e q) = ∑ᶠ pr, F pr := finsum_comp_equiv e
  have hFfin : (Function.support F).Finite := by
    apply (hfin.image e).subset
    intro pr hpr
    refine ⟨e.symm pr, ?_, by simp⟩
    have : u (Quotient.out (e.symm pr)) = F pr := by
      rw [key]; simp [hF]
    simpa [Function.mem_support, this] using hpr
  have h3 : ∑ᶠ pr, F pr = ∑ᶠ (p : H ⧸ T) (r : T ⧸ S.subgroupOf T), F (p, r) := finsum_curry F hFfin
  have h4 : ∀ p : H ⧸ T, ∑ᶠ (r : T ⧸ S.subgroupOf T), F (p, r)
      = (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p) := fun p =>
    finsum_const_eq_card_mul (u (Quotient.out p))
  have hffin : (Function.support fun (p : H ⧸ T) => u (Quotient.out p)).Finite := by
    apply (hfin.image fun q => (e q).1).subset
    intro p hp
    refine ⟨((Quotient.out p : H) : H ⧸ S), ?_, ?_⟩
    · have h5 : u (Quotient.out ((Quotient.out p : H) : H ⧸ S)) = u (Quotient.out p) :=
        quotient_out_right_invariant S u huS _
      simpa [Function.mem_support, h5] using hp
    · show (e ((Quotient.out p : H) : H ⧸ S)).1 = p
      rw [hfst]
      exact QuotientGroup.out_eq' p
  rw [h1, h2, h3, finsum_congr h4, hcard]
  have hsub : (Function.support fun p : H ⧸ T =>
      (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p)) ⊆ ↑hffin.toFinset := by
    intro p hp
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hp
    intro h0
    apply hp
    simp only [h0, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum _ hffin, Finset.mul_sum]

end UpperTheory.Reformulated.B.P6.r20a
end

