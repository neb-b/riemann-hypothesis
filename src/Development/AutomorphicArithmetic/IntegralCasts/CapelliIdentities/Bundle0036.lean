module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailFurther
section
namespace UpperTheory.Reformulated.B.Yva3.Helpers

private lemma key {α ι : Type} [Fintype ι] [DecidableEq ι] [DecidableEq α] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) (u : Finset (ι → α)) :
    ∑ ξ ∈ u, ∏ i, f (ξ i) ≤ ∏ _i : ι, ∑' x, f x := by
  have h1 : ∑ ξ ∈ u, ∏ i, f (ξ i)
      ≤ ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ξ hξ
      rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hξ
    · intro ξ _ _
      exact Finset.prod_nonneg fun i _ => h0 (ξ i)
  have h2 : ∑ ξ ∈ Fintype.piFinset (fun i => u.image (fun η => η i)), ∏ i, f (ξ i)
      = ∏ i, ∑ x ∈ u.image (fun η => η i), f x :=
    by rw [Finset.prod_univ_sum]
  have h3 : ∏ i, ∑ x ∈ u.image (fun η => η i), f x ≤ ∏ _i : ι, ∑' x, f x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => h0 x
    · intro i _
      exact hf.sum_le_tsum _ (fun x _ => h0 x)
  exact h1.trans (h2.le.trans h3)

private lemma summ {α ι : Type} [Fintype ι] {f : α → ℝ}
    (hf : Summable f) (h0 : ∀ a, 0 ≤ f a) : Summable fun (ξ : ι → α) ↦ ∏ i : ι, f (ξ i) := by
  classical
  exact summable_of_sum_le (fun ξ => Finset.prod_nonneg fun i _ => h0 (ξ i)) (key hf h0)

end UpperTheory.Reformulated.B.Yva3.Helpers

theorem UpperTheory.Reformulated.B.Yva3.main :
    ∀ {k : Type} [inst : Field k] [NumberField k] {ι : Type} [inst : Fintype ι] {f : k → ℝ},
      Summable f → (∀ (a : k), (0 : ℝ) ≤ f a) → Summable fun (ξ : ι → k) ↦ ∏ i : ι, f (ξ i) := by
  intro k _ _ ι _ f hf h0
  exact UpperTheory.Reformulated.B.Yva3.Helpers.summ hf h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralOfNormBounded
section
open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (B : Subalgebra A K) {t y : K} (hty : t * y = 1) (hy : y ∈ B) (ht : IsIntegral A t) :
    t ∈ B := by
  obtain ⟨p, hm, hp⟩ := ht
  have key : ∀ (q : A[X]) (n : ℕ), q.natDegree ≤ n → y ^ n * aeval t q ∈ B := by
    intro q n hq
    rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
    refine Subalgebra.sum_mem _ fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e : y ^ n * (q.coeff i • t ^ i) = q.coeff i • y ^ (n - i) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin
      rw [Nat.add_sub_cancel_left, mul_smul_comm, pow_add]
      congr 1
      rw [mul_comm (y ^ i), mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hy _) _
  have h0 : aeval t p = 0 := hp
  have hd : p.natDegree ≠ 0 := by
    intro h
    have h1 := eq_one_of_monic_natDegree_zero hm h
    simp [h1] at h0
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have h2 : aeval t p.eraseLead + t ^ (d + 1) = 0 := by
    have h3 := p.eraseLead_add_C_mul_X_pow
    rw [← h3, map_add (f := _), map_mul, aeval_C, map_pow, aeval_X, hm.leadingCoeff, map_one, one_mul,
      hd'] at h0
    exact h0
  have h4 : t = -(y ^ d * aeval t p.eraseLead) := by
    have h5 : y ^ d * t ^ (d + 1) = t := by
      rw [pow_succ, ← mul_assoc, ← mul_pow, mul_comm y t, hty, one_pow, one_mul]
    have h6 : aeval t p.eraseLead = -t ^ (d + 1) := eq_neg_of_add_eq_zero_left h2
    rw [h6, mul_neg, neg_neg, h5]
  rw [h4]
  refine neg_mem (key _ _ ?_)
  have := p.eraseLead_natDegree_le
  omega

open Polynomial in
private lemma UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le {l : ℕ} [Fact (Nat.Prime l)] {K : Type}
    [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K]
    [IsScalarTower ℤ_[l] ℚ_[l] K] (z : K) (hz : spectralNorm ℚ_[l] K z ≤ 1) :
    IsIntegral ℤ_[l] z := by
  have hzi : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hzi
  have hc := (spectralValue_le_one_iff hmon).mp hz
  have hl : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hmon
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, ← eval₂_map, hq]
  exact minpoly.aeval ℚ_[l] z

theorem UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {R : Type}
    [inst_1 : CommRing R] [inst_2 : IsLocalRing R] [inst_3 : Algebra ℤ_[l] R] {K : Type} [inst_4 : Field K]
    [inst_5 : Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [inst_7 : Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R,
      IsIntegral ℤ_[l] ((x : R → K) a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ (x : R → K) a ^ n = (↑l : K) * b := by
  intro l _ R _ _ _ K _ _ _ _ _ x a ha
  have hA : ∀ t : K, t * x a = 1 → ¬ IsIntegral ℤ_[l] t := by
    intro t hty ht
    obtain ⟨r, hr⟩ : t ∈ x.range :=
      UpperTheory.Reformulated.B.IntegralOfNormBounded.mem_of_mul_eq_one x.range hty ⟨a, rfl⟩ ht
    have hr' : x r = t := hr
    have hmem : a * r ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ ha
    have hu : IsUnit (1 - a * r) := by
      by_contra hn
      have h1 : 1 - a * r ∈ IsLocalRing.maximalIdeal R := hn
      have h2 := Ideal.add_mem _ h1 hmem
      rw [sub_add_cancel] at h2
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
    have h3 := hu.map x
    have h4 : x (1 - a * r) = 0 := by
      rw [map_sub, map_mul, map_one, hr', mul_comm, hty, sub_self]
    rw [h4] at h3
    exact not_isUnit_zero h3
  change IsIntegral ℤ_[l] (x a) ∧ ∃ (n : ℕ) (b : K), IsIntegral ℤ_[l] b ∧ x a ^ n = (↑l : K) * b
  generalize x a = y at hA
  by_cases hy : y = 0
  · subst hy
    exact ⟨isIntegral_zero, 1, 0, isIntegral_zero, by simp⟩
  let f := spectralMulAlgNorm ℚ_[l] K
  have hf : ∀ z, f z = spectralNorm ℚ_[l] K z := fun _ => rfl
  have hfmul : ∀ u v, f (u * v) = f u * f v := fun u v => map_mul f u v
  have hf1 : f 1 = 1 := map_one f
  have hfy : f y < 1 := by
    have h1 : ¬ f y⁻¹ ≤ 1 := fun h =>
      hA y⁻¹ (inv_mul_cancel₀ hy) (UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ h)
    have h2 : f y * f y⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ hy, hf1]
    have h3 : 0 ≤ f y := (hf y).symm ▸ spectralNorm_nonneg y
    push_neg at h1
    nlinarith
  have hfpow : ∀ (n : ℕ) (z : K), f (z ^ n) = f z ^ n := by
    intro n z
    induction n with
    | zero => simp [hf1]
    | succ n ih => rw [pow_succ, hfmul, ih, pow_succ]
  have hlpos : (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime l).pos
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hlpos) hfy
  have hlK : (l : K) ≠ 0 := by
    have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
    rw [h1]
    have h2 : (l : ℚ_[l]) ≠ 0 := by
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    exact (map_ne_zero (algebraMap ℚ_[l] K)).mpr h2
  refine ⟨UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ hfy.le, n, y ^ n * (l : K)⁻¹,
    UpperTheory.Reformulated.B.IntegralOfNormBounded.isIntegral_of_norm_le _ ?_, ?_⟩
  · have h1 : f ((l : K)⁻¹) = l := by
      have h2 : (l : K)⁻¹ = algebraMap ℚ_[l] K ((l : ℚ_[l])⁻¹) := by simp
      rw [h2, hf, spectralNorm_extends, norm_inv, Padic.norm_p]
      simp
    change f (y ^ n * (l : K)⁻¹) ≤ 1
    rw [hfmul, hfpow, h1]
    calc f y ^ n * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ hlpos.ne'
  · field_simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralQuadraticHalfInt
section
private lemma int_of_isIntegral_cast (q : ℚ) (h : IsIntegral ℤ (q : ℂ)) : ∃ n : ℤ, (n : ℚ) = q := by
  have h1 : IsIntegral ℤ (algebraMap ℚ ℂ q) := by simpa using h
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simpa using hn⟩

private lemma int_of_sq_mul (d : ℕ) (hd : d.Prime) (q : ℚ) (m : ℤ)
    (h : q ^ 2 * (d : ℚ) = m) : ∃ n : ℤ, (n : ℚ) = q := by
  have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
  have h1 : q.num ^ 2 * (d : ℤ) = m * (q.den : ℤ) ^ 2 := by
    have : ((q.num : ℚ)) ^ 2 * (d : ℚ) = (m : ℚ) * (q.den : ℚ) ^ 2 := by
      rw [← hq, ← h]; ring
    exact_mod_cast this
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) := by
    apply IsCoprime.pow
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    simpa [Int.gcd] using q.reduced
  have h2 : (q.den : ℤ) ^ 2 ∣ (d : ℤ) :=
    hc.dvd_of_dvd_mul_left ⟨m, by rw [h1]; ring⟩
  have h3 : q.den * q.den ∣ d := by
    have : q.den ^ 2 ∣ d := by exact_mod_cast h2
    rwa [sq] at this
  have h4 : q.den = 1 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h3)
  refine ⟨q.num, ?_⟩
  rw [← hq, h4]; simp

private lemma even_sub_of_norm (d : ℕ) (hd : d.Prime) (x y n : ℤ)
    (h : x ^ 2 + y ^ 2 * (d : ℤ) = 4 * n) : Even (x - y) := by
  obtain ⟨s, hs | hs⟩ := Int.even_or_odd' x <;> obtain ⟨t, ht | ht⟩ := Int.even_or_odd' y
  · exact ⟨s - t, by omega⟩
  · exfalso
    have h1 : (d : ℤ) = 4 * (n - s ^ 2 - (t ^ 2 + t) * d) := by
      rw [hs, ht] at h; linear_combination h
    have h2 : 2 * 2 ∣ d := by
      have : ((4 : ℕ) : ℤ) ∣ (d : ℤ) := ⟨_, by exact_mod_cast h1⟩
      exact_mod_cast this
    have h3 := Nat.isUnit_iff.1 (hd.prime.squarefree _ h2)
    omega
  · exfalso
    have h1 : (1 : ℤ) = 4 * (n - s ^ 2 - s - t ^ 2 * d) := by
      rw [hs, ht] at h; linear_combination h
    omega
  · exact ⟨s - t, by omega⟩

theorem UpperTheory.integral_quadratic_half_int :
    ∀ (d : ℕ), d.Prime → ∀ (a b : ℚ), IsIntegral ℤ ((a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) → ∃ x y : ℤ, Even (x - y) ∧ (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ)) = ((x : ℂ) + (y : ℂ) * (Complex.I * ((Real.sqrt (d : ℝ) : ℝ) : ℂ))) / 2 := by
  intro d hd a b h
  have hr : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    have : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast this
  generalize Real.sqrt (d : ℝ) = r at h hr ⊢
  have h' : IsIntegral ℤ ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
    have h0 := map_isIntegral_int (starRingEnd ℂ) h
    have e : (starRingEnd ℂ) ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        = (a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ)) := by
      simp only [map_add (f := _), map_mul, map_ratCast, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [e] at h0
  obtain ⟨x, hx⟩ := int_of_isIntegral_cast (2 * a) (by
    have e : ((2 * a : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        + ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast; ring
    rw [e]; exact h.add h')
  obtain ⟨n, hn⟩ := int_of_isIntegral_cast (a ^ 2 + b ^ 2 * d) (by
    have e : ((a ^ 2 + b ^ 2 * d : ℚ) : ℂ) = ((a : ℂ) + (b : ℂ) * (Complex.I * (r : ℂ)))
        * ((a : ℂ) - (b : ℂ) * (Complex.I * (r : ℂ))) := by
      push_cast
      linear_combination (b : ℂ) ^ 2 * (r : ℂ) ^ 2 * Complex.I_sq - (b : ℂ) ^ 2 * hr
    rw [e]; exact h.mul h')
  obtain ⟨y, hy⟩ := int_of_sq_mul d hd (2 * b) (4 * n - x ^ 2) (by
    push_cast
    rw [hn, hx]; ring)
  refine ⟨x, y, even_sub_of_norm d hd x y n ?_, ?_⟩
  · have : (x : ℚ) ^ 2 + (y : ℚ) ^ 2 * (d : ℚ) = 4 * n := by
      rw [hx, hy, hn]; ring
    exact_mod_cast this
  · have hx' : (x : ℂ) = 2 * (a : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hx
    have hy' : (y : ℂ) = 2 * (b : ℂ) := by exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) hy
    rw [hx', hy']; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntertwinerDiagonalization
section
private theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine {K : Type} [Field K]
    (M : GL (Fin 2) K) (D P : Matrix (Fin 2) (Fin 2) K) (hP : P.det ≠ 0)
    (h : (↑M : Matrix (Fin 2) (Fin 2) K) * P = P * D) :
    ∃ (g : GL (Fin 2) K), (↑(g * M * g⁻¹) : Matrix (Fin 2) (Fin 2) K) = D := by
  let u : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero P hP
  have hu : (↑u : Matrix (Fin 2) (Fin 2) K) = P := rfl
  refine ⟨u⁻¹, ?_⟩
  rw [inv_inv, Units.val_mul, Units.val_mul, mul_assoc, hu, h, ← hu, ← mul_assoc,
    Units.inv_mul, one_mul]

theorem UpperTheory.Reformulated.B.IntertwinerDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K]
    (M : GL (Fin (2 : ℕ)) K) {x : K},
    x ≠ (1 : K) →
      (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).trace = (1 : K) + x →
        (↑M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K).det = x →
          ∃ (g : GL (Fin (2 : ℕ)) K),
            (↑(g * M * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) K) = Matrix.diagonal ![(1 : K), x] := by
  intro K _ M x hx ht hd
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : K, (↑M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hD : (Matrix.diagonal ![(1 : K), x] : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hM] at ht hd
  have ht' : a + d = 1 + x := by simpa using ht
  have hd' : a * d - b * c = x := by simpa using hd
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hq : (a - 1) * (a - x) = 0 := by
        rw [hb] at hd'
        linear_combination a * ht' - hd'
      rcases mul_eq_zero.mp hq with h | h
      · have ha : a = 1 := sub_eq_zero.mp h
        have hdx : d = x := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ 1 (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, mul_one, one_mul]
      · have ha : a = x := sub_eq_zero.mp h
        have hdx : d = 1 := by linear_combination ht' - ha
        refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![0, 1; 1, 0] (by simp) ?_
        rw [hM, hD, ha, hb, hc, hdx, Matrix.mul_fin_two, Matrix.mul_fin_two]
        simp
    · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![b, b; 1 - a, x - a] ?_ ?_
      · have : (!![b, b; 1 - a, x - a] : Matrix (Fin 2) (Fin 2) K).det = b * (x - 1) := by
          rw [Matrix.det_fin_two_of]; ring
        rw [this]
        exact mul_ne_zero hb hx'
      · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
        have e1 : a * b + b * (1 - a) = b * 1 + b * 0 := by ring
        have e2 : a * b + b * (x - a) = b * 0 + b * x := by ring
        have e3 : c * b + d * (1 - a) = (1 - a) * 1 + (x - a) * 0 := by
          linear_combination ht' - hd'
        have e4 : c * b + d * (x - a) = (1 - a) * 0 + (x - a) * x := by
          linear_combination x * ht' - hd'
        rw [e1, e2, e3, e4]
  · refine UpperTheory.Reformulated.B.IntertwinerDiagonalization.of_intertwine M _ !![1 - d, x - d; c, c] ?_ ?_
    · have : (!![1 - d, x - d; c, c] : Matrix (Fin 2) (Fin 2) K).det = -(c * (x - 1)) := by
        rw [Matrix.det_fin_two_of]; ring
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero hc hx')
    · rw [hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
      have e1 : a * (1 - d) + b * c = (1 - d) * 1 + (x - d) * 0 := by
        linear_combination ht' - hd'
      have e2 : a * (x - d) + b * c = (1 - d) * 0 + (x - d) * x := by
        linear_combination x * ht' - hd'
      have e3 : c * (1 - d) + d * c = c * 1 + c * 0 := by ring
      have e4 : c * (x - d) + d * c = c * 0 + c * x := by ring
      rw [e1, e2, e3, e4]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvOfUnitCoeffMem
section
theorem UpperTheory.invOfUnit_coeff_mem :
    ∀ (R : Type) [CommRing R] (S : Subring R) (f : PowerSeries R), (∀ n, PowerSeries.coeff n f ∈ S) → PowerSeries.constantCoeff f = 1 → ∀ n, PowerSeries.coeff n (PowerSeries.invOfUnit f 1) ∈ S := by
  intro R _ S f hf _ n
  have h1 : ((1⁻¹ : Rˣ) : R) ∈ S := by
    rw [inv_one, Units.val_one]
    exact S.one_mem
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_invOfUnit]
    split_ifs with hn
    · exact h1
    · refine S.mul_mem (S.neg_mem h1) (S.sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact S.mul_mem (hf _) (ih _ hx)
      · exact S.zero_mem
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionMapCompactFinite
section
theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by
  intro X _ _ _ _ μ U ι hm hU hc hmaps hinv h0 hfin K hK
  rw [MeasureTheory.Measure.map_apply hm hK.measurableSet]
  have hcomp : IsCompact (ι '' (K ∩ U)) :=
    (hK.inter_right hU).image_of_continuousOn (hc.mono Set.inter_subset_right)
  have hsub : ι ⁻¹' K ⊆ ι '' (K ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨ι x, ⟨hx, hmaps x hxU⟩, hinv x hxU⟩
    · exact Or.inr hxU
  calc μ (ι ⁻¹' K) ≤ μ (ι '' (K ∩ U) ∪ Uᶜ) := MeasureTheory.measure_mono hsub
    _ ≤ μ (ι '' (K ∩ U)) + μ Uᶜ := MeasureTheory.measure_union_le _ _
    _ = μ (ι '' (K ∩ U)) := by rw [h0, add_zero]
    _ < ⊤ := hfin _ hcomp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrCases
section
theorem UpperTheory.Reformulated.B.Qe20.irrCases :
    ∀ {G V : Type} [inst : Group G]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ G V),
    ρ.IsIrreducible →
      ∀ (W : Submodule ℂ V), (∀ (g : G), ∀ v ∈ W, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G V _ _ _ ρ hρ W hW
  let S : Subrepresentation ρ := ⟨W, fun g v hv => hW g v hv⟩
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIff
section
theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleIffStable
section
theorem UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable :
    ∀ {H K : Type} [inst : Group H] [inst_1 : Field K] {n : ℕ}
    (r : H →* Matrix (Fin n) (Fin n) K),
    Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) = ⊤ →
      ∀ (W : Submodule K (Fin n → K)),
        (∀ (g : H), ∀ v ∈ W, ((r : H → Matrix (Fin n) (Fin n) K) g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro H K _ _ n r hspan W hW
  have hall : ∀ (A : Matrix (Fin n) (Fin n) K), ∀ v ∈ W, A.mulVec v ∈ W := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range (⇑r : H → Matrix (Fin n) (Fin n) K)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hW g v hv
    | zero => rw [Matrix.zero_mulVec]; exact W.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact W.add_mem hx hy
    | smul c x _ hx => rw [Matrix.smul_mulVec]; exact W.smul_mem c hx
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h := hall (Matrix.of fun a b => if b = i then w a / v i else 0) v hv
    have e : (Matrix.of fun a b => if b = i then w a / v i else 0 :
        Matrix (Fin n) (Fin n) K).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [e] at h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntConj
section
theorem UpperTheory.Reformulated.B.Qf45.isInt_conj :
    ∀ {O : Type} [inst : CommRing O]
    {B : Type} [inst_1 : Ring B] [inst_2 : Algebra O B] (a b k : B),
    a * b = (1 : B) → b * a = (1 : B) → IsIntegral O k → IsIntegral O (a * k * b) := by
  intro O _ B _ _ a b k hab hba hk
  let f : B →ₐ[O] B :=
    { toFun := fun x => a * x * b
      map_one' := by rw [mul_one, hab]
      map_mul' := fun x y => by
        calc a * (x * y) * b = a * x * (b * a) * y * b := by
              rw [hba, mul_one, mul_assoc a x y]
          _ = a * x * b * (a * y * b) := by simp only [mul_assoc]
      map_zero' := by rw [mul_zero, zero_mul]
      map_add' := fun x y => by rw [mul_add, add_mul]
      commutes' := fun r => by
        rw [← Algebra.commutes r a, mul_assoc, hab, mul_one] }
  exact hk.map f
end

