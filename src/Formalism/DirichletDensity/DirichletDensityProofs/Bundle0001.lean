module

public import Mathlib
public import Formalism.DirichletDensity.Statement

@[expose] public section

-- bundled from Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
section
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries

noncomputable section

namespace Formalism.HF.P

variable {q : ℕ} [NeZero q] {a : ZMod q}

private lemma apld_term_lemma (a : ZMod q) (x : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (residueClass a n : ℂ)) (x : ℂ) n =
      ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, residueClass_apply_zero, zero_div, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]

lemma apld_tsum_residueClass_eq (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  have hx' : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx
  have hLS : LSeries (fun n ↦ (residueClass a n : ℂ)) x =
      ((∑' n, residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => apld_term_lemma a x n
  have hE := eqOn_LFunctionResidueClassAux ha hx'
  have hA : LFunctionResidueClassAux a x =
      (((∑' n, residueClass a n / (n : ℝ) ^ x) - (q.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ) := by
    rw [hE]
    simp only [hLS]
    push_cast
    rfl
  rw [hA, Complex.ofReal_re]
  ring

lemma apld_summable (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ x := by
  have hL : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) x :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissaOfAbsConv_residueClass_le_one a).trans_lt
      (by simp only [Complex.ofReal_re]; exact_mod_cast hx))
  have h2 : Summable (LSeries.term (fun n ↦ (residueClass a n : ℂ)) x) := hL
  have h3 : Summable fun n : ℕ ↦ ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    convert h2 using 1
    funext n
    exact (apld_term_lemma a x n).symm
  exact Complex.summable_ofReal.1 h3

lemma residue_class_l_function_tendsto (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) := by
  have hc : ContinuousWithinAt (fun x : ℝ ↦ LFunctionResidueClassAux a x) (Set.Ioi 1) 1 := by
    have h1 : ContinuousWithinAt (LFunctionResidueClassAux a) {s : ℂ | 1 ≤ s.re} ((1 : ℝ) : ℂ) :=
      continuousOn_LFunctionResidueClassAux a _ (by simp)
    exact h1.comp Complex.continuous_ofReal.continuousWithinAt
      (fun x hx => by simp only [Set.mem_setOf_eq, Complex.ofReal_re]; exact le_of_lt hx)
  have hre : Tendsto (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (𝓝[>] 1)
      (𝓝 (LFunctionResidueClassAux a ((1 : ℝ) : ℂ)).re) :=
    (Complex.continuous_re.tendsto _).comp hc.tendsto
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  simpa using hlin.mul hre

lemma apld_nonprime_nonneg (a : ZMod q) (x : ℝ) (n : ℕ) :
    0 ≤ (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x := by
  split_ifs
  · simp
  · exact div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

lemma apld_nonprime_le (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤
      (if n.Prime then 0 else residueClass a n) / n := by
  split_ifs
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [residueClass_apply_zero, zero_div, zero_div]
    · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hn)
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx

lemma apld_prime_part_eq (a : ZMod q) (x : ℝ) (n : ℕ) :
    (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x =
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n := by
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod q) = a
    · have hmem : n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := ⟨hp, hn⟩
      rw [if_pos hp, Set.indicator_of_mem hmem]
      simp [residueClass, Set.indicator, hn, vonMangoldt_apply_prime hp]
    · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hn h.2
      rw [if_pos hp, Set.indicator_of_notMem hmem]
      simp [residueClass, Set.indicator, hn]
  · have hmem : n ∉ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod q) = a}} := fun h => hp h.1
    rw [if_neg hp, Set.indicator_of_notMem hmem, zero_div]

end Formalism.HF.P


open Formalism.HF.P in
theorem Formalism.HF.apLogDensity : Formalism.HF.APLogDensity := by
  intro N _ a ha
  unfold Formalism.HF.LogDensity
  set P : ℝ → ℕ → ℝ := fun x n => (if n.Prime then residueClass a n else 0) / (n : ℝ) ^ x with hP
  set Q : ℝ → ℕ → ℝ := fun x n => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x with hQ
  have hPQ : ∀ x n, residueClass a n / (n : ℝ) ^ x = P x n + Q x n := by
    intro x n
    simp only [hP, hQ, ← add_div]
    congr 1
    split_ifs <;> simp
  have hPnn : ∀ x n, 0 ≤ P x n := by
    intro x n
    simp only [hP]
    refine div_nonneg ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) x)
    split_ifs
    · exact residueClass_nonneg a n
    · exact le_rfl
  have hQnn : ∀ x n, 0 ≤ Q x n := fun x n => apld_nonprime_nonneg a x n
  have hPs : ∀ x : ℝ, 1 < x → Summable (P x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hPnn x) (fun n => by rw [hPQ]; linarith [hQnn x n])
  have hQs : ∀ x : ℝ, 1 < x → Summable (Q x) := fun x hx =>
    (apld_summable a hx).of_nonneg_of_le (hQnn x) (fun n => by rw [hPQ]; linarith [hPnn x n])
  have hB : Summable fun n : ℕ => (if n.Prime then 0 else residueClass a n) / n :=
    summable_residueClass_non_primes_div a
  set B := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n with hBdef
  have hQle : ∀ x : ℝ, 1 < x → ∑' n, Q x n ≤ B := fun x hx =>
    (hQs x hx).tsum_le_tsum (fun n => apld_nonprime_le a hx.le n) hB
  have hsplit : ∀ x : ℝ, 1 < x →
      (x - 1) * (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ - (x - 1) * ∑' n, Q x n =
      (x - 1) * (∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) := by
    intro x hx
    have hsum : ∑' n, residueClass a n / (n : ℝ) ^ x = ∑' n, P x n + ∑' n, Q x n := by
      rw [← (hPs x hx).tsum_add (hQs x hx)]
      exact tsum_congr (hPQ x)
    have hPind : ∑' n, P x n = ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n :=
      tsum_congr (fun n => apld_prime_part_eq a x n)
    have hT := apld_tsum_residueClass_eq ha hx
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 hx.ne'
    rw [← hPind]
    have : ∑' n, P x n = (LFunctionResidueClassAux a x).re + (N.totient : ℝ)⁻¹ / (x - 1) - ∑' n, Q x n := by
      linarith
    rw [this]
    field_simp
  have h1 : Tendsto (fun x : ℝ => (x - 1) * (LFunctionResidueClassAux a x).re) (𝓝[>] 1) (𝓝 0) :=
    residue_class_l_function_tendsto a
  have hlin : Tendsto (fun x : ℝ ↦ x - 1) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ ↦ x - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun x : ℝ => (x - 1) * ∑' n, Q x n) (𝓝[>] 1) (𝓝 0) := by
    have hup : Tendsto (fun x : ℝ => (x - 1) * B) (𝓝[>] 1) (𝓝 0) := by
      simpa using hlin.mul_const B
    refine squeeze_zero' ?_ ?_ hup
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (tsum_nonneg (hQnn x))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_le_mul_of_nonneg_left (hQle x hx) (sub_nonneg.2 (le_of_lt hx))
  have hlim := (h1.add (tendsto_const_nhds (x := (N.totient : ℝ)⁻¹))).sub h3
  have e : (0 : ℝ) + (N.totient : ℝ)⁻¹ - 0 = 1 / (N.totient : ℝ) := by simp
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hsplit x hx
end
end

-- bundled from Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
section
open NumberField Polynomial Matrix

noncomputable section

namespace Formalism.HF.P

lemma quad_not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)

theorem quadDiscr_ne_one (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a)
    (h4 : a % 4 = 1) (h1 : a ≠ 1) : discr K = a := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
    exact this
  have htrq : ∀ q : ℚ, Algebra.trace ℚ K (algebraMap ℚ K q) = 2 * q := by
    intro q
    rw [Algebra.trace_algebraMap, hrank]; simp
  have htrlin : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K (algebraMap ℚ K q * z) =
      q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htrx : Algebra.trace ℚ K x = 0 := by
    have hnc : (X ^ 2 - C (a : ℚ)).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C _, coeff_sub, coeff_X_pow, coeff_C]; norm_num
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnc]; simp
  set ω : K := (1 + x) / 2 with hω
  have hω1 : ω = algebraMap ℚ K (1 / 2) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; ring
  have hω2 : ω * ω = algebraMap ℚ K ((1 + a) / 4) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; linear_combination (1 / 4 : K) * hx
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, htrq]; norm_num
  have htrω : Algebra.trace ℚ K ω = 1 := by
    rw [hω1, map_add (f := _), htrq, htrlin, htrx]; norm_num
  have htrωω : Algebra.trace ℚ K (ω * ω) = (1 + a) / 2 := by
    rw [hω2, map_add (f := _), htrq, htrlin, htrx]; ring
  have hdisc : Algebra.discr ℚ ![(1 : K), ω] = a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [htr1, htrω, htrωω]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, ?_, ?_⟩
    · monicity!
    · rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast, hω]
      linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  let B := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← hrank, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivFinOfCardEq hcard
  let B' : Module.Basis (Fin 2) ℤ (𝓞 K) := B.reindex e
  let Cb : Module.Basis (Fin 2) ℚ K := (integralBasis K).reindex e
  have hC : ∀ i, Cb i = ((B' i : 𝓞 K) : K) := by
    intro i; simp [Cb, B', B, integralBasis_apply]
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  let v : Fin 2 → 𝓞 K := ![1, ω']
  let P : Matrix (Fin 2) (Fin 2) ℤ := B'.toMatrix v
  have hv : ![(1 : K), ω] = Cb ᵥ* (P.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K) := by
    have h0 := B'.toMatrix_map_vecMul v
    funext j
    have hj := congrArg (fun w : Fin 2 → 𝓞 K => ((w j : 𝓞 K) : K)) h0
    have hvj : ((v j : 𝓞 K) : K) = ![(1 : K), ω] j := by
      fin_cases j <;> rfl
    rw [← hvj, ← hj]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hC, P]
  have key : (a : ℚ) = ((P.det : ℤ) : ℚ) ^ 2 * (discr K : ℚ) := by
    rw [← hdisc, hv, Algebra.discr_of_matrix_vecMul, coe_discr, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have key' : a = P.det ^ 2 * discr K := by exact_mod_cast key
  have hu : IsUnit P.det := hsf P.det ⟨discr K, by rw [key']; ring⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (rw [key', h]; ring)

end Formalism.HF.P

theorem Formalism.HF.quadDiscr : Formalism.HF.QuadDiscr := by
  intro K _ _ a x hx hadj hsf h4
  by_cases h1 : a = 1
  · subst h1
    have hx1 : x * x = 1 := by rw [← sq, hx]; simp
    have hbot : x ∈ (⊥ : IntermediateField ℚ K) := by
      rcases mul_self_eq_one_iff.1 hx1 with h | h
      · rw [h]; exact IntermediateField.one_mem _
      · rw [h]; exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
    have htop : (⊥ : IntermediateField ℚ K) = ⊤ := by
      rw [← hadj, eq_comm]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 hbot
    let e : ℚ ≃ₐ[ℚ] K := (IntermediateField.botEquiv ℚ K).symm.trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
    rw [← NumberField.discr_eq_discr_of_algEquiv ℚ e, NumberField.discr_rat]
  · exact Formalism.HF.P.quadDiscr_ne_one K a x hx hadj hsf h4 h1
end
end

