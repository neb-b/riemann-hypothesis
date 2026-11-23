module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegKrull
section
namespace ReciprocityTheory.ChartRestriction.G.T0

namespace KrullColonIdeal

variable {R : Type*} [CommRing R]

def colonI (s c : R) : Ideal R where
  carrier := {r | r * c ∈ Ideal.span {s}}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [add_mul]
    exact Ideal.add_mem _ hx hy
  zero_mem' := by simp
  smul_mem' := by
    intro r x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    rw [mul_assoc]
    exact Ideal.mul_mem_left _ _ hx

theorem mem_colonI {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := Iff.rfl

theorem exists_prime_colon [IsNoetherianRing R] (s a : R) (ha : a ∉ Ideal.span {s}) :
    ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      ∀ q1 q2 : R, q1 * q2 ∈ colonI s b → q1 ∈ colonI s b ∨ q2 ∈ colonI s b := by
  classical
  have hS : ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      colonI s b = J} : Set (Ideal R)).Nonempty := ⟨colonI s a, a, ha, le_rfl, rfl⟩
  obtain ⟨M, hM, hmax⟩ : ∃ M ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)),
      ∀ I ∈ ({J : Ideal R | ∃ b : R, b ∉ Ideal.span {s} ∧
      colonI s a ≤ colonI s b ∧ colonI s b = J} : Set (Ideal R)), ¬ M < I := by
    first
    | exact set_has_maximal_iff_noetherian.mpr inferInstance _ hS
    | exact WellFounded.has_min (wellFounded_submodule_gt R R) _ hS
  obtain ⟨b, hb, hab, rfl⟩ := hM
  refine ⟨b, hb, hab, fun q1 q2 h => ?_⟩
  by_cases h1 : q1 ∈ colonI s b
  · exact Or.inl h1
  · right

    have hle : colonI s b ≤ colonI s (q1 * b) := by
      intro r hr
      rw [mem_colonI] at hr ⊢
      have e : r * (q1 * b) = q1 * (r * b) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ q1 hr
    have hnot : q1 * b ∉ Ideal.span {s} := fun h' => h1 (mem_colonI.2 h')
    have heq : colonI s b = colonI s (q1 * b) := by
      by_contra hne
      exact hmax _ ⟨q1 * b, hnot, hab.trans hle, rfl⟩ (lt_of_le_of_ne hle hne)
    rw [heq, mem_colonI]
    have h' := mem_colonI.1 h
    have e : q2 * (q1 * b) = q1 * q2 * b := by ring
    rw [e]
    exact h'

end KrullColonIdeal


open KrullColonIdeal in
theorem mem_of_mem_heightOne_localizations {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = x := open KrullColonIdeal in by
  classical

  obtain ⟨a, b, hb0, hxab⟩ : ∃ a b : R, b ≠ 0 ∧ x * algebraMap R K b = algebraMap R K a := by
    obtain ⟨⟨a, ⟨b, hb⟩⟩, hx'⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    refine ⟨a, b, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← hx']
    exact IsLocalization.mk'_spec K a ⟨b, hb⟩
  have hbK : algebraMap R K b ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective R K
    rw [h, map_zero]
  by_contra hne
  have ha : a ∉ Ideal.span {b} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    apply hne
    refine ⟨r, ?_⟩
    apply mul_right_cancel₀ hbK
    rw [hxab, ← hr, map_mul]
  obtain ⟨c, hc, hac, hprime⟩ := exists_prime_colon b a ha
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (Ideal.zero_mem _)
  have hbP : b ∈ colonI b c := mem_colonI.2 (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self b))
  have hPne : colonI b c ≠ ⊥ := by
    intro h
    have hb' := hbP
    rw [h, Ideal.mem_bot] at hb'
    exact hb0 hb'
  have hPprime : (colonI b c).IsPrime := by
    refine ⟨?_, fun h => hprime _ _ h⟩
    refine (Ideal.ne_top_iff_one _).2 (fun h1 => hc ?_)
    have h1' := mem_colonI.1 h1
    rwa [one_mul] at h1'

  have key : ∃ q0 ∈ colonI b c, ∃ u : R, u ∉ colonI b c ∧ u * b = q0 * c := by
    by_contra hcon
    push_neg at hcon
    apply hc
    have hint : IsIntegral R (algebraMap R K c / algebraMap R K b) := by
      refine isIntegral_of_smul_mem_submodule
        (Submodule.map (Algebra.linearMap R K) (colonI b c)) ?_ ?_ _ ?_
      · intro hbot
        have hmem : algebraMap R K b ∈ Submodule.map (Algebra.linearMap R K) (colonI b c) :=
          Submodule.mem_map_of_mem hbP
        rw [hbot, Submodule.mem_bot] at hmem
        exact hbK hmem
      · exact (IsNoetherian.noetherian (colonI b c)).map _
      · intro n hn
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hn
        obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
        have hvP : v ∈ colonI b c := by
          by_contra hv'
          exact hcon q hq v hv' hv
        refine Submodule.mem_map.2 ⟨v, hvP, ?_⟩
        have hv2 : algebraMap R K v * algebraMap R K b = algebraMap R K q * algebraMap R K c := by
          rw [← map_mul, ← map_mul, hv]
        simp only [Algebra.linearMap_apply, smul_eq_mul]
        first
        | (rw [div_mul_eq_mul_div, eq_div_iff hbK]; linear_combination hv2)
        | (field_simp; linear_combination hv2)
        | (field_simp; linear_combination -hv2)
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = algebraMap R K c / algebraMap R K b := by
      first
      | exact IsIntegrallyClosed.isIntegral_iff.1 hint
      | exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hrc : r * b = c := by
      apply IsFractionRing.injective R K
      rw [map_mul, hr]
      first
      | exact div_mul_cancel₀ _ hbK
      | field_simp
    exact Ideal.mem_span_singleton'.2 ⟨r, hrc⟩
  obtain ⟨q0, hq0, u, hu, huq⟩ := key
  have huP : ∀ q ∈ colonI b c, u * q ∈ Ideal.span {q0} := by
    intro q hq
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (mem_colonI.1 hq)
    refine Ideal.mem_span_singleton'.2 ⟨v, ?_⟩
    apply mul_right_cancel₀ hc0
    linear_combination (-v) * huq + u * hv

  have hmin : colonI b c ∈ (Ideal.span {q0}).minimalPrimes := by
    refine ⟨⟨hPprime, ?_⟩, fun Q hQ hQP => ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hq0
    · intro q hq
      have huq' : u * q ∈ Q := hQ.2 (huP q hq)
      rcases hQ.1.mem_or_mem huq' with h | h
      · exact absurd (hQP h) hu
      · exact h
  haveI : Submodule.IsPrincipal (Ideal.span {q0}) := ⟨⟨q0, rfl⟩⟩
  have hle1 : (colonI b c).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {q0}) _ hmin
  have hge1 : (1 : ℕ∞) ≤ (colonI b c).height := by
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hPne
  have hheight : (colonI b c).height = 1 := le_antisymm hle1 hge1
  obtain ⟨a', s', hs', hs'x⟩ := hx (colonI b c) hPprime hheight
  apply hs'
  apply hac
  rw [mem_colonI]
  refine Ideal.mem_span_singleton'.2 ⟨a', ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_mul, ← hs'x, ← hxab]
  ring

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceA
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MeasureTheory Module Submodule

theorem gtA_countable {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Countable (span ℤ (Set.range B)).toAddSubgroup := by
  have e : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)) =
      Set.range (fun c : Fin n → ℤ => ∑ i, c i • B i) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, Set.mem_range]
  have hc : ((span ℤ (Set.range B) : Submodule ℤ (Fin n → ℝ)) : Set (Fin n → ℝ)).Countable := by
    rw [e]
    exact Set.countable_range _
  exact hc.to_subtype

theorem gtA_mink_pi_lt {n : ℕ} (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (h : |(Matrix.of B).det| < t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ < t := by
  haveI := gtA_countable B
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.ball (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_ball (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_ball 0 ht, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _),
        ENNReal.ofReal_lt_ofReal_iff (by positivity), mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_lt_mul_of_pos_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_mink_pi_le {n : ℕ} (hn : 0 < n) (B : Basis (Fin n) ℝ (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) (h : |(Matrix.of B).det| ≤ t ^ n) :
    ∃ x ∈ span ℤ (Set.range B), x ≠ 0 ∧ ‖x‖ ≤ t := by
  haveI := gtA_countable B
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have fund := ZSpan.isAddFundamentalDomain B volume
  obtain ⟨x, hx0, hxs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (L := (span ℤ (Set.range B)).toAddSubgroup) fund (s := Metric.closedBall (0 : Fin n → ℝ) t) (fun y hy => by simpa using hy)
    (convex_closedBall (0 : Fin n → ℝ) t) (isCompact_closedBall (0 : Fin n → ℝ) t) (by
      have h2 : (2 : ENNReal) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [ZSpan.volume_fundamentalDomain B, Real.volume_pi_closedBall 0 ht.le, Module.finrank_fin_fun,
        Fintype.card_fin, h2, ← ENNReal.ofReal_mul (abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, mul_comm ((2 : ℝ) ^ n)]
      exact mul_le_mul_of_nonneg_right h (by positivity))
  refine ⟨x, x.2, fun h0 => hx0 (Subtype.ext h0), ?_⟩
  simpa using hxs

theorem gtA_norm_le_sqrt_mul (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
  rw [EuclideanSpace.norm_eq]
  have hM : ∀ i, ‖x i‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := fun i =>
    norm_le_pi_norm (EuclideanSpace.equiv (Fin n) ℝ x) i
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin n, ‖EuclideanSpace.equiv (Fin n) ℝ x‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact Finset.sum_le_sum fun i _ => by gcongr; exact hM i
    _ = Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem gtB_inner_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k, EuclideanSpace.equiv (Fin n) ℝ x k * EuclideanSpace.equiv (Fin n) ℝ y k := by
  first
    | simp [PiLp.inner_apply, mul_comm]
    | (rw [EuclideanSpace.inner_eq_star_dotProduct]; simp [dotProduct, mul_comm])

theorem gtB_nondeg (n : ℕ) : (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate := by
  show _ ∧ _
  constructor
  · intro x hx
    first
      | simpa using hx x
      | simpa [innerₗ_apply_apply] using hx x
  · intro y hy
    first
      | simpa using hy y
      | simpa [innerₗ_apply_apply] using hy y

theorem gtB_dual_short {n : ℕ} (hn : 0 < n) (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    ∃ y : EuclideanSpace ℝ (Fin n), y ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y (b j) = m) ∧
      ‖y‖ ≤ n / lam := by
  set e := EuclideanSpace.equiv (Fin n) ℝ with he
  set B := b.map e.toLinearEquiv with hBdef
  have hB : ∀ j, B j = e (b j) := fun j => by simp [B]
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hdet : (lam / Real.sqrt n) ^ n ≤ |(Matrix.of B).det| := by
    by_contra hlt
    push Not at hlt
    obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_lt B (by positivity) hlt
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
    have hex : e (∑ i, c i • b i) = ∑ i, c i • B i := by simp [hB, map_sum, map_zsmul]
    have hx'0 : (∑ i, c i • b i) ≠ 0 := by intro h; apply hx0; rw [← hex, h, map_zero]
    have h1 := hmin _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hx'0
    have h2 := gtA_norm_le_sqrt_mul n (∑ i, c i • b i)
    rw [hex] at h2
    have : Real.sqrt n * ‖∑ i, c i • B i‖ < lam := by
      calc _ < Real.sqrt n * (lam / Real.sqrt n) := mul_lt_mul_of_pos_left hxn hsq
        _ = lam := by field_simp
    linarith
  set c := LinearMap.BilinForm.dualBasis (innerₗ (EuclideanSpace ℝ (Fin n))) (gtB_nondeg n) b with hcdef
  have hc : ∀ i j, inner ℝ (c i) (b j) = if j = i then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left (gtB_nondeg n) b i j
    simpa using this
  set C := c.map e.toLinearEquiv with hCdef
  have hC : ∀ j, C j = e (c j) := fun j => by simp [C]
  have hCB : Matrix.of C * (Matrix.of B).transpose = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply, hB, hC]
    rw [← gtB_inner_eq, hc]
    simp [eq_comm]
  have hdetCB : (Matrix.of C).det * (Matrix.of B).det = 1 := by
    rw [← Matrix.det_transpose (Matrix.of B), ← Matrix.det_mul, hCB, Matrix.det_one]
  have hdetC : |(Matrix.of C).det| ≤ (Real.sqrt n / lam) ^ n := by
    have hpos : 0 < (lam / Real.sqrt n) ^ n := by positivity
    have h1 : |(Matrix.of C).det| * |(Matrix.of B).det| = 1 := by rw [← abs_mul, hdetCB, abs_one]
    have h2 : |(Matrix.of C).det| = |(Matrix.of B).det|⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h2, show (Real.sqrt n / lam) ^ n = ((lam / Real.sqrt n) ^ n)⁻¹ by
      rw [← inv_pow, inv_div]]
    exact inv_anti₀ hpos hdet
  obtain ⟨x, hxs, hx0, hxn⟩ := gtA_mink_pi_le hn C (by positivity) hdetC
  obtain ⟨k, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxs
  have hex : e (∑ i, k i • c i) = ∑ i, k i • C i := by simp [hC, map_sum, map_zsmul]
  refine ⟨∑ i, k i • c i, ?_, ?_, ?_⟩
  · intro h; apply hx0; rw [← hex, h, map_zero]
  · intro j
    refine ⟨k j, ?_⟩
    rw [sum_inner]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hc]
    simp
  · have h2 := gtA_norm_le_sqrt_mul n (∑ i, k i • c i)
    rw [hex] at h2
    calc _ ≤ _ := h2
      _ ≤ Real.sqrt n * (Real.sqrt n / lam) := mul_le_mul_of_nonneg_left hxn hsq.le
      _ = n / lam := by
        rw [← mul_div_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

end ReciprocityTheory.ChartRestriction.G.T0
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TransferenceB
section
namespace ReciprocityTheory.ChartRestriction.G.T0

open Module Submodule

theorem gtC_prim {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (b : Basis (Fin n) ℝ E) (y1 : E) (hy1 : y1 ≠ 0)
    (hint : ∀ j, ∃ m : ℤ, inner ℝ y1 (b j) = m) :
    ∃ y0 : E, ∃ xu ∈ span ℤ (Set.range b), y0 ≠ 0 ∧ (∀ j, ∃ m : ℤ, inner ℝ y0 (b j) = m) ∧
      ‖y0‖ ≤ ‖y1‖ ∧ inner ℝ y0 xu = 1 := by
  classical
  choose m hm using hint
  have hPI := IsPrincipalIdealRing.principal (Ideal.span (Set.range m))
  obtain ⟨g, hg⟩ := Submodule.IsPrincipal.principal (Ideal.span (Set.range m))
  have hgI : g ∈ Ideal.span (Set.range m) := by
    rw [hg]
    exact Submodule.mem_span_singleton_self g
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hgI
  simp only [smul_eq_mul] at hc
  have hdiv : ∀ j, ∃ a : ℤ, a * g = m j := by
    intro j
    have hj : m j ∈ Ideal.span (Set.range m) := Ideal.subset_span ⟨j, rfl⟩
    rw [hg] at hj
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hj
    exact ⟨a, by simpa using ha⟩
  choose a ha using hdiv
  have hne : ∃ j, m j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy1
    have h0 : ∀ x, inner ℝ y1 x = 0 := by
      intro x
      rw [← b.sum_repr x, inner_sum]
      simp [inner_smul_right, hm, hcon]
    exact inner_self_eq_zero.1 (h0 y1)
  have hg0 : g ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne
    exact hj (by rw [← ha j, mul_zero])
  have hgR : (g : ℝ) ≠ 0 := Int.cast_ne_zero.2 hg0
  refine ⟨(g : ℝ)⁻¹ • y1, ∑ i, c i • b i,
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, rfl⟩,
    smul_ne_zero (inv_ne_zero hgR) hy1, fun j => ⟨a j, ?_⟩, ?_, ?_⟩
  · rw [real_inner_smul_left, hm, ← ha j]
    push_cast
    field_simp
  · rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |(g : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hg0
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ h1)
  · rw [inner_sum]
    simp_rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, real_inner_smul_left, hm]
    have h2 : ∑ i, (c i : ℝ) * ((g : ℝ)⁻¹ * (m i : ℝ)) = (g : ℝ)⁻¹ * ((∑ i, c i * m i : ℤ) : ℝ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h2, hc]
    exact inv_mul_cancel₀ hgR

theorem gtD_lat {m : ℕ} (b : Basis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (y0 xu : EuclideanSpace ℝ (Fin (m + 1))) (hy0 : y0 ≠ 0) (hxu : xu ∈ span ℤ (Set.range b))
    (h1 : inner ℝ y0 xu = 1) (hint : ∀ j, ∃ k : ℤ, inner ℝ y0 (b j) = k) :
    ∃ bW : Basis (Fin m) ℝ (ℝ ∙ y0)ᗮ,
      (∀ x ∈ span ℤ (Set.range bW),
        ((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b)) ∧
      (∀ v ∈ span ℤ (Set.range b), ∃ p ∈ span ℤ (Set.range bW),
        (p : EuclideanSpace ℝ (Fin (m + 1))) = v - inner ℝ y0 v • xu) := by
  classical
  have hintL : ∀ v ∈ span ℤ (Set.range b), ∃ k : ℤ, inner ℝ y0 v = k := by
    intro v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv
    choose k hk using hint
    refine ⟨∑ i, c i * k i, ?_⟩
    rw [inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hk]
  have hPW : ∀ v : EuclideanSpace ℝ (Fin (m + 1)), v - inner ℝ y0 v • xu ∈ (ℝ ∙ y0)ᗮ := by
    intro v
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, real_inner_smul_right, h1,
      mul_one, sub_self]
  have hPL : ∀ v ∈ span ℤ (Set.range b), v - inner ℝ y0 v • xu ∈ span ℤ (Set.range b) := by
    intro v hv
    obtain ⟨k, hk⟩ := hintL v hv
    rw [hk, Int.cast_smul_eq_zsmul]
    exact sub_mem hv (Submodule.smul_mem _ k hxu)
  let K : Submodule ℤ (ℝ ∙ y0)ᗮ :=
    (span ℤ (Set.range b)).comap (((ℝ ∙ y0)ᗮ).subtype.restrictScalars ℤ)
  have hKmem : ∀ x : (ℝ ∙ y0)ᗮ,
      x ∈ K ↔ (x : EuclideanSpace ℝ (Fin (m + 1))) ∈ span ℤ (Set.range b) := fun x => Iff.rfl
  have : DiscreteTopology K := by
    let f : K → span ℤ (Set.range b) := fun x =>
      ⟨((x : (ℝ ∙ y0)ᗮ) : EuclideanSpace ℝ (Fin (m + 1))), (hKmem x).1 x.2⟩
    refine DiscreteTopology.of_continuous_injective (f := f)
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext hv)
  have : IsZLattice ℝ K := by
    refine ⟨eq_top_iff.2 fun w _ => ?_⟩
    have hw0 : inner ℝ y0 (w : EuclideanSpace ℝ (Fin (m + 1))) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 w.2
    have hw0' : ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j * inner ℝ y0 (b j) = 0 := by
      rw [← hw0]
      conv_rhs => rw [← b.sum_repr (w : EuclideanSpace ℝ (Fin (m + 1)))]
      rw [inner_sum]
      simp_rw [real_inner_smul_right]
    have hsum : w = ∑ j, b.repr (w : EuclideanSpace ℝ (Fin (m + 1))) j •
        (⟨b j - inner ℝ y0 (b j) • xu, hPW (b j)⟩ : (ℝ ∙ y0)ᗮ) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_sub, Finset.sum_sub_distrib]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, hw0', zero_smul, sub_zero, b.sum_repr]
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact (hKmem _).2 (hPL (b j) (Submodule.subset_span ⟨j, rfl⟩))
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hrank : Module.finrank ℤ K = m := by
    rw [ZLattice.rank ℝ K, Submodule.finrank_orthogonal_span_singleton (n := m) hy0]
  let bK : Basis (Fin m) ℤ K := Module.finBasisOfFinrankEq ℤ K hrank
  refine ⟨bK.ofZLatticeBasis ℝ K, ?_, ?_⟩
  · intro x hx
    rw [Basis.ofZLatticeBasis_span] at hx
    exact (hKmem x).1 hx
  · intro v hv
    refine ⟨⟨v - inner ℝ y0 v • xu, hPW v⟩, ?_, rfl⟩
    rw [Basis.ofZLatticeBasis_span]
    exact (hKmem _).2 (hPL v hv)

end ReciprocityTheory.ChartRestriction.G.T0
end

