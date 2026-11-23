module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandauSummableOfExpDirichletSeriesEntire
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordDivisible
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CoordDiv

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {c | ∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' := fun {a} ha v => neg_mem (ha v)

theorem algebraMap_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ intAdeles F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

theorem exists_of_mem (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAdeles F) :
    ∃ a : 𝓞 F, (a : F) = k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact ⟨a, ha⟩

theorem dvd_of_eq (x : 𝓞 F) (N : ℕ) (hN : 0 < N) (e : FiniteAdeleRing (𝓞 F) F)
    (he : e ∈ intAdeles F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = (N : FiniteAdeleRing (𝓞 F) F) * e) :
    ∃ a : 𝓞 F, x = (N : 𝓞 F) * a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e := by
    rw [div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN',
      map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_of_mem F _ (hk ▸ he)
  have hx : (x : F) = N * (a : F) := by
    rw [ha]
    field_simp
  exact ⟨a, by exact_mod_cast hx⟩

theorem int_dvd (z : ℤ) (N : ℕ) (a : 𝓞 F) (h : (z : 𝓞 F) = (N : 𝓞 F) * a) : (N : ℤ) ∣ z := by

  have h2 := congrArg (Algebra.norm ℤ) h
  rw [map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z,
    show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩

theorem coord_divisible : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (r : β → FiniteAdeleRing (𝓞 F) F) (N : ℕ), 0 < N → (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) → (∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v, (e : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) = (N : FiniteAdeleRing (𝓞 F) F) * e) → ∀ i, ∃ s : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ s = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c) ∧ r i = (N : FiniteAdeleRing (𝓞 F) F) * s := by
  intro F _ _ β _ ω r N hN hr hsum i
  obtain ⟨e, he, hsum⟩ := hsum
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have := (isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    rwa [map_natCast] at this
  have hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F :=
    fun j => algebraMap_mem F (ω j)
  have hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F := fun z => intCast_mem _ z

  choose z c hc hrc using fun j => hr j N hN
  have hc' : ∀ j, c j ∈ intAdeles F := hc

  have hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) =
      ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨a, ha⟩ := dvd_of_eq F (∑ j, z j • ω j) N hN
    (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F))
    (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by
      rw [hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrc j]
      ring)

  have hm : ∀ j, z j = N * ω.repr a j := by
    intro j
    have h1 := congrArg (fun y => ω.repr y j) ha
    have h2 : (N : 𝓞 F) * a = (N : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    simp only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
    simpa using h1
  have key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j) := by
    intro j
    rw [hrc j, hm j]
    push_cast
    ring
  refine ⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩
  intro M hM

  obtain ⟨z', c', hc'', hr'⟩ := hr i (M * N) (Nat.mul_pos hM hN)
  have hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F :=
    sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')
  obtain ⟨a', ha'⟩ := dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) =
        (z' : FiniteAdeleRing (𝓞 F) F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
    have e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c' := by
      rw [hr']
      ring
    rw [e1, e2, key i]
    push_cast
    ring)
  obtain ⟨t, ht⟩ := int_dvd F z' N a' ha'
  refine ⟨t, c', hc'', hu.mul_left_cancel ?_⟩
  rw [← key i, hr', ht]
  push_cast
  ring

end GlobalTheory.CoordDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EntriesBoundedOfConjSpanningBounded
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem entries_bounded_of_conj_spanning_bounded :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  intro ι _ _ σ _ g hg C
  have hmem : ∀ k l : ι, ∃ a : σ → ℂ, ∑ s, a s • g s = Matrix.single k l (1 : ℂ) := by
    intro k l
    have : Matrix.single k l (1 : ℂ) ∈ Submodule.span ℂ (Set.range g) := by
      rw [hg]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).1 this
  choose a ha using hmem
  set C₁ : ℝ := ∑ k, ∑ l, ∑ s, ‖a k l s‖ * |C| with hC₁
  refine ⟨max 1 ((Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι), ?_⟩
  intro P hP hb i k
  have hent : ∀ l j, ‖P i k * P⁻¹ l j‖ ≤ C₁ := by
    intro l j
    have h1 : P i k * P⁻¹ l j = ∑ s, a k l s * (P * g s * P⁻¹) i j := by
      have h2 : (P * Matrix.single k l (1 : ℂ) * P⁻¹) i j = P i k * P⁻¹ l j := by
        simp [Matrix.mul_apply, Matrix.single, ite_and]
      rw [← h2, ← ha k l, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    have h3 : ‖P i k * P⁻¹ l j‖ ≤ ∑ s, ‖a k l s‖ * |C| := by
      rw [h1]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hb s i j).trans (le_abs_self C)) (norm_nonneg _)
    refine h3.trans ?_
    calc ∑ s, ‖a k l s‖ * |C| ≤ ∑ l, ∑ s, ‖a k l s‖ * |C| :=
          Finset.single_le_sum (f := fun l => ∑ s, ‖a k l s‖ * |C|)
            (fun l _ => by positivity) (Finset.mem_univ l)
      _ ≤ C₁ :=
          Finset.single_le_sum (f := fun k => ∑ l, ∑ s, ‖a k l s‖ * |C|)
            (fun k _ => by positivity) (Finset.mem_univ k)
  have hdetinv : (P⁻¹).det = 1 := by
    rw [Matrix.det_nonsing_inv, hP]; simp
  have hdet := Matrix.det_le (A := P i k • P⁻¹) (abv := NormedField.toAbsoluteValue ℂ) (x := C₁)
    (fun l j => hent l j)
  rw [Matrix.det_smul, hdetinv, mul_one] at hdet
  have hdet' : ‖P i k‖ ^ Fintype.card ι ≤
      (Nat.factorial (Fintype.card ι)) • C₁ ^ Fintype.card ι := by
    rw [← norm_pow]; exact hdet
  have hN : Fintype.card ι ≠ 0 := (Fintype.card_pos_iff.2 ⟨i⟩).ne'
  rcases le_total ‖P i k‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  · exact ((le_self_pow₀ h hN).trans hdet').trans (le_max_right _ _)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EulerProductNeZeroOneOfEntire
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma neg_one_le_re_pow_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (k : ℕ) : -1 ≤ (c ^ k).re := by
  have h1 : ‖c ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have h2 := Complex.abs_re_le_norm (c ^ k)
  linarith [(abs_le.mp (h2.trans h1)).1]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ¬ Summable fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) := by
  intro h
  set f := fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) with hf
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one hc (k + 1)]) (by positivity)
  have hkey : ∀ k : ℕ, 3 / 2 * (1 / ((k : ℝ) + 1)) ≤ f k + f (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hn : ‖c ^ (k + 1)‖ ^ 2 ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    have hz : c ^ (2 * k + 1 + 1) = c ^ (k + 1) * c ^ (k + 1) := by ring
    have hsum : f k + f (2 * k + 1) = (3 + 2 * (c ^ (k + 1)).re +
        ((c ^ (k + 1)).re * (c ^ (k + 1)).re - (c ^ (k + 1)).im * (c ^ (k + 1)).im)) /
        ((k : ℝ) + 1) := by
      simp only [hf, hz, Complex.mul_re]
      push_cast
      field_simp
      ring
    rw [hsum, mul_one_div]
    exact (div_le_div_iff_of_pos_right hk).mpr (by nlinarith [sq_nonneg ((c ^ (k + 1)).re + 1 / 2)])
  have hs2 : Summable fun k : ℕ => f k + f (2 * k + 1) :=
    h.add (h.comp_injective (fun a b hab => by simpa using hab))
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    have h3 : Summable fun k : ℕ => 3 / 2 * (1 / ((k : ℝ) + 1)) :=
      hs2.of_nonneg_of_le (fun k => by positivity) hkey
    exact (summable_mul_left_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).mp h3
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ?_)
  simpa using hharm

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma norm_mul_natCast_cpow_neg_le {n : ℕ} (hn : 2 ≤ n) {c : ℂ} (hc : ‖c‖ ≤ 1) (s : ℂ) :
    ‖c * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  exact mul_le_of_le_one_left (by positivity) hc

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma natCast_rpow_neg_le_half {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    (n : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / n := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hn


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.conj_neg_log_euler_factor (n : ℕ) (hn : 2 ≤ n) (c : ℂ) (hc : ‖c‖ ≤ 1) (s : ℂ)
    (hs : 1 < s.re) :
    starRingEnd ℂ (-Complex.log (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s)))) =
      -Complex.log (1 - starRingEnd ℂ c * (n : ℂ) ^ (-s)) := by
  have hlt : ‖c * (n : ℂ) ^ (-(starRingEnd ℂ s))‖ < 1 :=
    ((norm_mul_natCast_cpow_neg_le hn hc (starRingEnd ℂ s)).trans
      (natCast_rpow_neg_le_half hn (by simpa using hs))).trans_lt (by norm_num)
  have hre : 0 < (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).re := by
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm (c * (n : ℂ) ^ (-(starRingEnd ℂ s)))]
  have harg : (1 - c * (n : ℂ) ^ (-(starRingEnd ℂ s))).arg ≠ Real.pi := fun h => by
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith
  have hconj : starRingEnd ℂ ((n : ℂ) ^ (-(starRingEnd ℂ s))) = (n : ℂ) ^ (-s) := by
    have := Complex.cpow_conj (n : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
    rw [map_neg] at this
    rw [this, Complex.conj_conj, Complex.conj_natCast]
  rw [map_neg, ← Complex.log_conj _ harg, map_sub, map_one, map_mul, hconj]


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.eulerProduct_ne_zero_one_of_entire : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z L : ℂ → ℂ, Differentiable ℂ Z → Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → (∀ s : ℂ, 1 < s.re → L s = Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))) → L 1 ≠ 0 := by
  intro ι N c hN hc hsum hne Z L hZ hL hZs hLs h1
  set L' : ℂ → ℂ := fun s => starRingEnd ℂ (L (starRingEnd ℂ s)) with hL'
  have hdL' : Differentiable ℂ L' := fun s => by
    have := (hL (starRingEnd ℂ s)).conj_conj
    simpa [hL', Function.comp_def] using this
  have hL'1 : L' 1 = 0 := by simp [hL', h1]
  have hds : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ (dslope f 1) := fun f hf =>
    differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
  have ha : ∀ p : ι × ℕ, 0 ≤ (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) := fun p =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one (hc p.1) (p.2 + 1)]) (by positivity)
  have key := _root_.GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s ^ 2 * dslope L 1 s * dslope L' 1 s) ha
    (fun p => mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by have := hN p.1; omega : 1 ≤ N p.1))))
    (((hZ.pow 2).mul (hds L hL)).mul (hds L' hdL')) (by
      intro s hs
      refine ⟨_, _root_.GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hL's : L' s = Complex.exp (∑' i, -Complex.log
          (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s))) := by
        simp only [hL']
        rw [hLs _ (by simpa using hs), ← Complex.exp_conj, Complex.conj_tsum]
        congr 1
        exact tsum_congr fun i => _root_.GlobalTheory.conj_neg_log_euler_factor (N i) (hN i) (c i) (hc i) s hs
      simp only [dslope_of_ne _ hs1, slope_def_field, h1, hL'1, sub_zero]
      rw [hZs s hs, hLs s hs, hL's, two_mul, Complex.exp_add, Complex.exp_add, Complex.exp_add]
      field_simp)
  obtain ⟨i⟩ := hne
  exact _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c i) (hc i)
    (((summable_prod_of_nonneg (fun p => ha p)).mp key).1 i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenNormsOfUnitNonsquare
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem evenNorms_of_unit_nonsquare {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, w (x - 1) < 1 → IsSquare x) (δ : K) (hδ : w δ = 1) (hn : ¬ IsSquare δ) :
    EvenNorms w δ := by
  have key : ∀ c : K, c ≠ 0 → ∃ n : ℤ, w c ^ 2 = WithZero.exp (2 * n) := by
    intro c hc
    have h0 : w c ≠ 0 := by simpa using hc
    refine ⟨WithZero.log (w c), ?_⟩
    rw [two_mul, WithZero.exp_add, WithZero.exp_log h0, sq]
  intro a b hab
  have ha2 : w (a ^ 2) = w a ^ 2 := map_pow _ _ _
  have hb2 : w (δ * b ^ 2) = w b ^ 2 := by rw [map_mul, hδ, one_mul, map_pow]
  rcases lt_trichotomy (w a) (w b) with h | h | h
  · have hb : b ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : w (a ^ 2) < w (δ * b ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_right hlt, hb2]
    exact key b hb
  · have ha : a ≠ 0 := by
      rintro rfl
      rcases hab with h' | h'
      · exact h' rfl
      · rw [map_zero] at h
        exact h' (by simpa using h.symm)
    have ha0 : w a ≠ 0 := by simpa using ha
    have hb : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact ha0 h
    have hle : w (a ^ 2 - δ * b ^ 2) ≤ w a ^ 2 := by
      refine (w.map_sub _ _).trans (max_le ha2.le ?_)
      rw [hb2, h]
    rcases hle.lt_or_eq with hlt | heq
    · exfalso
      apply hn
      have e : δ * (b / a) ^ 2 - 1 = -((a ^ 2 - δ * b ^ 2) / a ^ 2) := by
        field_simp; ring
      have hs : IsSquare (δ * (b / a) ^ 2) := by
        apply hsq
        rw [e, Valuation.map_neg, map_div₀, ha2, div_lt_one₀ (pow_pos (zero_lt_iff.2 ha0) 2)]
        exact hlt
      obtain ⟨r, hr⟩ := hs
      refine ⟨r * a / b, ?_⟩
      have : δ = (δ * (b / a) ^ 2) * (a / b) ^ 2 := by field_simp
      rw [this, hr]; ring
    · rw [heq]; exact key a ha
  · have ha : a ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : w (δ * b ^ 2) < w (a ^ 2) := by
      rw [ha2, hb2]; exact pow_lt_pow_left₀ h zero_le two_ne_zero
    rw [w.map_sub_eq_of_lt_left hlt, ha2]
    exact key a ha

theorem evenNorms_of_odd_place : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 →
    ∀ δ : v.adicCompletion F, Valued.v δ = 1 → ¬ IsSquare δ → EvenNorms Valued.v δ := by
  intro F _ _ v h2 δ hδ hn
  refine evenNorms_of_unit_nonsquare _ (fun x hx => ?_) δ hδ hn
  apply GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v x
  have : (4 : v.adicCompletion F) = 2 * 2 := by norm_num
  rw [this, map_mul, h2, one_mul]
  exact hx

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRoot
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_exp_two_mul_of_eq_sq {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) {u y : K}
    (hy : y ≠ 0) (h : w u = w (y ^ 2)) : ∃ n : ℤ, w u = WithZero.exp (2 * n) := by
  refine ⟨WithZero.log (w y), ?_⟩
  rw [h, map_pow, two_mul, WithZero.exp_add, WithZero.exp_log ((Valuation.ne_zero_iff w).mpr hy),
    sq]


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.evenNorms_one_add_four_mul :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 →
      (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) →
        _root_.GlobalTheory.QNorm.EvenNorms w (1 + 4 * ρ) := by
  intro K _ w ρ h2 hρ hroot a b hab
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    exact exists_exp_two_mul_of_eq_sq w ha (by congr 1; ring)
  · set t := (a - b) / (2 * b) with ht_def
    have hfac : a ^ 2 - (1 + 4 * ρ) * b ^ 2 = (2 * b) ^ 2 * (t ^ 2 + t - ρ) := by
      rw [ht_def]
      field_simp
      ring
    by_cases ht : w t ≤ 1
    · exact exists_exp_two_mul_of_eq_sq w (mul_ne_zero h2 hb)
        (by rw [hfac, map_mul, hroot t ht, mul_one])
    · push_neg at ht
      have ht0 : t ≠ 0 := by
        rintro h
        rw [h, map_zero] at ht
        exact not_lt_of_ge zero_le' ht
      have hlt : w (t - ρ) < w (t ^ 2) := by
        calc w (t - ρ) ≤ max (w t) (w ρ) := Valuation.map_sub w t ρ
          _ = w t := max_eq_left (hρ.trans ht.le)
          _ < w t * w t := lt_mul_self ht
          _ = w (t ^ 2) := by rw [map_pow, sq]
      have hval : w (t ^ 2 + t - ρ) = w (t ^ 2) := by
        rw [add_sub_assoc]
        exact Valuation.map_add_eq_of_lt_left w hlt
      refine exists_exp_two_mul_of_eq_sq w (y := 2 * b * t) (mul_ne_zero (mul_ne_zero h2 hb) ht0) ?_
      rw [hfac, map_mul, hval, ← map_mul]
      congr 1
      ring

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStable
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem IsPre.exists_group_range :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ →
      ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  intro ι _ _ Γ hΓ
  let H : Subgroup (Matrix.SpecialLinearGroup ι ℂ) :=
    { carrier := {g | (g : Matrix ι ι ℂ) ∈ Γ}
      one_mem' := hΓ.one_mem
      mul_mem' := fun {a b} ha hb => hΓ.mul_mem _ ha _ hb
      inv_mem' := fun {a} ha => hΓ.adj_mem _ ha }
  let ρ : H →* Matrix ι ι ℂ :=
    { toFun := fun g => ((g : Matrix.SpecialLinearGroup ι ℂ) : Matrix ι ι ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨H, inferInstance, ρ, ?_⟩
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro hg
    exact ⟨⟨⟨g, hΓ.det_eq g hg⟩, hg⟩, rfl⟩

end GlobalTheory.ClassFin
end

