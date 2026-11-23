module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LLower

theorem tsum_one_div_rpow_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ σ ≤ σ / (σ - 1) := by
  have hσ0 : 0 < σ := by linarith
  have anti : AntitoneOn (fun t : ℝ => t ^ (-σ)) (Set.Ici ((1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici, Nat.cast_one] at hx hy
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hxy (by linarith)
  have integ : IntegrableOn (fun t : ℝ => t ^ (-σ)) (Set.Ioi ((1 : ℕ) : ℝ)) := by
    simpa using integrableOn_Ioi_rpow_of_lt (by linarith : -σ < -1) zero_lt_one
  have nonneg : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ (fun t : ℝ => t ^ (-σ)) t := by
    intro t ht
    simp only [Set.mem_Ioi, Nat.cast_one] at ht
    exact Real.rpow_nonneg (by linarith) _
  have key := anti.tsum_comp_add_le_integral 1 integ nonneg
  have hI : ∫ t in Set.Ioi ((1 : ℕ) : ℝ), t ^ (-σ) = 1 / (σ - 1) := by
    rw [Nat.cast_one, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have : σ - 1 ≠ 0 := by linarith
    have : -σ + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hI] at key
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ σ) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)
    simpa [Nat.cast_add, Nat.cast_one] using this
  rw [hs.tsum_eq_zero_add]
  have heq : ∀ n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) + 1) ^ σ = ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by
    intro n
    rw [Real.rpow_neg (by positivity), one_div]
    push_cast
    ring_nf
  simp only [heq] at *
  have h0 : (1 : ℝ) / ((0 : ℕ) + 1 : ℝ) ^ σ = 1 := by simp
  rw [h0]
  have : σ / (σ - 1) = 1 + 1 / (σ - 1) := by
    have : σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [this]
  linarith

theorem norm_LSeries_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ s.re / (s.re - 1) := by
  have hσ : 1 < s.re := hs
  have hg : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s.re) (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ s.re) := by
    have hsum := Real.summable_one_div_nat_rpow.mpr hσ
    have := hsum.hasSum
    rw [hsum.tsum_eq_zero_add] at this
    simpa [Real.zero_rpow (by linarith : s.re ≠ 0)] using this
  refine (tsum_of_norm_bounded hg fun n => ?_).trans (tsum_one_div_rpow_le hσ)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · subst hn
    simp [Real.zero_rpow (by linarith : s.re ≠ 0)]
  · have hpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
    exact div_le_div_of_nonneg_right (hf n) hpos.le

theorem norm_LFunction_ge (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 < s.re) : (s.re - 1) / s.re ≤ ‖LFunction χ s‖ := by
  have hre : 1 < s.re := hs
  have hσ : 0 < s.re := by linarith
  have hprod := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hb : ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ ≤ s.re / (s.re - 1) := by
    refine norm_LSeries_le (fun n => ?_) hre
    rw [norm_mul]
    have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have h2 : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    calc ‖χ n‖ * ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hn : ‖LSeries (fun n => (χ n : ℂ)) s‖ * ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖ = 1 := by
    have hprod' : LSeries (fun n => (χ n : ℂ)) s * LSeries (fun n => χ n * (moebius n : ℂ)) s = 1 :=
      hprod
    rw [← norm_mul, hprod', norm_one]
  have hd : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ hσ]
  have hA : 0 ≤ ‖LSeries (fun n => (χ n : ℂ)) s‖ := norm_nonneg _
  calc s.re - 1 = (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ *
        ‖LSeries (fun n => χ n * (moebius n : ℂ)) s‖) := by rw [hn, mul_one]
    _ ≤ (s.re - 1) * (‖LSeries (fun n => (χ n : ℂ)) s‖ * (s.re / (s.re - 1))) := by
        gcongr
    _ = ‖LSeries (fun n => (χ n : ℂ)) s‖ * s.re := by
        field_simp

end GlobalTheory.LLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationIntegerLeOne
section
universe u_1 u_2

namespace GlobalTheory.UnitDenominatorValuation

open NumberField
open scoped nonZeroDivisors

theorem valuation_integer_le_one {E : Type u_1} {Ω : Type u_2} [Field E] [NumberField E]
    [Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) (a : 𝓞 E) :
    A.valuation (ι (a : E)) ≤ 1 := by

  have hZ : IsIntegral ℤ (ι (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hZ.tower_top (A := A))
  rw [← hy]
  exact A.valuation_le_one y

theorem exists_unit_denominator {E : Type u_1} {Ω : Type u_2} [inst : Field E] [NumberField E]
    [inst_2 : Field Ω] (ι : E →+* Ω) (A : ValuationSubring Ω) {x : E}
    (hx : A.valuation (ι x) ≤ 1) :
    ∃ (s : 𝓞 E) (t : 𝓞 E), A.valuation (ι (s : E)) = 1 ∧ (s : E) * x = (t : E) := by
  classical
  by_contra hne
  push Not at hne

  let P : Submodule (𝓞 E) E :=
    { carrier := {u | A.valuation (ι u) < 1}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at hu hv ⊢
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hu hv)
      zero_mem' := by simp
      smul_mem' := fun r u hu => by
        simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul] at hu ⊢
        calc A.valuation (ι (algebraMap (𝓞 E) E r)) * A.valuation (ι u)
            ≤ 1 * A.valuation (ι u) := mul_le_mul' (valuation_integer_le_one ι A r) le_rfl
          _ < 1 := by rwa [one_mul] }

  let J : FractionalIdeal (𝓞 E)⁰ E := 1 ⊔ FractionalIdeal.spanSingleton _ x
  have h1J : (1 : E) ∈ J := (le_sup_left : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ J)
    (FractionalIdeal.one_mem_one _)
  have hxJ : x ∈ J := (le_sup_right : FractionalIdeal.spanSingleton _ x ≤ J)
    (FractionalIdeal.mem_spanSingleton_self _ x)
  have hJ : J ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at h1J
    exact one_ne_zero h1J

  have hJle : ∀ z ∈ (J : Submodule (𝓞 E) E), A.valuation (ι z) ≤ 1 := by
    intro z hz
    rw [FractionalIdeal.coe_sup, Submodule.mem_sup] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨b', rfl⟩ := (FractionalIdeal.mem_spanSingleton _).mp hb
    rw [map_add (f := _)]
    refine le_trans (Valuation.map_add _ _ _) (max_le (valuation_integer_le_one ι A a') ?_)
    rw [Algebra.smul_def, map_mul, map_mul]
    calc A.valuation (ι (algebraMap (𝓞 E) E b')) * A.valuation (ι x) ≤ 1 * 1 :=
          mul_le_mul' (valuation_integer_le_one ι A b') hx
      _ = 1 := one_mul 1

  have hinv : ∀ y ∈ ((J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E),
      A.valuation (ι y) < 1 := by
    intro y hy
    have hy1 := (FractionalIdeal.mem_inv_iff hJ).mp hy 1 h1J
    have hyx := (FractionalIdeal.mem_inv_iff hJ).mp hy x hxJ
    rw [mul_one] at hy1
    obtain ⟨s, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp hy1
    obtain ⟨t, ht⟩ := (FractionalIdeal.mem_one_iff _).mp hyx
    refine lt_of_le_of_ne (valuation_integer_le_one ι A s) fun h => hne s t h ?_
    exact ht.symm
  have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) ≤ P := by
    rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.mpr fun z hz y hy => ?_
    show A.valuation (ι (z * y)) < 1
    rw [map_mul, map_mul]
    calc A.valuation (ι z) * A.valuation (ι y) ≤ 1 * A.valuation (ι y) :=
          mul_le_mul' (hJle z hz) le_rfl
      _ < 1 := by rw [one_mul]; exact hinv y hy
  rw [mul_inv_cancel₀ hJ] at hle
  have h1 : A.valuation (ι 1) < 1 := hle (FractionalIdeal.one_mem_one _)
  simp at h1

end GlobalTheory.UnitDenominatorValuation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedFejerPositivity
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem normSq_geomSum_le_fejer (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by
  have hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re
      = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]
      ring
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j
        = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ']
    have h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re
        = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re
          + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      · push_cast; ring
    have h3 := hre (J + 1)
    have hw2 : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg w
      nlinarith
    rw [h2]
    set S := ∑ j ∈ Finset.range (J + 1), w ^ j
    rw [h1] at h3 ⊢
    have h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S
        + 2 * (w * S + 1).re - 1 := by
      rw [Complex.normSq_add, map_mul]
      simp
      ring
    have h5 := Complex.normSq_nonneg S
    rw [h4, h3]
    push_cast
    nlinarith

theorem fejer_re_ge (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    -(1 / 2) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
  have h := normSq_geomSum_le_fejer w hw J
  have h0 := Complex.normSq_nonneg (∑ j ∈ Finset.range (J + 1), w ^ j)
  have hJ : (0 : ℝ) < J + 1 := by positivity
  have h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
      = (∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re) / (J + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [h1, le_div_iff₀ hJ]
  linarith

theorem sum_fejer_weights (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) = (J : ℝ) / 2 := by
  have h : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  have hJ : (0 : ℝ) < J + 1 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, h]
  simp
  field_simp
  ring

theorem weighted_fejer_split (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (θ * I)) ^ j).re) / 2
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (-(θ * I))) ^ j).re) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

theorem weighted_fejer_positivity : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  intro J θ
  have n1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have n2 : ‖Complex.exp (-(θ * I))‖ = 1 := by
    rw [Complex.exp_neg, norm_inv, n1, inv_one]
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [weighted_fejer_split]
    have a := fejer_re_ge w hw J
    have b := fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J
    have c := fejer_re_ge (w * Complex.exp (-(θ * I)))
      (by rw [norm_mul, n2, mul_one]; exact hw) J
    linarith
  · rw [weighted_fejer_split]
    have a := fejer_re_ge (Complex.exp (θ * I)) n1.le J
    have b := fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I))
      (by rw [norm_mul, n1, mul_one]) J
    have c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [c]
    simp only [one_pow, Complex.one_re, mul_one]
    rw [sum_fejer_weights]
    linarith

end GlobalTheory
end

