module

public import Mathlib

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent

open MvPowerSeries

variable {σ : Type}

variable {k : Type} [CommRing k]

variable [Algebra ℚ k]

private lemma coeff_XX_pow_lemma (d : ℕ) (e : Fin 2 →₀ ℕ) :
    coeff e ((X 0 + X 1 : MvPowerSeries (Fin 2) k) ^ d) =
      if e 0 + e 1 = d then ((d.choose (e 0) : ℕ) : k) else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_pow, map_sum]
  have key : ∀ m ∈ Finset.range (d + 1),
      coeff e ((X 0 : MvPowerSeries (Fin 2) k) ^ m * X 1 ^ (d - m) * (d.choose m : MvPowerSeries (Fin 2) k)) =
        if e 0 = m ∧ e 1 = d - m then (d.choose m : k) else 0 := by
    intro m _
    rw [← map_natCast (C : k →+* MvPowerSeries (Fin 2) k), coeff_mul_C, X_pow_eq, X_pow_eq,
      monomial_mul_monomial, coeff_monomial]
    have hiff : (e = Finsupp.single 0 m + Finsupp.single 1 (d - m)) ↔ (e 0 = m ∧ e 1 = d - m) := by
      constructor
      · rintro rfl
        simp
      · rintro ⟨h0, h1⟩
        ext i
        fin_cases i <;> simp [h0, h1]
    by_cases h : e 0 = m ∧ e 1 = d - m
    · rw [if_pos (hiff.2 h), if_pos h]
      simp
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, zero_mul]
  rw [Finset.sum_congr rfl key]
  by_cases hd : e 0 + e 1 = d
  · rw [if_pos hd, Finset.sum_eq_single (e 0)]
    · rw [if_pos ⟨rfl, by omega⟩]
    · intro m _ hm
      rw [if_neg]
      rintro ⟨h, _⟩
      exact hm h.symm
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_range] at hm
    rw [if_neg]
    rintro ⟨h0, h1⟩
    omega

private lemma coeff_substX_lemma_2 (i : Fin 2) (f : PowerSeries k) (e : Fin 2 →₀ ℕ) :
    coeff e (PowerSeries.subst (X i : MvPowerSeries (Fin 2) k) f) =
      if e = Finsupp.single i (e i) then PowerSeries.coeff (e i) f else 0 := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  simp_rw [coeff_X_pow]
  by_cases h : e = Finsupp.single i (e i)
  · rw [if_pos h, finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · rw [if_neg h]
    have hz : ∀ d : ℕ, (PowerSeries.coeff d f • if e = Finsupp.single i d then (1 : k) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]

theorem exp_biv :
    PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) =
      PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) := by
  ext e
  have hsum : PowerSeries.HasSubst (X 0 + X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have hL : coeff e (PowerSeries.subst (X (0 : Fin 2) + X 1 : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0 + e 1) (PowerSeries.exp k) * ((e 0 + e 1).choose (e 0) : k) := by
    rw [PowerSeries.coeff_subst hsum, finsum_eq_single _ (e 0 + e 1)]
    · rw [coeff_XX_pow_lemma, if_pos rfl, smul_eq_mul]
    · intro d hd
      rw [coeff_XX_pow_lemma, if_neg (fun h => hd h.symm), smul_zero]
  have hR : coeff e (PowerSeries.subst (X (0 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k) *
        PowerSeries.subst (X (1 : Fin 2) : MvPowerSeries (Fin 2) k) (PowerSeries.exp k)) =
      PowerSeries.coeff (e 0) (PowerSeries.exp k) * PowerSeries.coeff (e 1) (PowerSeries.exp k) := by
    rw [coeff_mul, Finset.sum_eq_single (Finsupp.single 0 (e 0), Finsupp.single 1 (e 1))]
    · rw [coeff_substX_lemma_2, coeff_substX_lemma_2, if_pos (by simp), if_pos (by simp)]
      simp
    · rintro ⟨p, q⟩ hpq hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      rw [coeff_substX_lemma_2, coeff_substX_lemma_2]
      by_cases h1 : p = Finsupp.single 0 (p 0)
      · by_cases h2 : q = Finsupp.single 1 (q 1)
        · exfalso
          apply hne
          have hq0 : q 0 = 0 := by
            rw [h2]
            simp
          have hp1 : p 1 = 0 := by
            rw [h1]
            simp
          have c0 := DFunLike.congr_fun hpq 0
          have c1 := DFunLike.congr_fun hpq 1
          simp only [Finsupp.coe_add, Pi.add_apply] at c0 c1
          rw [Prod.mk.injEq]
          constructor
          · rw [h1]
            congr 1
            omega
          · rw [h2]
            congr 1
            omega
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro h
      exfalso
      apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      ext i
      fin_cases i <;> simp
  rw [hL, hR, PowerSeries.coeff_exp, PowerSeries.coeff_exp, PowerSeries.coeff_exp,
    ← map_natCast (algebraMap ℚ k), ← map_mul, ← map_mul]
  congr 1
  have hle : e 0 ≤ e 0 + e 1 := Nat.le_add_right _ _
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((e 0 + e 1).choose (e 0) : ℚ) * ((e 0).factorial : ℚ) * ((e 1).factorial : ℚ) =
      ((e 0 + e 1).factorial : ℚ) := by
    exact_mod_cast h
  have hc : ((e 0 + e 1).choose (e 0) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hle).ne'
  have hf0 : ((e 0).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hf1 : ((e 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [← h']
  field_simp

theorem psubst_comp {τ υ : Type} (b : τ → MvPowerSeries υ k) (hb : HasSubst b)
    (a : MvPowerSeries τ k) (ha : constantCoeff a = 0) (f : PowerSeries k) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  have ha' : HasSubst (fun _ : Unit => a) := hasSubst_of_constantCoeff_zero (fun _ => ha)
  simp only [PowerSeries.subst]
  rw [subst_comp_subst_apply ha' hb]

theorem expS_add {τ : Type} (x y : MvPowerSeries τ k) (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) :
    PowerSeries.subst (x + y) (PowerSeries.exp k) =
      PowerSeries.subst x (PowerSeries.exp k) * PowerSeries.subst y (PowerSeries.exp k) := by
  have hb : HasSubst (![x, y] : Fin 2 → MvPowerSeries τ k) :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hx, hy])
  have h := congrArg (subst (![x, y] : Fin 2 → MvPowerSeries τ k)) (exp_biv (k := k))
  rw [psubst_comp _ hb (X 0 + X 1) (by simp), subst_mul hb, psubst_comp _ hb (X 0) (by simp),
    psubst_comp _ hb (X 1) (by simp)] at h
  simpa [subst_add hb, subst_X hb] using h

end Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open NumberField Module FractionalIdeal
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E]

theorem trace_sum (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ z := by
  rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from (eq_ratCast _ _).symm,
    trace_eq_sum_embeddings ℂ]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ (fun σ => rfl)

theorem emb_nonempty : Nonempty (E →+* ℂ) := by
  exact ⟨(IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom⟩

theorem eq_of_emb {a b : E} (h : ∀ σ : E →+* ℂ, σ a = σ b) : a = b := by
  obtain ⟨σ⟩ := emb_nonempty (E := E)
  exact σ.injective (h σ)

section Conj

variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj

theorem cj_add (a b : E) : cj (a + b) = cj a + cj b := eq_of_emb fun φ => by rw [hcj, map_add (f := _), star_add, map_add (f := _), hcj, hcj]

theorem cj_mul (a b : E) : cj (a * b) = cj a * cj b := eq_of_emb fun φ => by rw [hcj, map_mul, star_mul', map_mul, hcj, hcj]

theorem cj_one : cj 1 = 1 := eq_of_emb fun φ => by rw [hcj, map_one, star_one]

theorem cj_zero : cj 0 = 0 := eq_of_emb fun φ => by rw [hcj, map_zero, star_zero]

theorem cj_cj (a : E) : cj (cj a) = a := eq_of_emb fun φ => by rw [hcj, hcj, star_star]

def cjR : E →+* E where
  toFun := cj
  map_one' := cj_one hcj
  map_mul' := cj_mul hcj
  map_zero' := cj_zero hcj
  map_add' := cj_add hcj

theorem trace_cj (z : E) : Algebra.trace ℚ E (cj z) = Algebra.trace ℚ E z := by
  apply Rat.cast_injective (α := ℂ)
  rw [trace_sum, trace_sum]
  simp_rw [hcj]
  rw [← star_sum, ← trace_sum]
  exact map_ratCast (starRingEnd ℂ) _

theorem cj_integral (c : 𝓞 E) : ∃ c' : 𝓞 E, (c' : E) = cj c := by
  exact ⟨⟨cj c, c.isIntegral_coe.map (cjR hcj).toIntAlgHom⟩, rfl⟩

theorem cj_ratCast (q : ℚ) : cj (q : E) = q := eq_of_emb fun φ => by rw [hcj, map_ratCast]; exact map_ratCast (starRingEnd ℂ) q

theorem cj_smul (q : ℚ) (a : E) : cj (q • a) = q • cj a := by
  rw [Rat.smul_def, Rat.smul_def, cj_mul hcj, cj_ratCast hcj]

theorem cj_neg (a : E) : cj (-a) = -cj a := eq_of_emb fun φ => by rw [hcj, map_neg, star_neg, map_neg, hcj]

theorem exists_theta (hne : ∃ z : E, cj z ≠ z) :
    ∃ θ : 𝓞 E, (θ : E) ≠ 0 ∧ cj (θ : E) = -(θ : E) := by
  obtain ⟨z, hz⟩ := hne
  have hex : ∃ c : 𝓞 E, cj (c : E) ≠ c := by
    by_contra hall
    push_neg at hall
    apply hz
    let f : E →ₗ[ℚ] E :=
      { toFun := cj, map_add' := cj_add hcj, map_smul' := fun q a => cj_smul hcj q a }
    have hf : f = LinearMap.id := (integralBasis E).ext fun i => by
      show cj (integralBasis E i) = integralBasis E i
      rw [integralBasis_apply]
      exact hall _
    exact LinearMap.congr_fun hf z
  obtain ⟨c, hc⟩ := hex
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  have hθ : ((c - c' : 𝓞 E) : E) = (c : E) - cj (c : E) := by
    rw [← hc']
    first | rfl | (push_cast; rfl) | norm_cast
  refine ⟨c - c', ?_, ?_⟩
  · rw [hθ]
    exact sub_ne_zero.mpr (Ne.symm hc)
  · rw [hθ, sub_eq_add_neg, cj_add hcj, cj_neg hcj, cj_cj hcj]
    ring

end Conj

def ed (E : Type) [Field E] [NumberField E] : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

theorem tr_ed_eb (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (ed E i * integralBasis E j) = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E) (integralBasis E) i j
  rw [Algebra.traceForm_apply] at h
  exact h

theorem eb_repr (z : E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (ed E i * z) := by
  have h : (integralBasis E).coord i =
      (Algebra.trace ℚ E).comp (LinearMap.mulLeft ℚ (ed E i)) := (integralBasis E).ext fun j => by
    show (integralBasis E).repr (integralBasis E j) i = Algebra.trace ℚ E (ed E i * integralBasis E j)
    rw [Module.Basis.repr_self, tr_ed_eb, Finsupp.single_apply]
  exact LinearMap.congr_fun h z

theorem tr_ed_int (c : 𝓞 E) (i : Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (ed E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← eb_repr]
  have h := integralBasis_repr_apply E c i
  simpa using h


attribute [local instance] Classical.propDecidable

open scoped Classical in
theorem ortho (σ τ : E →+* ℂ) :
    ∑ i, σ (ed E i) * τ (integralBasis E i) = if σ = τ then 1 else 0 := by
  classical
  let P : Matrix (E →+* ℂ) (Free.ChooseBasisIndex ℤ (𝓞 E)) ℂ := Matrix.of fun ρ i => ρ (integralBasis E i)
  let Q : Matrix (Free.ChooseBasisIndex ℤ (𝓞 E)) (E →+* ℂ) ℂ := Matrix.of fun i ρ => ρ (ed E i)
  have hQP : Q * P = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Q, P, Matrix.of_apply, Matrix.one_apply]
    simp_rw [← map_mul]
    rw [← trace_sum, tr_ed_eb]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →+* ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, NumberField.Embeddings.card]
  have hPQ : P * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hQP
  have h := congrFun (congrFun hPQ τ) σ
  simp only [Matrix.mul_apply, P, Q, Matrix.of_apply, Matrix.one_apply] at h
  convert h using 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · exact if_congr eq_comm rfl rfl


abbrev Dinv (E : Type) [Field E] [NumberField E] : FractionalIdeal (𝓞 E)⁰ E :=
  FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)

theorem mem_Dinv {z : E} : z ∈ Dinv E ↔ ∀ c : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * c) = m := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)]
  constructor
  · intro h c
    obtain ⟨m, hm⟩ := h (c : E) ((FractionalIdeal.mem_one_iff _).mpr ⟨c, rfl⟩)
    exact ⟨m, by rw [← Algebra.traceForm_apply, ← hm, eq_intCast]⟩
  · intro h a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨m, hm⟩ := h c
    exact ⟨m, by rw [eq_intCast, Algebra.traceForm_apply]; exact hm.symm⟩

theorem ed_mem (i : Free.ChooseBasisIndex ℤ (𝓞 E)) : ed E i ∈ Dinv E := mem_Dinv.mpr fun c => ⟨_, tr_ed_int c i⟩

theorem cj_mem_Dinv {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
    {z : E} (hz : z ∈ Dinv E) : cj z ∈ Dinv E := by
  rw [mem_Dinv] at hz ⊢
  intro c
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  obtain ⟨m, hm⟩ := hz c'
  refine ⟨m, ?_⟩
  rw [← hm, hc', ← trace_cj hcj (z * cj c), cj_mul hcj, cj_cj hcj]

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

