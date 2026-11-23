module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallyMapMemMaximalCompactGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private lemma val_le_one_ae (E : Type) [Field E] [NumberField E] (e : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) e) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) e).eventually_cofinite_notMem] with w hw
  have h : ¬ 1 < w.valuation E e := hw
  have h' : Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  rw [h']
  exact not_lt.mp h

private lemma mem_GLint {n : ℕ} {L : Type} [Field L] (O : Subring L) (g : GL (Fin n) L)
    (h₁ : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h₂ : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h₁ i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h₂ i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := hinj (by
    show (A * B).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have hBA : B * A = 1 := hinj (by
    show (B * A).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  rfl

theorem UpperTheory.eventually_map_mem_maximalCompactGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite,
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ n δ
  have h₁ : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      Valued.v (algebraMap E (w.adicCompletion E) ((δ : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 :=
    eventually_all.2 fun i => eventually_all.2 fun j => val_le_one_ae E _
  have h₂ : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      Valued.v (algebraMap E (w.adicCompletion E)
        (((δ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 :=
    eventually_all.2 fun i => eventually_all.2 fun j => val_le_one_ae E _
  filter_upwards [h₁, h₂] with w hw₁ hw₂
  refine mem_GLint (Ov E w) _ (fun i j => ?_) (fun i j => ?_)
  · exact hw₁ i j
  · rw [← map_inv]
    exact hw₂ i j
end

-- bundled from Development.AutomorphicArithmetic.UnitaryInvolutions.EventuallySeparableOfIntegralModel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private theorem coeff_mem_eventually {E : Type} [Field E] [NumberField E] (R : E[X]) :
    ∀ᶠ w : Pl E in cofinite, ∀ n, algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w := by
  have h : ∀ᶠ w : Pl E in cofinite, ∀ n ∈ R.support,
      algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w := by
    refine (Filter.eventually_all_finset _).2 fun n _ => ?_
    filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) (R.coeff n)).compl_mem_cofinite] with w hw
    have hv : Valued.v (algebraMap E (w.adicCompletion E) (R.coeff n)) = w.valuation E (R.coeff n) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (R.coeff n)
    have hle : Valued.v (algebraMap E (w.adicCompletion E) (R.coeff n)) ≤ 1 :=
      hv.trans_le (not_lt.mp hw)
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hle
  filter_upwards [h] with w hw n
  by_cases hn : n ∈ R.support
  · exact hw n hn
  · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
    exact zero_mem _

private theorem exists_lift {E : Type} [Field E] [NumberField E] (w : Pl E) (R : E[X])
    (h : ∀ n, algebraMap E (w.adicCompletion E) (R.coeff n) ∈ Ov E w) :
    ∃ R₀ : (Ov E w)[X], R₀.map (Ov E w).subtype = R.map (algebraMap E (w.adicCompletion E)) := by
  have hl : R.map (algebraMap E (w.adicCompletion E)) ∈ Polynomial.lifts (Ov E w).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact ⟨⟨_, h n⟩, rfl⟩
  exact (Polynomial.mem_lifts _).1 hl

theorem UpperTheory.eventually_separable_of_integral_model :
    ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable → ∀ᶠ w : Pl E in cofinite,
        ∀ Q : (Ov E w)[X], Q.map (Ov E w).subtype = P.map (algebraMap E (w.adicCompletion E)) → Q.Separable := by
  intro E _ _ P hP
  obtain ⟨a, b, hab⟩ := hP
  filter_upwards [coeff_mem_eventually a, coeff_mem_eventually b] with w ha hb Q hQ
  obtain ⟨a₀, ha₀⟩ := exists_lift w a ha
  obtain ⟨b₀, hb₀⟩ := exists_lift w b hb
  refine ⟨a₀, b₀, Polynomial.map_injective (Ov E w).subtype Subtype.val_injective ?_⟩
  have hd : (derivative Q).map (Ov E w).subtype =
      (derivative P).map (algebraMap E (w.adicCompletion E)) := by
    rw [← Polynomial.derivative_map, hQ, Polynomial.derivative_map]
  have := congrArg (Polynomial.map (algebraMap E (w.adicCompletion E))) hab
  simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_one] at this ⊢
  rw [ha₀, hb₀, hQ, hd, this]
end

