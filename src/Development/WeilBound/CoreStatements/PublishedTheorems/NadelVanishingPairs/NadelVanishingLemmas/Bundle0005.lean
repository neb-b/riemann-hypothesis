module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsDerivationNonPthPower

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ChartFormsDifferentialClosed
section
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.chart_forms_differential_closed : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | exact _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionCartanFormula
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

private theorem dDR_iota_dlog_eq_zero (K : Type) [Field K] (u : Kˣ) :
    CechDR.dDR ℤ K (ExteriorAlgebra.ι K (dlog u)) = 0 := by
  have h1 : (ExteriorAlgebra.ι K (dlog u) : CechDR.DR ℤ K) =
      ((u : K)⁻¹) • CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) := by
    show ExteriorAlgebra.ι K (((u⁻¹ : Kˣ) : K) • KaehlerDifferential.D ℤ K (u : K)) = _
    rw [map_smul, Units.val_inv_eq_inv_val]
  rw [h1, CechDR.dDR_smul, CechDR.dDR_D, smul_zero, add_zero, Derivation.leibniz_inv, map_smul,
    smul_mul_assoc]
  have h2 : (CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) : CechDR.DR ℤ K) *
      CechDR.ι1 (KaehlerDifferential.D ℤ K (u : K)) = 0 := ExteriorAlgebra.ι_sq_zero _
  rw [h2, smul_zero]

private theorem dDR_prod_dlog_eq_zero_and_euler_contraction (K : Type) [Field K] {n : ℕ} (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K) (hθ : IsEulerContraction x i θ) (l : List (Fin n)) :
    CechDR.dDR ℤ K (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = 0 ∧
    CechDR.dDR ℤ K (θ (l.map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod) = 0 := by
  have d1 : CechDR.dDR ℤ K (1 : CechDR.DR ℤ K) = 0 := by
    have h := CechDR.dDR_algebraMap (R := ℤ) (B := K) 1
    rw [map_one, Derivation.map_one_eq_zero, map_zero] at h
    exact h
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    refine ⟨d1, ?_⟩
    rw [hθ.1, map_zero]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [CechDR.dDR_mul, ih.1, dDR_iota_dlog_eq_zero, mul_zero, zero_mul, add_zero]
    · rw [hθ.2.1, hθ.2.2 a]
      split_ifs
      · rw [one_mul, map_sub, CechDR.dDR_mul, ih.1, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, sub_self]
      · rw [zero_mul, zero_sub, map_neg, CechDR.dDR_mul, ih.2, dDR_iota_dlog_eq_zero, mul_zero, zero_mul,
          add_zero, neg_zero]

theorem euler_cartan_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n)
    (θ : abelian₂ K →ₗ[K] abelian₂ K), IsEulerContraction x i θ → ∀ (c : K) (e : Fin n → K) (I : Finset (Fin n)),
    dK c = ∑ j, e j • dlog (x j) →
    extD K (θ (c • logWedge x I)) + θ (extD K (c • logWedge x I)) = e i • logWedge x I := by
  intro K _ n x i θ hθ c e I hc
  obtain ⟨hd, hdθ⟩ := dDR_prod_dlog_eq_zero_and_euler_contraction K x i θ hθ (I.sort (· ≤ ·))
  have hω : logWedge x I =
      ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod := rfl
  rw [hω]
  generalize ((I.sort (· ≤ ·)).map (fun j => ExteriorAlgebra.ι K (dlog (x j)))).prod = ω at hd hdθ ⊢
  have hθc : θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c)) = e i • 1 := by
    have h : KaehlerDifferential.D ℤ K c = ∑ j, e j • dlog (x j) := hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h, map_sum, map_sum]
    simp only [map_smul, hθ.2.2, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [extD_apply]
  rw [map_smul θ, CechDR.dDR_smul, CechDR.dDR_smul, hd, hdθ]
  simp only [smul_zero, add_zero]
  show _ + θ (ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * ω) = _
  rw [hθ.2.1, hθc, smul_one_mul]
  show ExteriorAlgebra.ι K (KaehlerDifferential.D ℤ K c) * θ ω + (e i • ω - _) = _
  abel

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionChartForms
section
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.euler_contraction_chart_forms : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  first | exact @_root_.GlobalTheory.LogDR.chartForms_stable_euler | exact _root_.GlobalTheory.LogDR.chartForms_stable_euler | (intros; apply _root_.GlobalTheory.LogDR.chartForms_stable_euler <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KernelDifferentialPthPower
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem dK_eq_zero_imp_pow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K),
    dK f = 0 → ∃ g : K, f = g ^ p := by
  intro K _ p _ _ f hf
  by_contra hne
  push_neg at hne
  obtain ⟨D, hD⟩ := DerivExt.exists_derivation p f hne
  have h := D.liftKaehlerDifferential_comp_D f
  have h0 : (KaehlerDifferential.D ℤ K) f = 0 := hf
  rw [h0, map_zero, hD] at h
  exact zero_ne_one h

end GlobalTheory
end

