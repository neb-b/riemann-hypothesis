module

public import Mathlib

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HaarIcc
section
noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

theorem haar_Icc (m : Measure ℝ) (hinv : ∀ c : ℝ, ∀ S : Set ℝ, MeasurableSet S → m ((fun x => c + x) ⁻¹' S) = m S)
    (a0 ℓ : ℝ) (hℓ : 0 < ℓ) (hfin : m (Set.Icc a0 (a0 + ℓ)) ≠ ⊤) :
    ∃ R : ℝ, ∀ a c : ℝ, a ≤ c → (m (Set.Icc a c)).toReal = R * (c - a) := by
  have hI : m.IsAddLeftInvariant := ⟨fun c => Measure.ext fun S hS => by
    rw [Measure.map_apply (measurable_const_add c) hS]; exact hinv c S hS⟩
  have hfin' : ∀ a, m (Set.Icc a (a + ℓ)) < ⊤ := by
    intro a
    have h := hinv (a0 - a) (Set.Icc a0 (a0 + ℓ)) measurableSet_Icc
    rw [Set.preimage_const_add_Icc] at h
    have e1 : a0 - (a0 - a) = a := by ring
    have e2 : a0 + ℓ - (a0 - a) = a + ℓ := by ring
    rw [e1, e2] at h
    rw [h]; exact lt_top_iff_ne_top.2 hfin
  have hL : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Set.Icc (x - ℓ / 2) (x - ℓ / 2 + ℓ),
    Icc_mem_nhds (by linarith) (by linarith), hfin' _⟩⟩
  have hm := Measure.isAddLeftInvariant_eq_smul m (volume : Measure ℝ)
  refine ⟨(Measure.addHaarScalarFactor m volume : ℝ), fun a c hac => ?_⟩
  have h2 := congrArg (fun μ : Measure ℝ => μ (Set.Icc a c)) hm
  rw [h2, Measure.smul_apply, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.2 hac)]

end UpperTheory.Esk.UnipotentIntegrandLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IntegralProdLog
section
noncomputable section
open MeasureTheory

namespace UpperTheory.Esk.UnipotentIntegrandLemmas

theorem integral_prod_log {I : Type} [Fintype I] [Nontrivial I] (φ : I → ℝ → ℂ)
    (h : ∀ v, Integrable (φ v) ∧ Integrable (fun x => (Real.log (1 + x ^ 2) : ℂ) * φ v x) ∧ ∫ x, φ v x = 0)
    (R C : ℝ) :
    ∫ x : I → ℝ, (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ) = 0 := by
  classical
  set ψ : I → I → ℝ → ℂ := fun w v t =>
    (if v = w then (Real.log (1 + t ^ 2) : ℂ) else 1) * φ v t with hψ
  have hψprod : ∀ (w : I) (x : I → ℝ),
      ∏ v, ψ w v (x v) = (Real.log (1 + x w ^ 2) : ℂ) * ∏ v, φ v (x v) := by
    intro w x
    simp only [hψ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hψint : ∀ w v, Integrable (ψ w v) := by
    intro w v
    by_cases hv : v = w
    · simpa [hψ, hv] using (h w).2.1
    · simpa [hψ, hv] using (h v).1
  have hP : Integrable (fun x : I → ℝ => ∏ v, φ v (x v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => (h v).1)
  have hψP : ∀ w, Integrable (fun x : I → ℝ => ∏ v, ψ w v (x v)) := by
    intro w
    rw [volume_pi]
    exact Integrable.fintype_prod (fun v => hψint w v)
  have hφzero : ∫ x : I → ℝ, ∏ v, φ v (x v) = 0 := by
    obtain ⟨v, -, -⟩ := exists_pair_ne I
    rw [integral_fintype_prod_volume_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (h v).2.2
  have hψzero : ∀ w, ∫ x : I → ℝ, ∏ v, ψ w v (x v) = 0 := by
    intro w
    obtain ⟨v, hv⟩ := exists_ne w
    rw [integral_fintype_prod_volume_eq_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simpa [hψ, hv] using (h v).2.2
  have key : ∀ x : I → ℝ,
      (∏ v, φ v (x v)) * ((R * (C + ∑ v, Real.log (1 + x v ^ 2)) : ℝ) : ℂ)
        = (R * C : ℂ) * ∏ v, φ v (x v) + ∑ w, (R : ℂ) * ∏ v, ψ w v (x v) := by
    intro x
    simp only [hψprod]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  simp_rw [key]
  rw [integral_add (hP.const_mul _) (integrable_finsetSum _ fun w _ => (hψP w).const_mul _),
    integral_const_mul, hφzero,
    integral_finsetSum _ fun w _ => (hψP w).const_mul _]
  simp [integral_const_mul, hψzero]

end UpperTheory.Esk.UnipotentIntegrandLemmas
end
end

