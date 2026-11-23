module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnfA
section
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] {lam : Measure V} [lam.IsAddHaarMeasure] {Λ : AddSubgroup V} [Countable Λ]
  {𝓖 : Set V}


omit [SecondCountableTopology V] in
theorem lintegral_fd_le (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (S : V → ℝ≥0∞)
    (hS : ∀ (ν : Λ) β, S (β + ν) = S β) {C : Set V} (hcov : ∀ β, ∃ ν : Λ, β + (ν : V) ∈ C) :
    ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in C, S β ∂lam := by
  rw [h𝓖.setLIntegral_eq_tsum' S C]
  have hsub : 𝓖 ⊆ ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖 := by
    intro β hβ
    obtain ⟨ν, hν⟩ := hcov β
    refine Set.mem_iUnion.2 ⟨-ν, ?_, hβ⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact hν
  calc ∫⁻ β in 𝓖, S β ∂lam ≤ ∫⁻ β in ⋃ ν : Λ, (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_mono_set hsub
    _ ≤ ∑' ν : Λ, ∫⁻ β in (ν +ᵥ C) ∩ 𝓖, S β ∂lam := lintegral_iUnion_le _ _
    _ = ∑' ν : Λ, ∫⁻ x in (ν +ᵥ C) ∩ 𝓖, S (-ν +ᵥ x) ∂lam := by
      refine tsum_congr fun ν => lintegral_congr fun x => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
      exact (hS (-ν) x).symm


omit [SecondCountableTopology V] in
theorem setIntegral_fd_eq_zero (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (g : V → ℂ)
    (hg : ∀ (ν : Λ) β, g (β + ν) = g β) (β₀ : V) (c : ℂ) (hc : c ≠ 1) (hβ₀ : ∀ β, g (β + β₀) = c * g β) :
    ∫ β in 𝓖, g β ∂lam = 0 := by
  have h1 : IsAddFundamentalDomain Λ ((-β₀) +ᵥ 𝓖) lam := h𝓖.vadd_of_comm (-β₀)
  have h2 : ∫ β in 𝓖, g β ∂lam = ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam := by
    rw [← (measurePreserving_vadd β₀ lam).setIntegral_image_emb (measurableEmbedding_const_vadd β₀)]
    congr 1
    rw [Set.image_vadd, vadd_vadd, add_neg_cancel, zero_vadd]
  have h3 : ∫ x in (-β₀) +ᵥ 𝓖, g (β₀ +ᵥ x) ∂lam = c * ∫ β in 𝓖, g β ∂lam := by
    have e : (fun x => g (β₀ +ᵥ x)) = fun x => c * g x := funext fun x => by
      rw [vadd_eq_add, add_comm, hβ₀]
    rw [e, h1.setIntegral_eq h𝓖 (fun ν x => by rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm, hg]),
      integral_const_mul]
  have h4 : (1 - c) * ∫ β in 𝓖, g β ∂lam = 0 := by
    rw [sub_mul, one_mul, ← h3, ← h2, sub_self]
  exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 (Ne.symm hc))

end PositivityTheory.SiegelWeilFormula.kunf

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.ExistsBetaPf
section
open Matrix

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem exists_beta_pf {K : Type} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : K) (he : e * e = 1)
    (hse : s e = e) (a c d' : Matrix (Fin n) (Fin n) K) (hc : c.det = 0) (hda : e • (c.map s)ᵀ * a + d' * c = 0)
    (T : Matrix (Fin n) (Fin n) K) (hT : Tᵀ = -(e • T.map s)) (hTd : T.det ≠ 0) :
    ∃ β₁ : Matrix (Fin n) (Fin n) K, β₁ᵀ = -(e • β₁.map s) ∧ c * β₁ * (e • (c.map s)ᵀ) = 0 ∧
      (∃ v w : Fin n → K, a * β₁ * (e • (c.map s)ᵀ) = Matrix.vecMulVec v w ∧ w ⬝ᵥ v = 0) ∧ (T * β₁).trace = 2 := by
  classical
  obtain ⟨u, hu0, hcu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hc
  have hTu : T *ᵥ u ≠ 0 := fun h0 => hTd (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu0, h0⟩)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hTu
  have hi' : (T *ᵥ u) i ≠ 0 := hi
  obtain ⟨y, hy⟩ : ∃ y : Fin n → K, y ⬝ᵥ (T *ᵥ u) = 1 :=
    ⟨Pi.single i ((T *ᵥ u) i)⁻¹, by rw [single_dotProduct, inv_mul_cancel₀ hi']⟩
  obtain ⟨su, hsu⟩ : ∃ w : Fin n → K, w = s ∘ u := ⟨_, rfl⟩
  obtain ⟨sy, hsy⟩ : ∃ w : Fin n → K, w = s ∘ y := ⟨_, rfl⟩
  have hcsu : c.map s *ᵥ su = 0 := by
    rw [hsu]
    ext j
    rw [← RingHom.map_mulVec, hcu]
    simp
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have hM : (e • (c.map s)ᵀ * a) *ᵥ u = 0 := by
    rw [eq_neg_of_add_eq_zero_left hda, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hcu,
      Matrix.mulVec_zero, neg_zero]
  have hM' : ((c.map s)ᵀ * a) *ᵥ u = 0 := by
    rw [Matrix.smul_mul, Matrix.smul_mulVec] at hM
    exact (smul_eq_zero.mp hM).resolve_left he0
  have key : (c.map s *ᵥ y) ⬝ᵥ (a *ᵥ u) = y ⬝ᵥ (((c.map s)ᵀ * a) *ᵥ u) := by
    simp only [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
  refine ⟨vecMulVec u y - e • vecMulVec sy su, ?_, ?_, ?_, ?_⟩
  · subst hsu hsy
    ext j k
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.sub_apply, Matrix.vecMulVec_apply, Function.comp_apply, smul_eq_mul, map_sub, map_mul, hs, hse]
    linear_combination (-(y j * u k)) * he
  · simp [Matrix.mul_sub, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, hcu, hcsu]
  · refine ⟨a *ᵥ u, e • (c.map s *ᵥ y), ?_, ?_⟩
    · simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
        hcsu]
    · rw [smul_dotProduct, key, hM', dotProduct_zero, smul_zero]
  · have h1 : (T *ᵥ u) ⬝ᵥ y = 1 := by rw [dotProduct_comm, hy]
    have hsy1 : sy ⬝ᵥ (T.map s *ᵥ su) = 1 := by
      have hmv : T.map s *ᵥ su = s ∘ (T *ᵥ u) := by
        rw [hsu]
        ext j
        exact (RingHom.map_mulVec s T u j).symm
      rw [hmv, hsy, ← RingHom.map_dotProduct, hy, map_one]
    have h2 : (T *ᵥ sy) ⬝ᵥ su = -e := by
      calc (T *ᵥ sy) ⬝ᵥ su = sy ⬝ᵥ (Tᵀ *ᵥ su) := by
            rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
        _ = sy ⬝ᵥ ((-(e • T.map s)) *ᵥ su) := by rw [hT]
        _ = -e * (sy ⬝ᵥ (T.map s *ᵥ su)) := by
            rw [Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_neg, dotProduct_smul,
              smul_eq_mul]
            ring
        _ = -e := by rw [hsy1, mul_one]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_vecMulVec, Matrix.trace_vecMulVec, h1, h2, smul_eq_mul]
    linear_combination he

end PositivityTheory.SiegelWeilFormula.kunf
end

