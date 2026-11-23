module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DetLowUni

@[expose] public section

noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

theorem eventually_not_mem_of_finite {F : Set ℂ} (hF : F.Finite) : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ∉ F := by
  have h1 : ∀ᶠ x in 𝓝 (0 : ℂ), x ∉ F \ {0} :=
    (hF.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx hx0
  exact fun hxF => hx ⟨hxF, hx0⟩

theorem det_add_smul_eventually {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (A + x • (1 : Matrix (Fin k) (Fin k) ℂ)).det ≠ 0 := by
  have hp : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  filter_upwards [eventually_not_mem_of_finite (Polynomial.finite_setOfPred_isRoot hp)] with x hx
  intro h0
  apply hx
  show Polynomial.IsRoot _ x
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply, sub_neg_eq_add, add_comm,
    ← Matrix.smul_one_eq_diagonal]
  exact h0

private theorem exists_LU_for_dense : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ),
    (∀ k (hk : k < n), (g.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0) →
    ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g = L * U := by
  intro n
  induction n with
  | zero =>
    intro g _
    exact ⟨1, g, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, by simp⟩
  | succ n ih =>
    intro g hg
    let A : Matrix (Fin n) (Fin n) ℂ := g.submatrix Fin.castSucc Fin.castSucc
    have hAk : ∀ k (hk : k < n), (A.submatrix (Fin.castLE hk.le) (Fin.castLE hk.le)).det ≠ 0 := by
      intro k hk
      exact hg k (Nat.lt_succ_of_lt hk)
    obtain ⟨L', U', hL', hU', hLU⟩ := ih A hAk
    have hdetA : A.det ≠ 0 := by
      exact hg n (Nat.lt_succ_self n)
    have hdL : L'.det = 1 := det_lowUni hL'
    have hdU : U'.det ≠ 0 := by
      intro h0; apply hdetA; rw [hLU, Matrix.det_mul, h0, mul_zero]
    have iL : IsUnit L'.det := by rw [hdL]; exact isUnit_one
    have iU : IsUnit U'.det := isUnit_iff_ne_zero.2 hdU
    set c : Fin n → ℂ := fun j => g (Fin.last n) j.castSucc
    set b : Fin n → ℂ := fun i => g i.castSucc (Fin.last n)
    set r : Fin n → ℂ := Matrix.vecMul c U'⁻¹
    set q : Fin n → ℂ := L'⁻¹ *ᵥ b
    refine ⟨blk L' 0 r 1, blk U' q 0 (g (Fin.last n) (Fin.last n) - r ⬝ᵥ q), ⟨?_, ?_⟩, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL'.2 i
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hU' i j (Fin.castSucc_lt_castSucc_iff.1 hij)
    · ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cl, blk_ll]
          simp [dotProduct]
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_lc, blk_cc, blk_ll, blk_lc]
          have : (Matrix.vecMul r U') j = c j := by
            simp only [r, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ iU, Matrix.vecMul_one]
          simp only [Pi.zero_apply, mul_zero, add_zero]
          exact this.symm
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, Pi.zero_apply, zero_mul, add_zero]
          have : (L' *ᵥ q) i = b i := by
            simp only [q, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ iL, Matrix.one_mulVec]
          exact this.symm
        | cast j =>
          simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blk_cc, blk_cl, blk_lc, Pi.zero_apply, zero_mul,
            add_zero]
          rw [← Matrix.mul_apply, ← hLU]; rfl


theorem dense_LU {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 ∧
      ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g + x • (1 : Matrix (Fin n) (Fin n) ℂ) = L * U := by
  have hsub : ∀ (x : ℂ) (m : ℕ) (hm : m ≤ n),
      (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm) =
        g.submatrix (Fin.castLE hm) (Fin.castLE hm) + x • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro x m hm
    simp only [Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply]
    rw [Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  have hmin : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ∀ m : Fin (n + 1),
      (g.submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2)) (Fin.castLE (Nat.lt_succ_iff.mp m.2)) +
        x • (1 : Matrix (Fin m) (Fin m) ℂ)).det ≠ 0 :=
    Filter.eventually_all.2 fun m => det_add_smul_eventually _
  filter_upwards [det_add_smul_eventually g, hmin] with x hdet hm
  exact ⟨hdet, exists_LU_for_dense n _ fun k hk => by
    simpa only [hsub] using hm ⟨k, Nat.lt_succ_of_lt hk⟩⟩

theorem tendsto_add_smul {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝[≠] 0) (𝓝 g) := by
  have h : Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝 0)
      (𝓝 (g + (0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :=
    tendsto_const_nhds.add (tendsto_id.smul_const _)
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

end PI.UnitaryGroupMassFormula.HwConjInf
