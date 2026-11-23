module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
section
open GlobalTheory.InertZeta Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem mem_intL_iff {x : L} : x ∈ Formalism.UG.intL L ↔ Valued.v x ≤ 1 := Iff.rfl

theorem det_updateRow_one (i : Fin n) (ρ : Fin n → L) :
    ((1 : Matrix (Fin n) (Fin n) L).updateRow i ρ).det = ρ i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one, ← Matrix.cramer_apply,
    Matrix.cramer_one]
  rfl

theorem rowLat_updateRow {M : Matrix (Fin n) (Fin n) L} {ρ : Fin n → L} {i : Fin n}
    (h0 : ρ i ≠ 0) (h1 : Valued.v (ρ i)⁻¹ ≤ 1) (h2 : ∀ j, Valued.v (ρ j) ≤ Valued.v (ρ i)) :
    rowLat M ⊔ Submodule.span (Formalism.UG.intL L) {ρ ᵥ* M} = rowLat (M.updateRow i (ρ ᵥ* M)) := by
  set w := ρ ᵥ* M with hw
  apply le_antisymm
  · refine sup_le (rowLat_le.2 fun j => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
    · by_cases hj : j = i
      · subst hj
        refine mem_rowLat.2 ⟨fun l => if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹), fun l => ?_, ?_⟩
        · by_cases hl : l = j
          · simp only [if_pos hl]
            exact h1
          · simp only [hl, if_false]
            refine neg_mem ?_
            rw [mem_intL_iff, map_mul, map_inv₀]
            exact mul_inv_le_one_of_le₀ (h2 l) zero_le'
        · rw [Matrix.vecMul_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have e1 : ∑ l ∈ Finset.univ.erase j, (if l = j then (ρ j)⁻¹ else -(ρ l * (ρ j)⁻¹)) • (M.updateRow j w) l
              = ∑ l ∈ Finset.univ.erase j, (-(ρ l * (ρ j)⁻¹)) • M l :=
            Finset.sum_congr rfl fun l hl => by
              have := Finset.ne_of_mem_erase hl
              simp [this, Matrix.updateRow_ne]
          have e2 : w = ρ j • M j + ∑ l ∈ Finset.univ.erase j, ρ l • M l := by
            rw [hw, Matrix.vecMul_eq_sum]
            exact (Finset.add_sum_erase _ (fun l => ρ l • M l) (Finset.mem_univ j)).symm
          rw [e1]
          simp only [if_true, Matrix.updateRow_self]
          rw [e2, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum, add_assoc,
            ← Finset.sum_add_distrib]
          simp only [smul_smul, neg_smul]
          have : ∀ l, (ρ j)⁻¹ * ρ l = ρ l * (ρ j)⁻¹ := fun l => mul_comm _ _
          simp [this]
      · have := row_mem_rowLat (M.updateRow i w) j
        rwa [Matrix.updateRow_ne hj] at this
    · have := row_mem_rowLat (M.updateRow i w) i
      rwa [Matrix.updateRow_self] at this
  · refine rowLat_le.2 fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [Matrix.updateRow_self]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · rw [Matrix.updateRow_ne hj]
      exact Submodule.mem_sup_left (row_mem_rowLat M j)

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  by_cases e0 : e = 0
  · subst e0
    refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact mem_intL_iff.2 (by simpa using hρ i)
  · obtain ⟨i, hi⟩ := he.resolve_left e0
    have h0 : ρ i ≠ 0 := fun h => by
      rw [h, map_zero] at hi
      exact WithZero.exp_ne_zero hi.symm
    have hone : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (e : ℤ) := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have h1 : Valued.v (ρ i)⁻¹ ≤ 1 := by
      rw [map_inv₀, hi]
      exact inv_le_one_of_one_le₀ hone
    refine ⟨M.updateRow i (ρ ᵥ* M), ?_, rowLat_updateRow h0 h1 fun j => hi ▸ hρ j⟩
    have e1 : M.updateRow i (ρ ᵥ* M) = (1 : Matrix (Fin n) (Fin n) L).updateRow i ρ * M := by
      ext a b
      by_cases ha : a = i
      · subst ha
        simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
      · simp [Matrix.updateRow_ne ha, Matrix.mul_apply, Matrix.one_apply]
    rw [e1, Matrix.det_mul, det_updateRow_one, map_mul, hi, hM, ← WithZero.exp_add, add_comm]

end GlobalTheory.CompanionTheory.InertZeta

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CompletionExists
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl

namespace GlobalTheory.CompanionTheory.InertDoubling

theorem ring_gram {R : Type} [Ring R] (J A B U V a b u v S s : R) (hJ : J * J = 1) (h1 : U * A + V * B = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * (U * J * u - V * J * v) * J + J * S + s * J := by
  have e : (J * U * J + s * a) * J * (J * u * J + A * S) - (-(J * V * J) + s * b) * J * (-(J * v * J) + B * S) =
      J * U * (J * J) * J * u * J + J * U * (J * J) * A * S + s * a * (J * J) * u * J + s * (a * J * A) * S
      - J * V * (J * J) * J * v * J + J * V * (J * J) * B * S + s * b * (J * J) * v * J - s * (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : J * U * 1 * J * u * J + J * U * 1 * A * S + s * a * 1 * u * J + s * (b * J * B) * S
      - J * V * 1 * J * v * J + J * V * 1 * B * S + s * b * 1 * v * J - s * (b * J * B) * S =
      J * (U * J * u - V * J * v) * J + J * (U * A + V * B) * S + s * (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h1, h2]
  noncomm_ring

theorem ring_pair {R : Type} [Ring R] (J A B U V a b u v S : R) (hJ : J * J = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = J := by
  have e : a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) =
      (a * (J * J) * u + b * (J * J) * v) * J + (a * J * A) * S - (b * J * B) * S := by
    noncomm_ring
  rw [e, hJ, h3]
  have e2 : (a * 1 * u + b * 1 * v) * J + (b * J * B) * S - (b * J * B) * S = (a * u + b * v) * J := by
    noncomm_ring
  rw [e2, h2, one_mul]

section Cong

variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}

theorem cT_add' (M N : Matrix m p L) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

theorem cT_sub' (M N : Matrix m p L) : cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem cT_neg' (M : Matrix m p L) : cT σ (-M) = -cT σ M := by
  ext i j; simp [cT]

theorem cT_smul' (c : L) (M : Matrix m p L) : cT σ (c • M) = σ c • cT σ M := by
  ext i j; simp [cT]

theorem cT_cT' (h : ∀ x, σ (σ x) = x) (M : Matrix m p L) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, h]

theorem cT_fromBlocks {m₁ m₂ p₁ p₂ : Type} (A : Matrix m₁ p₁ L) (B : Matrix m₁ p₂ L) (C : Matrix m₂ p₁ L)
    (D : Matrix m₂ p₂ L) : cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  ext (i | i) (j | j) <;> simp [cT]

theorem cT_submatrix {ι : Type} (e : m ≃ ι) (M : Matrix m m L) :
    cT σ (M.submatrix e.symm e.symm) = (cT σ M).submatrix e.symm e.symm := by
  ext i j; simp [cT]

end Cong

section Int

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isInt_fromBlocks {m₁ m₂ p₁ p₂ : Type} {A : Matrix m₁ p₁ L} {B : Matrix m₁ p₂ L} {C : Matrix m₂ p₁ L}
    {D : Matrix m₂ p₂ L} (hA : IsInt A) (hB : IsInt B) (hC : IsInt C) (hD : IsInt D) : IsInt (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

theorem isInt_neg' {m p : Type} {A : Matrix m p L} (h : IsInt A) : IsInt (-A) := fun i j => neg_mem (h i j)

theorem isInt_sub' {m p : Type} {A B : Matrix m p L} (h : IsInt A) (h' : IsInt B) : IsInt (A - B) :=
  fun i j => sub_mem (h i j) (h' i j)

theorem isInt_smul' {m p : Type} {A : Matrix m p L} {c : L} (hc : c ∈ intL L) (h : IsInt A) : IsInt (c • A) :=
  fun i j => mul_mem hc (h i j)

theorem isInt_cT' {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {m p : Type} {A : Matrix m p L} (h : IsInt A) :
    IsInt (cT σ A) := fun i j => by
  have := h j i
  rw [GlobalTheory.UnitarySwap.mem_int] at this ⊢
  simpa [cT, hσ] using this

theorem isInt_antiJ (n : ℕ) : IsInt (antiJ L n) := fun i j => by
  unfold antiJ
  split_ifs
  · exact one_mem _
  · exact zero_mem _

end Int

theorem cT_antiJ {L : Type} [Field L] (σ : L →+* L) (n : ℕ) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, antiJ, transpose_apply, map_apply]
  by_cases h : i.val + j.val + 1 = n
  · have : j.val + i.val + 1 = n := by omega
    simp [h, this]
  · have : ¬ (j.val + i.val + 1 = n) := by omega
    simp [h, this]

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem exists_block (hσσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {τ : L} (hτ : τ ∈ intL L)
    (hτ1 : τ + σ τ = 1) {A B U V : Matrix (Fin n) (Fin n) L} (hA : IsInt A) (hB : IsInt B) (hU : IsInt U) (hV : IsInt V)
    (hAB : cT σ A * antiJ L n * A = cT σ B * antiJ L n * B) (hUV : U * A + V * B = 1) :
    ∃ k₀ k₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, IsInt k₀ ∧ IsInt k₁ ∧ k₁ * k₀ = 1 ∧
      cT σ k₀ * fromBlocks (antiJ L n) 0 0 (-antiJ L n) * k₀ = fromBlocks (antiJ L n) 0 0 (-antiJ L n) ∧
      k₀.toBlocks₁₁ + k₀.toBlocks₁₂ = A ∧ k₀.toBlocks₂₁ + k₀.toBlocks₂₂ = B := by
  obtain ⟨J, hJdef⟩ : ∃ J, J = antiJ L n := ⟨_, rfl⟩
  rw [← hJdef] at hAB ⊢
  have hJ : J * J = 1 := hJdef ▸ GlobalTheory.UnitarySwap.antiJ_mul_self
  have hJc : cT σ J = J := hJdef ▸ cT_antiJ σ n
  have hJi : IsInt J := hJdef ▸ isInt_antiJ n
  have hτ' : σ τ ∈ intL L := by rw [GlobalTheory.UnitarySwap.mem_int, hσv]; exact hτ
  obtain ⟨R, hR⟩ : ∃ R, R = U * J * cT σ U - V * J * cT σ V := ⟨_, rfl⟩
  have hRc : cT σ R = R := by
    rw [hR]; simp only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have hRi : IsInt R := hR ▸ isInt_sub' ((hU.mul hJi).mul (isInt_cT' hσv hU)) ((hV.mul hJi).mul (isInt_cT' hσv hV))
  obtain ⟨S, hS⟩ : ∃ S, S = -(τ • (R * J)) := ⟨_, rfl⟩
  have hSc : cT σ S = -(σ τ • (J * R)) := by rw [hS, cT_neg', cT_smul', cT_mul, hRc, hJc]
  have hSi : IsInt S := hS ▸ isInt_neg' (isInt_smul' hτ (hRi.mul hJi))
  obtain ⟨Ψ₁, hΨ₁⟩ : ∃ Ψ, Ψ = J * cT σ U * J + A * S := ⟨_, rfl⟩
  obtain ⟨Ψ₂, hΨ₂⟩ : ∃ Ψ, Ψ = -(J * cT σ V * J) + B * S := ⟨_, rfl⟩
  have hΨ₁i : IsInt Ψ₁ := hΨ₁ ▸ ((hJi.mul (isInt_cT' hσv hU)).mul hJi).add (hA.mul hSi)
  have hΨ₂i : IsInt Ψ₂ := hΨ₂ ▸ (isInt_neg' ((hJi.mul (isInt_cT' hσv hV)).mul hJi)).add (hB.mul hSi)
  have h2 : cT σ A * cT σ U + cT σ B * cT σ V = 1 := by
    have := congrArg (cT σ) hUV
    rwa [cT_add', cT_mul, cT_mul, cT_one] at this
  have g12 : cT σ A * J * Ψ₁ - cT σ B * J * Ψ₂ = J := by
    rw [hΨ₁, hΨ₂]; exact ring_pair J A B U V _ _ _ _ S hJ h2 hAB
  have g21 : cT σ Ψ₁ * J * A - cT σ Ψ₂ * J * B = J := by
    have := congrArg (cT σ) g12
    simpa only [cT_sub', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc] using this
  have cΨ₁ : cT σ Ψ₁ = J * U * J + cT σ S * cT σ A := by
    rw [hΨ₁]; simp only [cT_add', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have cΨ₂ : cT σ Ψ₂ = -(J * V * J) + cT σ S * cT σ B := by
    rw [hΨ₂]; simp only [cT_add', cT_neg', cT_mul, cT_cT' hσσ, hJc, Matrix.mul_assoc]
  have g22 : cT σ Ψ₁ * J * Ψ₁ - cT σ Ψ₂ * J * Ψ₂ = 0 := by
    rw [cΨ₁, cΨ₂, hΨ₁, hΨ₂, ring_gram J A B U V _ _ _ _ S _ hJ hUV h2 hAB, ← hR, hSc, hS]
    have e : J * R * J + J * -(τ • (R * J)) + -(σ τ • (J * R)) * J = (1 - τ - σ τ) • (J * R * J) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, sub_smul, one_smul]
      abel
    rw [e, show 1 - τ - σ τ = 0 by linear_combination -hτ1, zero_smul]
  have e1 : σ τ • (1 : Matrix (Fin n) (Fin n) L) + τ • 1 = 1 := by rw [← add_smul, add_comm, hτ1, one_smul]
  have e2 : σ τ • J + τ • J = J := by rw [← add_smul, add_comm, hτ1, one_smul]
  obtain ⟨Jd, hJd⟩ : ∃ Jd : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, Jd = fromBlocks J 0 0 (-J) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, H = fromBlocks 0 J J 0 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks 1 (τ • 1) 1 (-(σ τ • 1)) := ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, D = fromBlocks (σ τ • 1) (τ • 1) 1 (-1) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, P = fromBlocks A Ψ₁ B Ψ₂ := ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨e1, by simp, by simp, ?_⟩
    rw [add_comm]; exact e1
  have hHH : H * H = 1 := by
    rw [hH, fromBlocks_multiply, ← fromBlocks_one]
    simp [hJ]
  have hDg : cT σ D * Jd * D = H := by
    rw [hD, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [cT_neg', cT_smul', cT_one, hσσ, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_neg]
    rw [fromBlocks_inj]
    refine ⟨by simp, by rw [add_comm]; exact e2, e2, ?_⟩
    rw [smul_comm, add_neg_cancel]
  have hPg : cT σ P * Jd * P = H := by
    rw [hP, hJd, hH, cT_fromBlocks, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg]
    simp only [← sub_eq_add_neg]
    rw [fromBlocks_inj]
    exact ⟨sub_eq_zero.2 hAB, g12, g21, g22⟩
  have hDi' : IsInt Di := hDi ▸ isInt_fromBlocks (isInt_smul' hτ' isInt_one) (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' isInt_one)
  have hDint : IsInt D := hD ▸ isInt_fromBlocks isInt_one (isInt_smul' hτ isInt_one) isInt_one (isInt_neg' (isInt_smul' hτ' isInt_one))
  have hPi : IsInt P := hP ▸ isInt_fromBlocks hA hΨ₁i hB hΨ₂i
  have hHi : IsInt H := hH ▸ isInt_fromBlocks isInt_zero hJi hJi isInt_zero
  have hJdi : IsInt Jd := hJd ▸ isInt_fromBlocks hJi isInt_zero isInt_zero (isInt_neg' hJi)
  refine ⟨P * Di, D * H * cT σ P * Jd, hPi.mul hDi', ((hDint.mul hHi).mul (isInt_cT' hσv hPi)).mul hJdi, ?_, ?_, ?_, ?_⟩
  · calc D * H * cT σ P * Jd * (P * Di) = D * H * (cT σ P * Jd * P) * Di := by simp only [Matrix.mul_assoc]
      _ = D * (H * H) * Di := by rw [hPg]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, hDDi]
  · rw [← hJd]
    calc cT σ (P * Di) * Jd * (P * Di) = cT σ Di * (cT σ P * Jd * P) * Di := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ Di * (cT σ D * Jd * D) * Di := by rw [hPg, hDg]
      _ = cT σ (D * Di) * Jd * (D * Di) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Jd := by rw [hDDi, cT_one, Matrix.one_mul, Matrix.mul_one]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • A + Ψ₁ + (τ • A + -Ψ₁) = (τ + σ τ) • A by rw [add_smul]; abel, hτ1, one_smul]
  · rw [hP, hDi, fromBlocks_multiply, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.mul_neg]
    rw [show σ τ • B + Ψ₂ + (τ • B + -Ψ₂) = (τ + σ τ) • B by rw [add_smul]; abel, hτ1, one_smul]

theorem completion : Completion := by
  intro L _ _ ϖ σ q n hU g U V C hF
  obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
  have hσσ := hU.1
  have hσv := hU.2.1
  obtain ⟨hUi, hVi, hC, hgC, hone⟩ := hF
  have hg : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have hAB : cT σ C * antiJ L n * C = cT σ (mat g * C) * antiJ L n * (mat g * C) := by
    rw [cT_mul]
    calc cT σ C * antiJ L n * C = cT σ C * (cT σ (mat g) * antiJ L n * mat g) * C := by rw [hg]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hUV : U * C + V * (mat g * C) = 1 := by
    rw [← hone]; simp only [Matrix.add_mul, Matrix.mul_assoc]
  obtain ⟨k₀, k₁, h0, h1, h10, hu, hx, hy⟩ := exists_block hσσ hσv hτ hτ1 hC hgC hUi hVi hAB hUV
  have hmul : k₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      k₁.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm = 1 := by
    rw [submatrix_mul_equiv, mul_eq_one_comm.1 h10, submatrix_one_equiv]
  obtain ⟨k, hki, hke⟩ := P.cartan_exists_glint (intL L) _ _ hmul (fun i j => h0 _ _) (fun i j => h1 _ _)
  refine ⟨k, ?_, hki, fun x => ?_⟩
  · show cT σ (k : Matrix _ _ L) * dblGram finSumFinEquiv (antiJ L n) * (k : Matrix _ _ L) = _
    rw [hke, cT_submatrix, dblGram, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, hu]
  · rw [hke, mulVec_pairVec]
    have e : (k₀.submatrix (finSumFinEquiv (m := n) (n := n)).symm finSumFinEquiv.symm).submatrix finSumFinEquiv
        finSumFinEquiv = k₀ := by ext i j; simp
    rw [e, ← add_mulVec, ← add_mulVec, hx, hy]

end Main

end GlobalTheory.CompanionTheory.InertDoubling
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CosetInjective
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem rad_mul_levi_apply {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hu i i le_rfl, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rcases le_or_gt (β l) (β i) with h1 | h1
    · rw [hu i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
    · rw [hp l j (by omega), mul_zero]
  · simp

theorem rad_levi_rad_apply {β : Fin n → ℕ} {u p u' : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β)
    (hu' : u' ∈ radU σ β) {i j : Fin n} (hij : β j ≤ β i) : mat (u * p * u') i j = mat p i j := by
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hu' j j le_rfl, Matrix.one_apply_eq, mul_one]
    exact rad_mul_levi_apply hu hp hij
  · intro l _ hl
    rcases le_or_gt (β j) (β l) with h1 | h1
    · rw [hu' l j h1, Matrix.one_apply_ne hl, mul_zero]
    · rw [rad_mul_levi_apply hu hp (by omega), hp i l (by omega), zero_mul]
  · simp

variable {N : ℕ}

theorem levi_mul_zero {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) : mat (x * y) 0 0 = mat x 0 0 * mat y 0 0 := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
    add_zero]
  intro j _
  rw [hx 0 (mid j) (by simp), zero_mul]

theorem levi_mul_last {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) :
    mat (x * y) (Fin.last (N + 1)) (Fin.last (N + 1)) =
      mat x (Fin.last (N + 1)) (Fin.last (N + 1)) * mat y (Fin.last (N + 1)) (Fin.last (N + 1)) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, Finset.sum_eq_zero, hx (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
    zero_add]
  intro j _
  rw [hx (Fin.last (N + 1)) (mid j) (by simp), zero_mul]

theorem levi_mul_mid {x y : GU σ (N + 2)} (hx : x ∈ leviU σ (blk N)) (i j : Fin N) :
    mat (x * y) (mid i) (mid j) = ∑ k, mat x (mid i) (mid k) * mat y (mid k) (mid j) := by
  rw [mat_mul, Matrix.mul_apply, sum_idx, hx (mid i) 0 (by simp), hx (mid i) (Fin.last (N + 1)) (by simp)]
  simp

end

theorem cosetInj : CosetInj := by
  intro L _ _ ϖ σ q N hU a a' g₀ g₀' m m' hm hm' u hu u' hu' hk
  obtain ⟨-, hσ, hσϖ, hϖ, -, -, -⟩ := hU
  obtain ⟨hl, h0, h1, h2⟩ := hm
  obtain ⟨hl', h0', h1', h2'⟩ := hm'
  have hli : m⁻¹ ∈ leviU σ (blk N) := inv_mem hl
  have hp : m⁻¹ * m' ∈ leviU σ (blk N) := mul_mem hli hl'
  have e : (m * u)⁻¹ * (m' * u') = u⁻¹ * (m⁻¹ * m') * u' := by group
  rw [e] at hk
  have hint : ∀ i j, blk N j ≤ blk N i → mat (m⁻¹ * m') i j ∈ intL L := fun i j hij => by
    rw [← rad_levi_rad_apply (inv_mem hu) hp hu' hij]
    exact (mem_KU_iff hσ _).1 hk i j
  have e0 : mat (m⁻¹ * m') 0 0 = ϖ ^ (a' - a) := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_zero hli, mat_inv_apply, Fin.rev_zero, h1, h0', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have e1 : mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (a - a') := by
    have hϖ0 : ϖ ≠ 0 := fun h => by
      rw [h, map_zero] at hϖ
      exact WithZero.coe_ne_zero hϖ.symm
    rw [levi_mul_last hli, mat_inv_apply, Fin.rev_last, h0, h1', map_zpow₀, hσϖ, ← zpow_add₀ hϖ0]
    congr 1 <;> ring
  have hv0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
  have hv1 : Valued.v ϖ < 1 := by
    rw [hϖ]
    exact WithZero.coe_lt_one.2 (by decide)
  have i0 : Valued.v ϖ ^ (a' - a) ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') 0 0) ≤ 1 := hint 0 0 le_rfl
    rwa [e0, map_zpow₀] at this
  have i1 : Valued.v ϖ ^ (a - a') ≤ 1 := by
    have : Valued.v (mat (m⁻¹ * m') (Fin.last (N + 1)) (Fin.last (N + 1))) ≤ 1 :=
      hint _ _ (le_refl (blk N (Fin.last (N + 1))))
    rwa [e1, map_zpow₀] at this
  rw [zpow_le_one_iff_right_of_lt_one₀ hv0 hv1] at i0 i1
  refine ⟨by omega, (mem_KU_iff hσ _).2 fun i j => ?_⟩
  have := hint (mid i) (mid j) (by simp)
  have e2 : ∀ i j, mat m⁻¹ (mid i) (mid j) = mat g₀⁻¹ i j := fun i j => by
    rw [mat_inv_apply, mat_inv_apply, ← mid_rev, ← mid_rev, h2]
  rw [levi_mul_mid hli] at this
  simp only [e2, h2'] at this
  rw [mat_mul, Matrix.mul_apply]
  exact this

end GlobalTheory.CompanionTheory.InertZeta

end
end

