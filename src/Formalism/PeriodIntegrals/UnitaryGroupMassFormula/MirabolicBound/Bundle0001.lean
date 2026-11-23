module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.Development

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.CharSumOne
section
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem addChar_sum {F : Type} [Field F] (ψ₀ : AddChar F ℂ) {m : ℕ} (g : Fin m → F) :
    ψ₀ (∑ i, g i) = ∏ i, ψ₀ (g i) := by
  have h : ∀ s : Finset (Fin m), ψ₀ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ₀ (g i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [AddChar.map_zero_eq_one]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
  exact h _

theorem charSum_one {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) (a : F) :
    ∑ t : F, ψ₀ (a * t) = if a = 0 then (Fintype.card F : ℂ) else 0 := by
  split_ifs with ha
  · subst ha
    simp [AddChar.map_zero_eq_one]
  · rw [show (∑ t : F, ψ₀ (a * t)) = ∑ t : F, ψ₀ t from
        Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun t => rfl)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem charSum {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (hψ : ψ₀ ≠ 1) {m : ℕ} (ν : Fin m → F) :
    ∑ c : Fin m → F, ψ₀ (∑ i, ν i * c i) = if ν = 0 then (Fintype.card F : ℂ) ^ m else 0 := by
  have hps : ∑ c : Fin m → F, ∏ i, ψ₀ (ν i * c i) = ∏ i, ∑ t : F, ψ₀ (ν i * t) := by
    first
      | exact (Fintype.prod_sum (fun i t => ψ₀ (ν i * t))).symm
      | (rw [Finset.prod_univ_sum]; simp)
  simp_rw [addChar_sum ψ₀]
  rw [hps]
  simp_rw [charSum_one ψ₀ hψ]
  split_ifs with hν
  · subst hν
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hν (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem charOrth : CharOrth := by
  intro F _ _ m ψ₀ hψ r s
  have h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i) := by
    intro x
    rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]
    rfl
  simp_rw [h]
  rw [charSum ψ₀ hψ (r - s)]
  simp only [sub_eq_zero]

theorem sepLemma : SepLemma := by
  intro W _ _ X R ι _ _ _ T χ χ' N hN horth f hf hind
  have hf' : ∀ x (q : R × ι), T x (f q) = χ q.1 x • f q := fun x q => hf x q.1 q.2
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  obtain ⟨s, i⟩ := p
  have h1 : ∑ x, χ' s x • T x (∑ q, g q • f q) = 0 := by
    rw [hg]
    simp
  have h2 : ∑ x, χ' s x • T x (∑ q, g q • f q) =
      ∑ q, (if q.1 = s then N * g q else 0) • f q := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, map_smul, hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have ho := horth q.1 s
    calc ∑ x, χ' s x * (g q * χ q.1 x) = g q * ∑ x, χ q.1 x * χ' s x := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
      _ = _ := by
          rw [ho]
          split_ifs <;> ring
  have h3 : ∑ q : R × ι, (if q.1 = s then N * g q else 0) • f q = N • ∑ j, g (s, j) • f (s, j) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp [Finset.smul_sum, smul_smul]
    · intro r _ hr
      simp [hr]
    · intro h
      exact absurd (Finset.mem_univ s) h
  rw [h2, h3] at h1
  have key : ∑ j, g (s, j) • f (s, j) = 0 := (smul_eq_zero.mp h1).resolve_left hN
  exact (Fintype.linearIndependent_iff.mp (hind s)) (fun j => g (s, j)) key i

end

end PI.GGMirBoundW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.LastRowMul
section
namespace PI.GGMirBoundW

open Matrix Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

section Entries

variable {F : Type} [Field F] [Fintype F] {n : ℕ}

@[simp] theorem blkM_cc (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blkM A (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem blkM_cl (A : Matrix (Fin n) (Fin n) F) (i : Fin n) :
    blkM A (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_lc (A : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    blkM A (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [blkM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem blkM_ll (A : Matrix (Fin n) (Fin n) F) :
    blkM A (Fin.last n) (Fin.last n) = 1 := by
  simp [blkM, finSumFinEquiv_symm_last]

@[simp] theorem colM_cc (x : Fin n → F) (i j : Fin n) :
    colM x (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) F) i j := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem colM_cl (x : Fin n → F) (i : Fin n) :
    colM x (Fin.castSucc i) (Fin.last n) = x i := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_lc (x : Fin n → F) (j : Fin n) :
    colM x (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [colM, finSumFinEquiv_symm_apply_castSucc, finSumFinEquiv_symm_last]

@[simp] theorem colM_ll (x : Fin n → F) :
    colM x (Fin.last n) (Fin.last n) = 1 := by
  simp [colM, finSumFinEquiv_symm_last]

theorem E_val (A : GL (Fin n) F) : ((E F n A : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    blkM (A : Matrix (Fin n) (Fin n) F) := rfl

theorem col_val (x : Fin n → F) : ((col x : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    colM x := rfl

end Entries

theorem blkFacts : UnitriangularBlockExtension := by
  intro F _ _ n u hu
  obtain ⟨hd, hl⟩ := hu
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [E_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simpa using hd i
  · rw [E_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [blkM_cc]
        exact hl i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · rw [E_val]
    unfold superdiag
    simp [Fin.sum_univ_castSucc]

theorem colFacts : ColFacts := by
  intro F _ _ n x
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [col_val]
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  · rw [col_val]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (lt_irrefl _)
      | cast j => simp
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
      | cast j =>
        simp only [colM_cc]
        exact Matrix.one_apply_ne (ne_of_gt (Fin.castSucc_lt_castSucc_iff.mp hij))
  · rw [col_val]
    unfold superdiag
    have h0 : ∀ i j : Fin (n + 1),
        (if (j : ℕ) = (i : ℕ) + 1 then (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i j else 0) = 0 := by
      intro i j
      split_ifs with h
      · rw [Matrix.one_apply_ne]
        intro e; subst e; omega
      · rfl
    have hl : ∀ i : Fin (n + 1), (n = (i : ℕ)) ↔ (i = Fin.last n) := by
      intro i; rw [Fin.ext_iff, Fin.val_last]; omega
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.sum_univ_castSucc (n := n + 1), colM_cc, colM_cl, colM_lc, colM_ll, Fin.val_castSucc,
      Fin.val_last, h0, ite_self, add_left_inj, hl]
    simp

theorem conjCol : ConjCol := by
  intro F _ _ n A x
  ext : 1
  simp only [Units.val_mul, E_val, col_val, blkM, colM]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 2
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · simp
  · simp

theorem baseProp : BaseProp := by
  intro F _ _ ψ₀ _ V _ _ π ℓ hℓ _
  have hD : D F (0 + 1) = 1 := by simp [D]
  show ∃ p : Fin (D F (0 + 1)) → GL (Fin (0 + 1)) F, _
  rw [hD]
  refine ⟨fun _ => 1, fun _ j => ?_, ?_⟩
  · simp only [Units.val_one]
    rw [Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · rw [linearIndependent_unique_iff]
    show ℓ ∘ₗ π 1 ≠ 0
    rw [map_one]
    intro h
    apply hℓ
    ext v
    simpa using LinearMap.congr_fun h v

theorem lastRowE_E {F : Type} [Field F] [Fintype F] {n : ℕ} (A : GL (Fin n) F) : LastRowE (E F n A) := by
  intro j
  rw [E_val]
  induction j using Fin.lastCases with
  | last => simp
  | cast j => simp [Fin.castSucc_ne_last]

theorem lastRow_mul {F : Type} [Field F] [Fintype F] {n : ℕ} {p : GL (Fin (n + 1)) F} (hp : LastRowE p)
    (g : GL (Fin (n + 1)) F) (j : Fin (n + 1)) :
    ((p * g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) j := by
  have h2 : ∀ l, (p : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (Fin.last n) l = if l = Fin.last n then 1 else 0 := hp
  rw [Units.val_mul, Matrix.mul_apply]
  simp only [h2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end PI.GGMirBoundW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.RowExists
section
namespace PI.GGMirBoundW

open Finset Matrix

noncomputable section

open Classical

theorem rowExists : RowExists := by
  intro F _ _ n r hr
  obtain ⟨k, hk⟩ : ∃ k, r k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap k (Fin.last n) with hσ
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
    Matrix.updateRow 1 (Fin.last n) (fun j => r (σ j)) with hA
  have hAtri : A.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := fun h => by
      subst h
      exact absurd hij' (not_lt.mpr (Fin.le_last j))
    rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]
  have hdetA : A.det = r k := by
    rw [Matrix.det_of_lowerTriangular A hAtri, Finset.prod_eq_single (Fin.last n)]
    · rw [hA, Matrix.updateRow_self]
      simp [hσ]
    · intro i _ hi
      rw [hA, Matrix.updateRow_ne hi, Matrix.one_apply_eq]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set B := A.submatrix id σ with hB
  have hdetB : B.det ≠ 0 := by
    rw [hB, Matrix.det_permute', hdetA]
    refine mul_ne_zero ?_ hk
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr (isUnit_iff_ne_zero.mpr hdetB)
  refine ⟨hunit.unit, fun j => ?_⟩
  rw [IsUnit.unit_spec]
  simp [hB, hA, hσ, Matrix.updateRow_self, Equiv.swap_apply_self]

end

end PI.GGMirBoundW
end

