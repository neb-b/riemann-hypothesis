module

public import Formalism.MahlerMeasure.Bundle0001

@[expose] public section

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm
section
namespace Formalism.GM

open Finset Polynomial

theorem prod_natDegree_coeff {K ι : Type*} [CommRing K] (s : Finset ι) (f : ι → K[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih h
    have ha' : (f a).natDegree ≤ d a := h a (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    exact ⟨Polynomial.natDegree_mul_le.trans (add_le_add ha' ih1),
      by rw [Polynomial.coeff_mul_add_eq_of_natDegree_le ha' ih1, ih2]⟩

theorem term_natDegree_coeff {K : Type*} [CommRing K] (u : ℤˣ) (p : K[X]) (N : ℕ)
    (hp : p.natDegree ≤ N) :
    (u • p).natDegree ≤ N ∧ (u • p).coeff N = u • p.coeff N := by
  refine ⟨?_, ?_⟩
  · rw [Units.smul_def]
    exact (Polynomial.natDegree_smul_le _ _).trans hp
  · rw [Units.smul_def, Units.smul_def, Polynomial.coeff_smul]

theorem det_natDegree_coeff {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K[X]) (N : ℕ)
    (c : Equiv.Perm (Fin n) → Fin n → ℕ) (hc : ∀ σ, ∑ i, c σ i = N)
    (hA : ∀ σ i, (A (σ i) i).natDegree ≤ c σ i) :
    A.det.natDegree ≤ N ∧
      A.det.coeff N = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
  have key : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤ N ∧
      (Equiv.Perm.sign σ • ∏ i, A (σ i) i).coeff N =
        Equiv.Perm.sign σ • ∏ i, (A (σ i) i).coeff (c σ i) := by
    intro σ
    obtain ⟨h1, h2⟩ := prod_natDegree_coeff univ (fun i => A (σ i) i) (c σ) (fun i _ => hA σ i)
    rw [hc σ] at h1 h2
    obtain ⟨k1, k2⟩ := term_natDegree_coeff (Equiv.Perm.sign σ) _ N h1
    exact ⟨k1, by rw [k2, h2]⟩
  rw [Matrix.det_apply]
  refine ⟨natDegree_sum_le_of_forall_le _ _ (fun σ _ => (key σ).1), ?_⟩
  rw [finsetSum_coeff]
  exact sum_congr rfl (fun σ _ => (key σ).2)

theorem determinant_block_leading_term : DetBlockLead := by
  unfold DetBlockLead
  intro K _ n A D e he hA
  set M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun i j => if e i = e j then (A i j).coeff (D - e i) else 0 with hM
  have hdeg : ∀ σ : Equiv.Perm (Fin n), ∀ i, (A (σ i) i).natDegree ≤ D - e i := by
    intro σ i
    have h3 := hA (σ i) i
    have h4 : e i ≤ max (e (σ i)) (e i) := le_max_right _ _
    omega
  obtain ⟨h1, h2⟩ := det_natDegree_coeff A (∑ i, (D - e i)) (fun _ i => D - e i)
    (fun _ => rfl) hdeg
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (A (σ i) i).coeff (D - e i) = ∏ i, M (σ i) i := by
    intro σ
    by_cases hall : ∀ i, e (σ i) = e i
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      simp [hM, Matrix.of_apply, hall i]
    · push_neg at hall
      have hex : ∃ j, e j < e (σ j) := by
        by_contra hno
        push_neg at hno
        have hsum : ∑ j, e (σ j) = ∑ j, e j := Equiv.sum_comp σ e
        have hall' := (Finset.sum_eq_sum_iff_of_le (fun j _ => hno j)).1 hsum
        obtain ⟨i, hi⟩ := hall
        exact hi (hall' i (Finset.mem_univ i))
      obtain ⟨j, hj⟩ := hex
      have hne : e (σ j) ≠ e j := ne_of_gt hj
      have hL : (A (σ j) j).coeff (D - e j) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have h3 := hA (σ j) j
        have h4 : e (σ j) ≤ max (e (σ j)) (e j) := le_max_left _ _
        have h5 := he (σ j)
        omega
      have hR : M (σ j) j = 0 := by simp [hM, Matrix.of_apply, hne]
      rw [Finset.prod_eq_zero (f := fun i => (A (σ i) i).coeff (D - e i)) (Finset.mem_univ j) hL,
        Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) hR]
  have hdet : A.det.coeff (∑ i, (D - e i)) = M.det := by
    rw [h2, Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [hprod σ])
  refine ⟨h1, hdet, fun hne => ?_⟩
  have hN : A.det.natDegree = ∑ i, (D - e i) :=
    le_antisymm h1 (Polynomial.le_natDegree_of_ne_zero (by rw [hdet]; exact hne))
  refine ⟨hN, ?_⟩
  rw [Polynomial.leadingCoeff, hN, hdet]

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.LevelSum
section
namespace Formalism.GM

open Finset

theorem altVand (B : ℕ) : ∀ z l : ℕ,
    ∑ j ∈ range (l + 1), (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + B + (l - j)).choose (l - j) : ℚ)
      = ((z + l).choose l : ℚ) := by
  induction B with
  | zero =>
    intro z l
    rw [Finset.sum_eq_single 0
      (fun j _ hj => by simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]) (by simp)]
    simp
  | succ B ih =>
    intro z l
    cases l with
    | zero => simp
    | succ m =>
      have h1 := ih (z + 1) (m + 1)
      have h2 := ih (z + 1) m
      rw [Finset.sum_range_succ'] at h1 ⊢
      have key : ∀ j ∈ range (m + 1),
          (-1 : ℚ) ^ (j + 1) * ((B + 1).choose (j + 1) : ℚ) *
              ((z + (B + 1) + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) =
            (-1 : ℚ) ^ (j + 1) * (B.choose (j + 1) : ℚ) *
                ((z + 1 + B + (m + 1 - (j + 1))).choose (m + 1 - (j + 1)) : ℚ) -
              (-1 : ℚ) ^ j * (B.choose j : ℚ) * ((z + 1 + B + (m - j)).choose (m - j) : ℚ) := by
        intro j hj
        have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have e1 : z + (B + 1) + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        have e2 : m + 1 - (j + 1) = m - j := by omega
        have e3 : z + 1 + B + (m + 1 - (j + 1)) = z + 1 + B + (m - j) := by omega
        rw [e1, e3, e2, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
        ring
      rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, h2]
      simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero] at h1 ⊢
      rw [show z + (B + 1) + (m + 1) = z + 1 + B + (m + 1) by omega]
      have hp : ((z + 1 + (m + 1)).choose (m + 1) : ℚ) =
          ((z + 1 + m).choose m : ℚ) + ((z + (m + 1)).choose (m + 1) : ℚ) := by
        have e1 : (z + 1 + (m + 1)).choose (m + 1) = (z + 1 + m + 1).choose (m + 1) := by
          rw [show z + 1 + (m + 1) = z + 1 + m + 1 by omega]
        have e2 : (z + (m + 1)).choose (m + 1) = (z + 1 + m).choose (m + 1) := by
          rw [show z + (m + 1) = z + 1 + m by omega]
        rw [e1, e2, Nat.choose_succ_succ']
        push_cast
        ring
      linear_combination h1 + hp

theorem alternatingChooseSum : LevelSum := by
  intro A z l hzl
  unfold qch
  have hAl : (A.choose l : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [← altVand (A - z - l) z l, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hAj : (A.choose j : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hcm : (A.choose l : ℚ) * (l.choose j : ℚ) = (A.choose j : ℚ) * ((A - j).choose (l - j) : ℚ) := by
    exact_mod_cast Nat.choose_mul (n := A) (k := l) (s := j) (by omega)
  have he : z + (A - z - l) + (l - j) = A - j := by omega
  rw [he, div_eq_div_iff hAj hAl]
  linear_combination ((-1 : ℚ) ^ j * ((A - z - l).choose j : ℚ)) * hcm

end Formalism.GM
end

