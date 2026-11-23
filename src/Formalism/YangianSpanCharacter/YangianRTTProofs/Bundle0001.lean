module

public import Formalism.YangianSpanCharacter.StatementT

@[expose] public section

-- bundled from Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
section
namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T

set_option linter.unusedSimpArgs false in
theorem rttRelation : Formalism.YangianSpanCharacter.T.RTT := by
  intro R A _ _ _ p c ci Y Y' hW
  obtain ⟨hcc, hcc', hpc⟩ := hW
  have hpc2 : ∀ x : A, p * (c * x) = c * (p * x) + c * x := fun x => by
    rw [← mul_assoc, hpc, add_mul, mul_assoc]
  have hpci : p * ci = ci * p - ci := by
    have h := congrArg (fun x => ci * x * ci) hpc
    simp only [mul_add, add_mul, ← mul_assoc, hcc', one_mul] at h
    simp only [mul_assoc, hcc, mul_one] at h
    rw [h]; abel
  have hpci2 : ∀ x : A, p * (ci * x) = ci * (p * x) - ci * x := fun x => by
    rw [← mul_assoc, hpci, sub_mul, mul_assoc]
  have hcc2 : ∀ x : A, c * (ci * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hcc2' : ∀ x : A, ci * (c * x) = x := fun x => by rw [← mul_assoc, hcc', one_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, T1, T2, Pf, Tm,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  all_goals
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_sub, sub_mul, neg_mul,
      mul_neg, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, smul_add, smul_sub,
      smul_neg, smul_smul, hpc, hpc2, hpci, hpci2, hcc, hcc', hcc2, hcc2', neg_neg, sub_smul]
  all_goals module

end Formalism.YangianSpanCharacter.P
end

-- bundled from Formalism.YangianSpanCharacter.YangianRTTProofs.TransposeSymplecticShift
section
namespace Formalism.YangianSpanCharacter.P

open Matrix

theorem transposeSymplecticShift : Formalism.YangianSpanCharacter.T.TJT := by
  intro R A _ _ _ p c ci Y h
  obtain ⟨h1, h2, h3⟩ := h
  have hpci : p * ci = ci * p - ci := by
    have : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
    have e1 : ci * (p * c) * ci = ci * p := by
      rw [mul_assoc, mul_assoc, h1, mul_one]
    have e2 : ci * (c * p + c) * ci = p * ci + ci := by
      rw [mul_add, add_mul, ← mul_assoc ci c p, h2, one_mul, one_mul]
    rw [e1, e2] at this
    rw [this]; abel
  have hc : ∀ x : A, algebraMap R A Y * x = x * algebraMap R A Y := fun x => Algebra.commutes Y x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.J, map_add (f := _), add_mul, mul_add]
  all_goals first
    | exact h1
    | exact h2
    | (rw [hpci, hc ci]; abel)

theorem planeWaveIntertwining : Formalism.YangianSpanCharacter.T.PlaneWave := by
  intro R A _ _ _ p c ci f s Y hfc hfci hpf
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Um, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two]
  · have key : c * f * algebraMap R A s = algebraMap R A s * f * c := by
      rw [← hfc, mul_assoc, ← Algebra.commutes, ← mul_assoc]
      exact congrArg (· * c) (Algebra.commutes s f).symm
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Formalism.YangianSpanCharacter.T.Tm, Formalism.YangianSpanCharacter.T.Uinv, Matrix.mul_apply, Fin.sum_univ_two, hfc, hfci] <;>
      simp only [mul_add, add_mul, mul_neg, neg_mul, hpf, key, Algebra.commutes] <;>
      first | noncomm_ring | abel

end Formalism.YangianSpanCharacter.P
end

