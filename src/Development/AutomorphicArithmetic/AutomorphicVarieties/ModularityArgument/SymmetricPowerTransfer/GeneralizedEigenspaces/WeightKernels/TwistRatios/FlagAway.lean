module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Tri

variable {k : Type} [Field k]

local notation "M2" => Matrix (Fin 2) (Fin 2) k

private theorem tri_exists [IsAlgClosed k] (M : GL (Fin 2) k) :
    ∃ Q : GL (Fin 2) k, ((Q * M * Q⁻¹ : GL (Fin 2) k) : M2) 1 0 = 0 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (M : M2))
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hMv : (M : M2).mulVec v = μ • v := by
    simpa [Matrix.toLin'_apply] using hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  obtain ⟨R, hR⟩ : ∃ R : GL (Fin 2) k, ∀ i, (R : M2) i 0 = v i := by
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := fun h1 => hv0 (by ext i; fin_cases i <;> simp [h0, h1])
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 1; v 1, 0]
        (by simp [Matrix.det_fin_two, h1]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, 0; v 1, 1]
        (by simp [Matrix.det_fin_two, h0]), ?_⟩
      intro i
      fin_cases i <;> simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
  refine ⟨R⁻¹, ?_⟩
  have hRT : (R : M2) * ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) = (M : M2) * (R : M2) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  set T : M2 := ((R⁻¹ * M * R⁻¹⁻¹ : GL (Fin 2) k) : M2) with hTdef
  have hcol : (R : M2).mulVec ![T 0 0 - μ, T 1 0] = 0 := by
    ext i
    have h1 : ((R : M2) * T) i 0 = ((M : M2) * (R : M2)) i 0 := by rw [hRT]
    have h2 : ((M : M2) * (R : M2)) i 0 = μ * v i := by
      have := congrFun hMv i
      simp only [Matrix.mul_apply, hR, Pi.smul_apply, smul_eq_mul] at this ⊢
      simpa [Matrix.mulVec, dotProduct] using this
    rw [h2, Matrix.mul_apply, Fin.sum_univ_two, hR] at h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hR, Pi.zero_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination h1
  have hdet : (R : M2).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 R.isUnit).ne_zero
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet hcol
  simpa using congrFun this 1

private def triSub : Subgroup (GL (Fin 2) k) where
  carrier := {M | (M : M2) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, ha]

end Tri
