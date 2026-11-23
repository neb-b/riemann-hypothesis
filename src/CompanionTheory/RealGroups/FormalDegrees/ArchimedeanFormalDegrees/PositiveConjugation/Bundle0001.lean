module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0010

@[expose] public section

-- bundled from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.DzSubMuNextNonneg
section
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem inP_entry_zero {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) {a b : Fin n}
    (h : ε a = ε b) : X a b = 0 := by
  have h1 := congrFun (congrFun hX.2 a) b
  simp only [Matrix.mul_apply, Matrix.neg_apply, Jm, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  rw [h] at h1
  split_ifs at h1 with hb
  · have : (2 : ℂ) * X a b = 0 := by linear_combination h1
    simpa using this
  · have : (2 : ℂ) * X a b = 0 := by linear_combination -h1
    simpa using this

theorem exists_pmat {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) :
    ∃ z : PCoord ε → ℂ, pmat z = X := by
  refine ⟨fun ab => X ab.1.1 ab.1.2, ?_⟩
  have hH := isHermitian_of_mem_noncompactPart' hX
  ext a b
  simp only [pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · rw [dite_eq_left h1]
  · rw [dite_eq_right h1]
    by_cases h2 : a < b ∧ ε b ≠ ε a
    · rw [dite_eq_left h2]
      have := congrFun (congrFun hH a) b
      simp only [Matrix.conjTranspose_apply] at this
      exact this
    · rw [dite_eq_right h2]
      by_cases he : ε a = ε b
      · exact (inP_entry_zero hX he).symm
      · have hab : a = b := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · exact h2 ⟨h, Ne.symm he⟩
          · exact h1 ⟨h, he⟩
        subst hab
        exact absurd rfl he

theorem one_le_lead_exp {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (i : ℕ) (hi : i ≤ n) :
    1 ≤ (lead i (NormedSpace.exp X)).re := by
  obtain ⟨z, rfl⟩ := exists_pmat hX
  have h0 := fi_nonneg z i
  have hp := (lead_posDef (exp_noncompactPart_posDef hX) i hi).1
  unfold Fi at h0
  have e : Del (NormedSpace.exp (pmat z)) i = lead i (NormedSpace.exp (pmat z)) := rfl
  rw [e] at h0
  exact (Real.log_nonneg_iff hp).1 h0

theorem dz_sub_muNext_nonneg (i : Fin n) : 0 ≤ Dz n i - muNext (Dz n) i := by
  unfold muNext Dz
  split_ifs with h
  · simp only
    omega
  · have : (i : ℕ) + 1 = n := by omega
    omega

theorem phiLe : PhiLe := by
  intro n ε X hX k
  obtain ⟨hP, hE⟩ := inP_conj k⁻¹ hX
  rw [inv_inv] at hP hE
  unfold phiK
  rw [← hE]
  set Y := toMK k⁻¹ * X * toMK k with hY
  have hpd := exp_noncompactPart_posDef hP
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) (NormedSpace.exp Y) = ((lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re : ℂ) :=
    fun i => Complex.ext (by simp) (by simp [(lead_posDef hpd _ i.isLt).2])
  have hphi : PhiM (Dz n) (NormedSpace.exp Y) =
      ((∏ i : Fin n, (lead ((i : ℕ) + 1) (NormedSpace.exp Y)).re ^ (-(Dz n i - muNext (Dz n) i)) : ℝ) : ℂ) := by
    unfold PhiM
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hr i, Complex.ofReal_zpow, Complex.ofReal_re]
  rw [hphi, Complex.ofReal_re]
  refine Finset.prod_le_one₀ (fun i _ => zpow_nonneg (zero_le_one.trans (one_le_lead_exp hP _ i.isLt)) _) fun i _ => ?_
  exact zpow_le_one_of_nonpos₀ (one_le_lead_exp hP _ i.isLt) (neg_nonpos.2 (dz_sub_muNext_nonneg i))

end CompanionTheory.RgFd
end
end

-- bundled from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.HsOpOpMul
section
noncomputable section

open Finset Matrix

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem polar_pP {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ k : KG ε, g = toMK k * pP g := by
  obtain ⟨u, hu⟩ := exists_toMK (PolarDecomposition.polar_k_mem hg)
  refine ⟨u, ?_⟩
  rw [hu, pP, Matrix.mul_assoc, PolarDecomposition.polar_exp_neg_mul, Matrix.mul_one]

theorem hsOp_op_mul {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    hsOp (T.op k * A) = hsOp A := by
  unfold hsOp
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.mul_apply, KType_norm_op_apply]

theorem hsPol : HsPol := by
  intro n ε g hg
  refine ⟨⟨PolarDecomposition.polar_L g, PolarDecomposition.polar_L_inP hg, rfl⟩, fun Λ T μ => ?_⟩
  obtain ⟨k, hk⟩ := polar_pP hg
  have hL := PolarDecomposition.polar_L_inP hg
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧ g = toMK k' * NormedSpace.exp X' :=
    ⟨k, PolarDecomposition.polar_L g, hL, hk⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  have hEq' : toMK k * NormedSpace.exp (PolarDecomposition.polar_L g) = toMK hex.choose * NormedSpace.exp hex.choose_spec.choose :=
    hk.symm.trans hEq
  obtain ⟨-, h2⟩ := polar_unique hL hP hEq'
  rw [hsOp_op_mul, ← h2]
  rfl

end CompanionTheory.RgFd
end
end

-- bundled from CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiMul
section
noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem posDef_conj_toMK {ε : Fin n → Bool} (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

theorem muNext_add_smul (μ D : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    muNext (μ + t • D) i = muNext μ i + t * muNext D i := by
  unfold muNext
  split_ifs <;> simp

theorem phiM_add_smul (μ D : Fin n → ℤ) (t : ℕ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    PhiM (μ + (t : ℤ) • D) y = PhiM μ y * PhiM D y ^ t := by
  unfold PhiM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : lead ((i : ℕ) + 1) y ≠ 0 := hy i
  rw [muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem phiMul : PhiMul := by
  intro n ε μ t x hx k
  have hy := posDef_conj_toMK k hx
  have h1 := phiM_posDef μ hy
  have h2 := phiM_posDef (Dz n) hy
  refine ⟨h1.1, ?_⟩
  unfold phiK
  rw [phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]
  have e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h1.2])
  have e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h2.2])
  rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

end CompanionTheory.RgFd
end
end

