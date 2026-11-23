module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.CentralScalar
public import Formalism.RealPlaceAnalysis.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.AdjointEquivalence
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

theorem jm_sq {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | h
  · cases hε : ε i <;> simp [Matrix.diagonal_apply, hε]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, h]

theorem jm_jm_mul {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, jm_sq, Matrix.one_mul]

theorem jm_inv {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv (jm_sq ε)

theorem jm_isUnit {n : ℕ} (ε : Fin n → Bool) : IsUnit (Formalism.REAL.Jm ε) := ⟨⟨Formalism.REAL.Jm ε, Formalism.REAL.Jm ε, jm_sq ε, jm_sq ε⟩, rfl⟩

theorem mem_UJset_iff {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := Iff.rfl

theorem exp_mem_UJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ PI.UpqRep.UJset ε := by
  rw [mem_UJset_iff]
  set A : Matrix (Fin n) (Fin n) ℂ := (t : ℂ) • X with hAdef
  have h0 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX
  have hX' : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, jm_sq, Matrix.mul_one]
      _ = _ := by rw [h0, Matrix.neg_mul]
  have hA : Aᴴ = Formalism.REAL.Jm ε * (-A) * (Formalism.REAL.Jm ε)⁻¹ := by
    have ht : star (t : ℂ) = t := Complex.conj_ofReal t
    rw [jm_inv, hAdef, Matrix.conjTranspose_smul, hX', ht]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hcomm : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute (-A) A (Commute.neg_left (Commute.refl A)), neg_add_cancel,
      NormedSpace.exp_zero]
  rw [← Matrix.exp_conjTranspose, hA, Matrix.exp_conj _ _ (jm_isUnit ε), jm_inv]
  calc Formalism.REAL.Jm ε * NormedSpace.exp (-A) * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * NormedSpace.exp A
      = Formalism.REAL.Jm ε * (NormedSpace.exp (-A) * NormedSpace.exp A) := by
        simp only [Matrix.mul_assoc, jm_jm_mul]
    _ = Formalism.REAL.Jm ε := by rw [hcomm, Matrix.mul_one]

end PI.UnitaryGroupMassFormula.DSIC
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open Finset
open scoped Matrix

theorem ofFn_prod_sum {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (t : ℕ) (f : Fin t → ι → R),
      (List.ofFn fun k => ∑ c, f k c).prod = ∑ c : Fin t → ι, (List.ofFn fun k => f k (c k)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_sum t, Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ : Fin (t + 1) => ι).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    simp [List.ofFn_succ, Fin.consEquiv]

theorem ofFn_prod_smul {R : Type*} [Ring R] [Algebra ℂ R] :
    ∀ (t : ℕ) (a : Fin t → ℂ) (x : Fin t → R),
      (List.ofFn fun k => a k • x k).prod = (∏ k, a k) • (List.ofFn x).prod := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    intro a x
    rw [List.ofFn_succ, List.prod_cons, ih, List.ofFn_succ (f := x), List.prod_cons, Fin.prod_univ_succ,
      smul_mul_smul_comm]

theorem intCast_mul_eq {R : Type*} [Ring R] [Algebra ℂ R] (z : ℤ) (y : R) : (z : R) * y = (z : ℂ) • y := by
  rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]

theorem sum_fun_eq_sum_perm {M : Type*} [AddCommMonoid M] {n : ℕ} (f : (Fin n → Fin n) → M)
    (hf : ∀ c, ¬ Function.Injective c → f c = 0) :
    ∑ c, f c = ∑ π : Equiv.Perm (Fin n), f π := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.map ⟨fun π : Equiv.Perm (Fin n) => (π : Fin n → Fin n), DFunLike.coe_injective⟩))]
  · rw [Finset.sum_map]
    rfl
  · intro c _ hc
    apply hf
    intro hinj
    apply hc
    rw [Finset.mem_map]
    exact ⟨Equiv.ofBijective c hinj.bijective_of_finite, Finset.mem_univ _, rfl⟩

def qF {R : Type*} [Ring R] {n : ℕ} (F : ℂ → Fin n → Fin n → R) (u : ℂ) : R :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) * (List.ofFn fun k : Fin n => F (u - (k : ℂ)) (σ k) k).prod

theorem qdet_eq_qF {R : Type*} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R) (u : ℂ) :
    Formalism.REAL.qdet E u = qF (Formalism.REAL.Tm E) u := rfl

theorem det_sub_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) :
    ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, A (σ k) (c k) = (A.submatrix id c).det := by
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  rfl

theorem det_sub_noninj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → Fin n) (hc : ¬ Function.Injective c) :
    (A.submatrix id c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hc
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])

theorem qF_row {R : Type*} [Ring R] [Algebra ℂ R] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : ℂ → Fin n → Fin n → R) (u : ℂ) :
    qF (fun x a b => ∑ c, A a c • F x c b) u = A.det • qF F u := by
  classical
  unfold qF
  simp_rw [ofFn_prod_sum, ofFn_prod_smul, intCast_mul_eq, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, det_sub_eq]
  rw [sum_fun_eq_sum_perm (fun c => (A.submatrix id c).det • (List.ofFn fun k : Fin n => F (u - (k : ℂ)) (c k) k).prod)
    (fun c hc => by rw [det_sub_noninj A c hc, zero_smul])]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Matrix.det_permute', mul_comm, mul_smul]

theorem qF_col {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (E : Fin n → Fin n → R) (hE : Formalism.REAL.GlRel E)
    (B : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) :
    qF (fun x a b => ∑ d, B d b • Formalism.REAL.Tm E x a d) u = B.det • Formalism.REAL.qdet E u := by
  classical
  have hperm : ∀ π : Equiv.Perm (Fin n), Formalism.REAL.qminor E id (π : Fin n → Fin n) u =
      ((Equiv.Perm.sign π : ℤ) : R) * Formalism.REAL.qdet E u :=
    fun π => Formalism.REAL.qSkewCol R n n E hE id id π u
  have hzero : ∀ d : Fin n → Fin n, ¬ Function.Injective d → Formalism.REAL.qminor E id d u = 0 := by
    intro d hd
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hd
    have hsw : d ∘ (Equiv.swap i j) = d := by
      funext k
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · rw [h1, hij]
      · rw [h2, hij]
      · rfl
    have h := Formalism.REAL.qSkewCol R n n E hE id d (Equiv.swap i j) u
    rw [hsw, Equiv.Perm.sign_swap hne] at h
    have h2 : (2 : ℂ) • Formalism.REAL.qminor E id d u = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      simp
    calc Formalism.REAL.qminor E id d u = (1 / 2 : ℂ) • ((2 : ℂ) • Formalism.REAL.qminor E id d u) := by
          rw [smul_smul]; norm_num
      _ = 0 := by rw [h2, smul_zero]
  unfold qF
  simp_rw [ofFn_prod_sum, ofFn_prod_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum]
  have hq : ∀ d : Fin n → Fin n, (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : R) *
      (List.ofFn fun k : Fin n => Formalism.REAL.Tm E (u - (k : ℂ)) (σ k) (d k)).prod) = Formalism.REAL.qminor E id d u :=
    fun d => rfl
  simp_rw [hq]
  rw [sum_fun_eq_sum_perm (fun d => (∏ k, B (d k) k) • Formalism.REAL.qminor E id d u)
    (fun d hd => by rw [hzero d hd, smul_zero])]
  simp_rw [hperm, intCast_mul_eq, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul, mul_comm]

theorem quasi_determinant_conj_inv : QdetConjInv := by
  intro A _ _ n E hE g hg u
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hT : (Formalism.REAL.Tm fun a b => ∑ c, ∑ d, (g c a * g⁻¹ b d) • E c d) =
      fun x a b => ∑ c, gᵀ a c • ∑ d, (g⁻¹)ᵀ d b • Formalism.REAL.Tm E x c d := by
    funext x a b
    simp only [Formalism.REAL.Tm, Matrix.transpose_apply, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    congr 1
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← Finset.sum_smul]
    have h1 : ∑ c, g c a * g⁻¹ b c = (g⁻¹ * g) b a := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [h1, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  rw [qdet_eq_qF, hT, qF_row, qF_col E hE, smul_smul, Matrix.det_transpose, Matrix.det_transpose,
    ← Matrix.det_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.det_one, one_smul]

end PI.UnitaryGroupMassFormula.DSIC
end
end

