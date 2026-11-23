module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeightBlockEmbeddingLe
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem ent_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) {c : ℝ}
    (hc : 1 ≤ c) (h : ∀ i j, ‖g.val i j‖ ≤ c) (i j : Fin n) : ‖(emb e g).val i j‖ ≤ c := by
  have hone : ∀ p q : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) p q‖ ≤ c := by
    intro p q
    rw [Matrix.one_apply]
    split_ifs <;> simp [hc, zero_le_one.trans hc]
  show ‖((emb e g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j‖ ≤ c
  rw [coe_emb, Matrix.add_apply]
  by_cases hi : ∃ k, i = e k
  · by_cases hj : ∃ l, j = e l
    · obtain ⟨k, rfl⟩ := hi
      obtain ⟨l, rfl⟩ := hj
      simp only [matrixExtendByZero_apply, Matrix.sub_apply, Matrix.one_apply, e.injective.eq_iff, add_sub_cancel]
      exact h k l
    · push_neg at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ i hj, add_zero]
      exact hone i j
  · push_neg at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, add_zero]
    exact hone i j

private theorem loc_le {E : Type} [NormedField E] {a n : ℕ} (e : Fin a ↪ Fin n) (g : GL (Fin a) E) :
    locHeight (emb e g) ≤ locHeight g := by
  apply locHeight_le (one_le_locHeight g)
  · exact ent_le e g (one_le_locHeight g) (norm_apply_le_locHeight g)
  · intro i j
    rw [← map_inv]
    exact ent_le e g⁻¹ (one_le_locHeight g) (norm_inv_apply_le_locHeight g) i j

theorem UpperTheory.height_blockEmbedding_le :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (g : AdelicGLn.AdelicGL K a), AutomorphicForm.height (emb e g) ≤ AutomorphicForm.height g := by
  classical
  intro K _ _ a n e g
  have hfin : ∀ v, Reduction.finAt v (emb e g) = emb e (Reduction.finAt v g) := by
    intro v
    show Matrix.GeneralLinearGroup.map (Reduction.finEval v) (emb e g) = _
    rw [emb_map]
    rfl
  have hinf : ∀ w, Reduction.infAt w (emb e g) = emb e (Reduction.infAt w g) := by
    intro w
    show Matrix.GeneralLinearGroup.map (Reduction.infEval w) (emb e g) = _
    rw [emb_map]
    rfl
  unfold AutomorphicForm.height
  simp only [hfin, hinf]
  apply mul_le_mul
  · apply Finset.prod_le_prod₀
    · intro w _
      exact pow_nonneg (locHeight_pos _).le _
    · intro w _
      exact pow_le_pow_left₀ (locHeight_pos _).le (loc_le e _) _
  · have h1 := finite_mulSupport_locHeight_finAt (emb e g)
    have h2 := finite_mulSupport_locHeight_finAt g
    simp only [hfin] at h1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx]),
      finprod_eq_prod_of_mulSupport_subset _ (s := h1.toFinset ∪ h2.toFinset)
        (by intro x hx; simp [hx])]
    apply Finset.prod_le_prod₀
    · intro v _
      exact (locHeight_pos _).le
    · intro v _
      exact loc_le e _
  · exact finprod_nonneg fun v => (locHeight_pos _).le
  · exact (zero_lt_one.trans_le (one_le_prod_locHeight g)).le
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LieMapEqSumIdempotentGen
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.lieMap_eq_sum_idempotent_gen :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (X : Matrix (Fin n) (Fin n) R), l X = ∑ τ, ∑ i, ∑ j, D.ch τ (X i j) • gen D l τ i j := by
  intro R _ _ ι _ n A _ _ _ _ D l X
  have key : ∀ i j, ∑ τ, D.ch τ (X i j) • gen D l τ i j = l (Matrix.single i j (X i j)) := by
    intro i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gen, ← map_smul, ← map_sum, ← D.mul_e, ← Finset.mul_sum, D.sum, mul_one,
      unitMap_tmul, one_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext i
    rw [Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [key, ← map_sum]
  congr 1
  exact Matrix.matrix_eq_sum_single X
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocallyFiniteOfAlgModCriterion
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.locallyFinite_of_algMod_criterion :
    ∀ (X Y : Type) [MeasurableSpace X] (μ : Measure X) (V : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V → ∀ F : X → Y → ℂ, (∀ x, F x ∈ V) → (∀ y, Integrable (fun x => F x y) μ) → (fun y => ∫ x, F x y ∂μ) ∈ V := by
  intro X Y _ μ V hV F hF hI
  classical
  let ev : Y → (V →ₗ[ℂ] ℂ) := fun y => (LinearMap.proj y).comp V.subtype
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    by_contra h
    apply hz
    ext y
    by_contra hy
    exact h ⟨ev y, ⟨y, rfl⟩, hy⟩
  have hint : ∀ φ : V →ₗ[ℂ] ℂ, Integrable (fun x => φ ⟨F x, hF x⟩) μ := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem f hf => obtain ⟨y, rfl⟩ := hf; exact hI y
    | zero => simp
    | add f g _ _ hf hg => exact hf.add hg
    | smul c f _ hf => exact hf.const_mul c
  let b := Module.finBasis ℂ V
  have key : (fun y => ∫ x, F x y ∂μ)
      = ∑ i, (∫ x, b.coord i ⟨F x, hF x⟩ ∂μ) • ((b i : V) : Y → ℂ) := by
    funext y
    have h1 : ∀ x, F x y = ∑ i, b.coord i ⟨F x, hF x⟩ * ((b i : V) : Y → ℂ) y := by
      intro x
      have h := congrArg (ev y) (b.sum_repr ⟨F x, hF x⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    simp only [h1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun i _ => (hint (b.coord i)).mul_const _)]
    exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  rw [key]
  exact V.sum_mem fun i _ => V.smul_mem _ (b i).2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UActionMemUnipotentInvariant
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.uAction_mem_unipotentInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (u : UEnv K n), ∀ ψ ∈ NInv K n r, uAction u ψ ∈ NInv K n r := by
  intro K _ _ n r u ψ hψ X g
  have h : ∀ y, ψ.1 (unipGL X * y) = ψ.1 y := hψ X
  have e : sliceL (unipGL X * g) ψ = sliceL g ψ :=
    Subtype.ext (funext fun x => by simp only [coe_sliceL, archSlice_apply, mul_assoc, h])
  simp only [coe_uAction, uActFun, e]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpperTriangularEqUnipotentMulLevi
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem cn_ne {r s : ℕ} (i : Fin r) (j : Fin s) : Fin.castAdd s i ≠ Fin.natAdd r j := fun h => by
  have := congrArg Fin.val h
  simp at this
  omega

private theorem block_embedding_first_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R) :
    (emb (e1 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks m.val 0 0 1) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have h0 : ext0 (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a) (Fin.castAdd s c) =
          ((m : Matrix (Fin r) (Fin r) R) - 1) a c :=
        matrixExtendByZero_apply (e1 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁, Matrix.sub_apply,
        Matrix.one_apply, Fin.castAdd_inj]
      ring
    | right d =>
      have := matrixExtendByZero_apply_of_outside_col (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (Fin.castAdd s a)
        (j := Fin.natAdd r d) (fun k h => cn_ne k d (by simpa [e1] using h.symm))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne]
  | right b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e1 r s) ((m : Matrix (Fin r) (Fin r) R) - 1) (i := Fin.natAdd r b)
      (fun k h => cn_ne k b (by simpa [e1] using h.symm)) j
    induction j using Fin.addCases with
    | left c => simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem block_embedding_second_val {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin s) R) :
    (emb (e2 r s) m).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 m.val) := by
  rw [coe_emb]
  ext i j
  induction i using Fin.addCases with
  | right a =>
    induction j using Fin.addCases with
    | right c =>
      have h0 : ext0 (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a) (Fin.natAdd r c) =
          ((m : Matrix (Fin s) (Fin s) R) - 1) a c :=
        matrixExtendByZero_apply (e2 r s) _ a c
      simp only [Matrix.add_apply, h0, Matrix.reindex_apply, Matrix.submatrix_apply,
        finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂, Matrix.sub_apply,
        Matrix.one_apply, Fin.natAdd_inj]
      ring
    | left d =>
      have := matrixExtendByZero_apply_of_outside_col (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (Fin.natAdd r a)
        (j := Fin.castAdd s d) (fun k h => cn_ne d k (by simpa [e2] using h))
      simp [Matrix.reindex_apply, this, Matrix.one_apply, (cn_ne d a).symm]
  | left b =>
    have := extendByZero_apply_eq_zero_of_row_not_mem (e2 r s) ((m : Matrix (Fin s) (Fin s) R) - 1) (i := Fin.castAdd s b)
      (fun k h => cn_ne b k (by simpa [e2] using h)) j
    induction j using Fin.addCases with
    | right c => simp [Matrix.reindex_apply, this, Matrix.one_apply, cn_ne b c]
    | left d => simp [Matrix.reindex_apply, this, Matrix.one_apply]

private theorem unip_val {R : Type} [CommRing R] {r s : ℕ} (Y : Matrix (Fin r) (Fin s) R) :
    ∃ X : UPos (r + s) r → R,
      unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 Y 0 1) := by
  refine ⟨fun p => Y ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - r, by have := p.1.2.isLt; have := p.2.2; omega⟩, ?_⟩
  ext i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply]
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left c =>
      have : ¬ (r ≤ ((Fin.castAdd s c : Fin (r + s)) : ℕ)) := by simp
      simp [this, Matrix.reindex_apply, Matrix.one_apply]
    | right d =>
      have h : ((Fin.castAdd s a : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r d : Fin (r + s)) : ℕ) := by
        simp
      rw [dite_eq_left h]
      simp [Matrix.reindex_apply, Matrix.one_apply, cn_ne]
  | right b =>
    have : ¬ (((Fin.natAdd r b : Fin (r + s)) : ℕ) < r) := by simp
    induction j using Fin.addCases with
    | left c => simp [this, Matrix.reindex_apply, Matrix.one_apply, (cn_ne c b).symm]
    | right d => simp [this, Matrix.reindex_apply, Matrix.one_apply]

theorem UpperTheory.upperTriangular_eq_unipotent_mul_levi :
    ∀ (R : Type) [CommRing R] (r s : ℕ) (b : GL (Fin (r + s)) R), b.val.IsUpperTriangular → ∃ (X : UPos (r + s) r → R) (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R), b = unipGL X * blk m₁ m₂ := by
  intro R _ r s b hb
  set M : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R :=
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm b.val with hMdef
  have hC : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hMdef, Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    apply hb
    simp [Fin.lt_def]
    omega
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← hC]
    exact (Matrix.fromBlocks_toBlocks M).symm
  have hbM : b.val = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    simp [hMdef]
  have hdet : IsUnit (Matrix.det M) := by
    rw [hMdef, Matrix.det_reindex_self]
    exact (Matrix.GeneralLinearGroup.det b).isUnit
  rw [hM, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit M.toBlocks₂₂.det := isUnit_of_mul_isUnit_right hdet
  obtain ⟨X, hX⟩ := unip_val (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹)
  refine ⟨X, Matrix.nonsingInvUnit _ hA, Matrix.nonsingInvUnit _ hD, ?_⟩
  have hmul : ∀ P Q : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv P * Matrix.reindex finSumFinEquiv finSumFinEquiv Q =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (P * Q) := by
    intro P Q
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  apply Units.ext
  rw [Units.val_mul, coe_unipGL, hX, blk, Units.val_mul, block_embedding_first_val, block_embedding_second_val, hbM, ← mul_assoc, hmul, hmul]
  congr 1
  conv_lhs => rw [hM]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h1 : (Matrix.nonsingInvUnit _ hA : Matrix (Fin r) (Fin r) R) = M.toBlocks₁₁ := rfl
  have h2 : (Matrix.nonsingInvUnit _ hD : Matrix (Fin s) (Fin s) R) = M.toBlocks₂₂ := rfl
  rw [h1, h2]
  simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
end

