module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open scoped Matrix Kronecker in
private theorem adMeas_pi {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝔸[K]) (u : (𝔸[K])ˣ) (hu : (u : 𝔸[K]) = M.det) :
    (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K).map (fun x => x ᵥ* M) =
      ENNReal.ofReal ((GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ))⁻¹ •
        Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K := by
  let σ := Fintype.equivFin ι
  have hd : (Matrix.reindex σ σ M).det = u := by rw [Matrix.det_reindex_self, hu]
  let g : GL (Fin (Fintype.card ι)) 𝔸[K] :=
    Matrix.GeneralLinearGroup.mk'' (Matrix.reindex σ σ M) (hd ▸ u.isUnit)
  have hg : (g : Matrix _ _ 𝔸[K]) = Matrix.reindex σ σ M := rfl
  have hdet : Matrix.GeneralLinearGroup.det g = u := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hd])
  have h := GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  rw [hdet] at h
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => 𝔸[K]) σ
  have hE : MeasurePreserving E (Measure.pi fun _ : ι => GroundTheory.Global.adeleMeasure K)
      (GJMatrix.adeleMeasurePi K) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => GroundTheory.Global.adeleMeasure K) σ
  have hfun : (fun x : ι → 𝔸[K] => x ᵥ* M) =
      E.symm ∘ (fun x => x ᵥ* (g : Matrix _ _ 𝔸[K])) ∘ E := by
    funext x
    have hx : E x = x ∘ σ.symm := by
      funext i
      obtain ⟨j, rfl⟩ := σ.surjective i
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    funext i
    change _ = (E x ᵥ* (g : Matrix _ _ 𝔸[K])) (σ i)
    rw [hx, hg, Matrix.reindex_apply, Matrix.submatrix_vecMul_equiv]
    simp [Function.comp_assoc]
  have hm := GJGlobal.Modulus.measurable_vecMul' g
  rw [hfun, ← Measure.map_map E.symm.measurable (hm.comp E.measurable),
    ← Measure.map_map hm E.measurable, hE.map_eq, h, Measure.map_smul, hE.symm.map_eq]
  exact E.symm.measurable.aemeasurable

private def adMeas_tau : Fin 2 × Fin 2 ≃ UPos (2 + 2) 2 where
  toFun p := ⟨(Fin.castAdd 2 p.1, Fin.natAdd 2 p.2), p.1.2, Nat.le_add_right _ _⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩)
  left_inv := by decide
  right_inv := by decide

private theorem adMeas_unip {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 1 (Matrix.of fun i j => X (adMeas_tau (i, j))) 0 1) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] <;>
    fin_cases i <;> fin_cases j <;> simp [adMeas_tau, Fin.ext_iff]

open scoped Matrix Kronecker in
private noncomputable def adMeas_M {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    Matrix (UPos (2 + 2) 2) (UPos (2 + 2) 2) R :=
  Matrix.reindex adMeas_tau adMeas_tau (((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)ᵀ ⊗ₖ (b : Matrix (Fin 2) (Fin 2) R))

private theorem adMeas_M_mul {R : Type} [CommRing R] (a b : GL (Fin 2) R) :
    adMeas_M a b * adMeas_M a⁻¹ b⁻¹ = 1 := by
  simp only [adMeas_M, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, ← Units.val_mul, ← Units.val_mul]
  simp

open scoped Matrix in
private theorem adMeas_conj {R : Type} [CommRing R] (a b : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    unipGL X * blk a b = blk a b * unipGL (X ᵥ* adMeas_M a b) := by
  have h : (Matrix.of fun i j => (X ᵥ* adMeas_M a b) (adMeas_tau (i, j))) =
      ((a⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (Matrix.of fun i j => X (adMeas_tau (i, j))) *
        (b : Matrix (Fin 2) (Fin 2) R) := by
    ext i j
    rw [adMeas_M, Matrix.reindex_apply, Matrix.of_apply, Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, Matrix.vecMul, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
      Matrix.of_apply, Fin.sum_univ_two]
    ring
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, adMeas_unip, adMeas_unip, h]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
  simp

open scoped Matrix in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.adMeas :
    ∀ {K : Type} [Field K] [NumberField K] (m₁ m₂ : G1 K 2) (t : ℝ),
    ∃ e : (UPos (2 + 2) 2 → 𝔸[K]) ≃ₜ+ (UPos (2 + 2) 2 → 𝔸[K]),
      (∀ X, unipOne (K := K) (n := 2 + 2) 2 X * lv m₁ m₂ t =
        lv m₁ m₂ t * unipOne (K := K) (n := 2 + 2) 2 (e X)) ∧
      (unipMeasure K (2 + 2) 2).map e = ENNReal.ofReal (Real.exp (4 * t)) • unipMeasure K (2 + 2) 2 := by
  intro K _ _ m₁ m₂ t
  set a : AdelicGLn.AdelicGL K 2 := (m₁ : AdelicGLn.AdelicGL K 2) * zt K t with ha
  set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
  have h2 : adMeas_M a⁻¹ b⁻¹ * adMeas_M a b = 1 := by
    simpa using adMeas_M_mul a⁻¹ b⁻¹
  refine ⟨{ toFun := fun X => X ᵥ* adMeas_M a b
            invFun := fun X => X ᵥ* adMeas_M a⁻¹ b⁻¹
            left_inv := fun X => by simp only [Matrix.vecMul_vecMul, adMeas_M_mul, Matrix.vecMul_one]
            right_inv := fun X => by simp only [Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
            map_add' := fun X Y => Matrix.add_vecMul _ _ _
            continuous_toFun := continuous_id.matrix_vecMul continuous_const
            continuous_invFun := continuous_id.matrix_vecMul continuous_const }, fun X => ?_, ?_⟩
  · refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1 m₁ m₂ t]
    exact adMeas_conj a b X
  · have hm : ∀ (m : G1 K 2) (s : ℝ),
        (detModule K 2 ((m : AdelicGLn.AdelicGL K 2) * zt K s) : ℝ) = Real.exp s := by
      intro m s
      rw [map_mul, mem_normOneGL_iff_detModule.1 m.2, one_mul, zt, detModule_centralSection two_pos]
    have h := adMeas_pi (adMeas_M a b)
      (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) (by
        rw [adMeas_M, Matrix.det_reindex_self, Matrix.det_kronecker, Matrix.det_transpose]
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply,
          Fintype.card_fin])
    have hv : ((GroundTheory.Global.IdeleGroup.ideleModule K
        (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) : ℝ))⁻¹ =
        Real.exp (4 * t) := by
      have e1 : GroundTheory.Global.IdeleGroup.ideleModule K
          (Matrix.GeneralLinearGroup.det a⁻¹ ^ 2 * Matrix.GeneralLinearGroup.det b ^ 2) =
          (detModule K 2 a)⁻¹ ^ 2 * detModule K 2 b ^ 2 := by
        rw [map_mul, map_pow, map_pow, ← map_inv (detModule K 2)]
        rfl
      rw [e1, Positive.val_mul, Positive.val_pow, Positive.val_pow, Positive.coe_inv, hm, hm,
        ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    rw [hv] at h
    exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.IsoExt
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem gramExt {ι E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (a : ι → E) (b : ι → H)
    (hd : Dense ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E))
    (hg : ∀ i j, ⟪b i, b j⟫_ℂ = ⟪a i, a j⟫_ℂ) : ∃ J : E →ₗᵢ[ℂ] H, ∀ i, J (a i) = b i := by
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hden : DenseRange A := by
    have : Set.range A = ((Submodule.span ℂ (Set.range a) : Submodule ℂ E) : Set E) := by
      rw [← Finsupp.range_linearCombination, LinearMap.coe_range]
    rw [DenseRange, this]; exact hd
  have hin : ∀ x y, ⟪B x, B y⟫_ℂ = ⟪A x, A y⟫_ℂ := by
    intro x y
    simp only [A, B, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, hg]
  have hn : ∀ x, ‖B x‖ = ‖A x‖ := by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hin]
  have hb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C * ‖A x‖ := ⟨1, fun x => by rw [one_mul, hn]⟩
  have h1 : ∀ x, (B.extendOfNorm A) (A x) = B x := fun x => LinearMap.extendOfNorm_eq hden hb x
  refine ⟨⟨(B.extendOfNorm A).toLinearMap, fun u => ?_⟩, fun i => ?_⟩
  · refine hden.induction_on (p := fun u => ‖(B.extendOfNorm A) u‖ = ‖u‖) u ?_ ?_
    · exact isClosed_eq (B.extendOfNorm A).continuous.norm continuous_norm
    · intro x; rw [h1, hn]
  · have := h1 (Finsupp.single i 1)
    simpa [A, B] using this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.isoExt :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℕ) (T : (ℝ → ℂ) → Eu d → H),
      (∀ β β' v v', Continuous β → HasCompactSupport β → Continuous β' → HasCompactSupport β' → ⟪T β v, T β' v'⟫_ℂ = (∫ t, conj (β t) * β' t) * ⟪v, v'⟫_ℂ) →
      ∃ J : L (Eu d) →ₗᵢ[ℂ] H, ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ᵐ x : ℝ, u x = β x • v) → J u = T β v := by
  intro H _ _ _ d T hT
  let ι := {p : (ℝ → ℂ) × Eu d × L (Eu d) //
    Continuous p.1 ∧ HasCompactSupport p.1 ∧ ∀ᵐ x : ℝ, p.2.2 x = p.1 x • p.2.1}
  obtain ⟨J, hJ⟩ := gramExt (ι := ι) (fun p => p.1.2.2) (fun p => T p.1.1 p.1.2.1) (by
    have h := (UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc d).1
    refine h.mono (SetLike.coe_subset_coe.2 (Submodule.span_mono ?_))
    rintro u ⟨β, v, h⟩
    exact ⟨⟨(β, v, u), h⟩, rfl⟩) (by
    rintro ⟨⟨β, v, u⟩, h1, h2, h3⟩ ⟨⟨β', v', u'⟩, h1', h2', h3'⟩
    dsimp only at *
    rw [hT β β' v v' h1 h2 h1' h2', MeasureTheory.L2.inner_def, ← integral_mul_const]
    refine integral_congr_ae ?_
    filter_upwards [h3, h3'] with x e e'
    rw [e, e', inner_smul_left, inner_smul_right, mul_assoc])
  exact ⟨J, fun β v u h1 h2 h3 => hJ ⟨(β, v, u), h1, h2, h3⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Ring

variable {R : Type} [CommRing R]

private def Low (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) : Prop :=
  ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → M i j = 0

private theorem low_mul {M N : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R} (hM : Low M) (hN : Low N) : Low (M * N) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < 2
  · rw [hM i k hi hk, zero_mul]
  · rw [hN k j (not_lt.1 hk) hj, mul_zero]

private theorem low_blocks (A B D : Matrix (Fin 2) (Fin 2) R) :
    Low (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B 0 D)) := by
  intro i j hi hj
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rcases i with i | i
  · exact absurd (show 2 ≤ (i : ℕ) from hi) (not_le.2 i.2)
  rcases j with j | j
  · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
  · exact absurd (show 2 + (j : ℕ) < 2 from hj) (by omega)

private def xm (X : UPos (2 + 2) 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), i.2, Nat.le_add_right 2 j⟩

private theorem unip_eq (X : UPos (2 + 2) 2 → R) :
    unipMatrix X = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (xm X) 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, xm] <;> rfl

private theorem xm_bij : Function.Bijective (xm : (UPos (2 + 2) 2 → R) → _) := by
  constructor
  · intro X Y h
    apply unipGL_injective
    apply Units.ext
    rw [coe_unipGL, coe_unipGL, unip_eq, unip_eq, h]
  · intro B
    refine ⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩
    ext i j
    simp [xm]

private theorem unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (xm X * b.val) 0 b.val) := by
  rw [Units.val_mul, coe_unipGL, unip_eq]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem unip_blk_inj {X X' : UPos (2 + 2) 2 → R} {a b a' b' : GL (Fin 2) R}
    (h : unipGL X * blk a b = unipGL X' * blk a' b') : X = X' ∧ a = a' ∧ b = b' := by
  have h1 := congrArg Units.val h
  rw [unip_blk, unip_blk] at h1
  obtain ⟨ha, hx, -, hb⟩ := Matrix.fromBlocks_inj.1 ((Matrix.reindex _ _).injective h1)
  obtain rfl : b = b' := Units.ext hb
  exact ⟨xm_bij.1 ((Units.mul_left_inj b).1 hx), Units.ext ha, rfl⟩

private theorem low_inv_unip_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    Low (((unipGL X * blk a b)⁻¹ : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) := by
  rw [mul_inv_rev, Units.val_mul, coe_unipGL_inv, unip_eq]
  exact low_mul (low_blocks _ _ _) (low_blocks _ _ _)

end Ring

private theorem low_decomp {K : Type} [Field K] (g : GL (Fin (2 + 2)) K) (hg : Low g.val) :
    ∃ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K), g = unipGL X * blk a b := by
  set M := (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm g.val with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    exact hg _ _ (Nat.le_add_right 2 i) j.2
  have hb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hd : M.det ≠ 0 := by
    rw [hM, Matrix.reindex_symm, Matrix.det_reindex_self]
    exact g.det_ne_zero
  rw [hb, Matrix.det_fromBlocks_zero₂₁, mul_ne_zero_iff] at hd
  let a := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.1
  let b := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd.2
  obtain ⟨X, hX⟩ := xm_bij.2 (M.toBlocks₁₂ * (b⁻¹).val)
  refine ⟨X, a, b, Units.ext ?_⟩
  rw [unip_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  change _ = Matrix.reindex _ _ (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂)
  rw [← hb, hM, Equiv.apply_symm_apply]

variable {K : Type} [Field K] [NumberField K]

private theorem diag_blk (a b : GL (Fin 2) K) :
    AdelicGLn.diagonal K (2 + 2) (blk a b) = blk (AdelicGLn.diagonal K 2 a) (AdelicGLn.diagonal K 2 b) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rw [AdelicGLn.diagonal_apply]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  congr 1
  exact Subtype.ext Real.exp_zero

private theorem low_diag (g : GL (Fin (2 + 2)) K) : Low (AdelicGLn.diagonal K (2 + 2) g).val ↔ Low g.val :=
  forall_congr' fun i => forall_congr' fun j => forall_congr' fun _ => forall_congr' fun _ => by
    rw [AdelicGLn.diagonal_apply]
    exact map_eq_zero_iff _ (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K)

private theorem gam_cases {n : ℕ} (γ : Gam K n) : ∃ g : GL (Fin n) K,
    γ = ⟨⟨AdelicGLn.diagonal K n g, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, g, rfl⟩ := by
  obtain ⟨g, hg⟩ := γ.2
  exact ⟨g, Subtype.ext (Subtype.ext hg.symm)⟩

private def lowΓ (K : Type) [Field K] [NumberField K] : Subgroup (Gam K (2 + 2)) where
  carrier := {γ | Low ((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)).val}
  one_mem' := by
    intro i j hi hj
    exact Matrix.one_apply_ne (by rintro rfl; omega)
  mul_mem' ha hb := low_mul ha hb
  inv_mem' := by
    intro γ hg
    obtain ⟨g, rfl⟩ := gam_cases γ
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    change Low (AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b))⁻¹.val
    rw [← map_inv, low_diag]
    exact low_inv_unip_blk X a b

private theorem par_eq : ParΓ K 2 2 = lowΓ K := Subgroup.closure_eq (lowΓ K)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ γ : Gam K (2 + 2), γ ∈ ParΓ K 2 2 ↔ ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
        (((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = 0) ∧
      (∀ γ : G1 K (2 + 2), γ ∈ PK K ↔ ∃ (ξ : unipLattice K (2 + 2) 2) (γ₁ : Gam K 2) (γ₂ : Gam K 2),
        γ = unipOne (K := K) (n := 2 + 2) 2 ξ.1 * lv γ₁ γ₂ 0) ∧
      (∀ (ξ ξ' : UPos (2 + 2) 2 → 𝔸[K]) (a b a' b' : G1 K 2) (t t' : ℝ),
        unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t =
          unipOne (K := K) (n := 2 + 2) 2 ξ' * lv a' b' t' → ξ = ξ' ∧ a = a' ∧ b = b' ∧ t = t') ∧
      ∀ γ : Gam K (2 + 2), ∃ δ ∈ PK K, (((Quotient.mk _ γ : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) = δ * γ := by
  intro K _ _
  have hlv := (blkLaws (K := K)).1
  have hco : ∀ (ξ : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) (t : ℝ),
      ((unipOne (K := K) (n := 2 + 2) 2 ξ * lv a b t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        unipGL ξ * blk ((a : AdelicGLn.AdelicGL K 2) * zt K t) ((b : AdelicGLn.AdelicGL K 2) * zt K (-t)) :=
    fun ξ a b t => by rw [Subgroup.coe_mul, hlv, coe_unipOne]
  have hdg : ∀ (X : UPos (2 + 2) 2 → K) (a b : GL (Fin 2) K) (h₁ h₂),
      ((unipOne (K := K) (n := 2 + 2) 2 (fun p => algebraMap K 𝔸[K] (X p)) *
        lv ⟨AdelicGLn.diagonal K 2 a, h₁⟩ ⟨AdelicGLn.diagonal K 2 b, h₂⟩ 0 :
        G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = AdelicGLn.diagonal K (2 + 2) (unipGL X * blk a b) :=
    fun X a b h₁ h₂ => by rw [hco, neg_zero, zt_zero, mul_one, mul_one, map_mul, diag_blk, diagonal_unipGL]
  refine ⟨fun γ => by rw [par_eq]; rfl, fun γ => ⟨?_, ?_⟩, ?_, fun γ => ?_⟩
  · rintro ⟨γ, hg, rfl⟩
    obtain ⟨g, rfl⟩ := gam_cases γ
    rw [par_eq] at hg
    obtain ⟨X, a, b, rfl⟩ := low_decomp g ((low_diag g).1 hg)
    exact ⟨⟨_, X, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨a, rfl⟩⟩, a, rfl⟩, ⟨⟨_, rationalGL_le_normOneGL ⟨b, rfl⟩⟩, b, rfl⟩,
      Subtype.ext (hdg X a b _ _).symm⟩
  · rintro ⟨⟨_, X, rfl⟩, γ₁, γ₂, rfl⟩
    obtain ⟨a, rfl⟩ := gam_cases γ₁
    obtain ⟨b, rfl⟩ := gam_cases γ₂
    have h₁ : AdelicGLn.diagonal K 2 a ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨a, rfl⟩
    have h₂ : AdelicGLn.diagonal K 2 b ∈ normOneGL (K := K) (n := 2) := rationalGL_le_normOneGL ⟨b, rfl⟩
    refine ⟨⟨_, unipGL X * blk a b, (hdg X a b h₁ h₂).symm⟩, ?_, rfl⟩
    rw [par_eq]
    change Low (Units.val _)
    have h := (low_diag (unipGL X * blk a b)).2 (by rw [unip_blk]; exact low_blocks _ _ _)
    rw [← hdg X a b h₁ h₂] at h
    exact h
  · intro ξ ξ' a b a' b' t t' h
    have h1 := congrArg Subtype.val h
    rw [hco, hco] at h1
    obtain ⟨hx, ha, hb⟩ := unip_blk_inj h1
    have h2 := congrArg (detModule K 2) ha
    rw [map_mul, map_mul, mem_normOneGL_iff_detModule.1 a.2, mem_normOneGL_iff_detModule.1 a'.2, one_mul, one_mul,
      zt, zt, detModule_centralSection two_pos, detModule_centralSection two_pos] at h2
    obtain rfl : t = t' := Real.exp_injective (congrArg Subtype.val h2)
    exact ⟨hx, Subtype.ext (mul_right_cancel ha), Subtype.ext (mul_right_cancel hb), rfl⟩
  · have h : (QuotientGroup.rightRel (ParΓ K 2 2)) γ (Quotient.mk _ γ : Cos K).out :=
      Quotient.exact (Quotient.out_eq _).symm
    rw [QuotientGroup.rightRel_apply] at h
    refine ⟨_, ⟨_, h, rfl⟩, ?_⟩
    simp
end

