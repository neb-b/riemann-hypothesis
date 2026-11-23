module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.DenseCc
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem ex_rep (d : ℕ) (β : ℝ → ℂ) (v : Eu d) (hβ : Continuous β) (hc : HasCompactSupport β) :
    ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v := by
  have h1 : Continuous fun x => β x • v := hβ.smul continuous_const
  have h2 : HasCompactSupport fun x => β x • v := hc.smul_right (f' := fun _ => v)
  have h3 : MemLp (fun x => β x • v) 2 (volume : Measure ℝ) := h1.memLp_of_hasCompactSupport h2
  exact ⟨h3.toLp _, h3.coeFn_toLp⟩

private theorem orth_zero (d : ℕ) (U : Set ℝ) (hU : IsOpen U) (w : L (Eu d))
    (hw : ∀ (β : ℝ → ℂ) (v : Eu d) (u : L (Eu d)), Continuous β → HasCompactSupport β → (∀ x, x ∉ U → β x = 0) →
      (∀ᵐ x : ℝ, u x = β x • v) → inner ℂ u w = 0) :
    ∀ᵐ x : ℝ, x ∈ U → w x = 0 := by
  have hli : LocallyIntegrable (fun x => w x) (volume : Measure ℝ) :=
    (Lp.memLp w).locallyIntegrable (by norm_num)
  refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hli.locallyIntegrableOn U) ?_
  intro g hg hc hs
  have hint : Integrable (fun x => g x • w x) (volume : Measure ℝ) :=
    hli.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  refine ext_inner_left ℂ fun v => ?_
  rw [inner_zero_right, ← integral_inner hint]
  have hβ : Continuous fun x => (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hβc : HasCompactSupport fun x => (g x : ℂ) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  obtain ⟨u, hu⟩ := ex_rep d _ v hβ hβc
  have h0 := hw _ v u hβ hβc (fun x hx => by
    have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    simp [this]) hu
  rw [L2.inner_def] at h0
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  rw [hx, inner_smul_left, Complex.conj_ofReal, ← Complex.coe_smul, inner_smul_right]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.denseCc :
    ∀ (d : ℕ), Dense ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d), Continuous β ∧ HasCompactSupport β ∧ ∀ᵐ x : ℝ, u x = β x • v} :
        Submodule ℂ (L (Eu d))) : Set (L (Eu d))) ∧
      (∀ (β : ℝ → ℂ) (v : Eu d), Continuous β → HasCompactSupport β → ∃ u : L (Eu d), ∀ᵐ x : ℝ, u x = β x • v) ∧
      ∀ (s : ℝ) (u : L (Eu d)), (∀ᵐ x : ℝ, x ≤ s → u x = 0) → u ∈ closure ((Submodule.span ℂ {u : L (Eu d) | ∃ (β : ℝ → ℂ) (v : Eu d),
        Continuous β ∧ HasCompactSupport β ∧ (∀ x, x ≤ s → β x = 0) ∧ ∀ᵐ x : ℝ, u x = β x • v} : Submodule ℂ (L (Eu d))) : Set (L (Eu d))) := by
  intro d
  refine ⟨?_, ex_rep d, ?_⟩
  · rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro w hw
    have h := orth_zero d univ isOpen_univ w fun β v u h1 h2 _ h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span ⟨β, v, h1, h2, h4⟩)
    rw [Submodule.mem_bot]
    refine Lp.ext ?_
    filter_upwards [h, Lp.coeFn_zero (Eu d) 2 (volume : Measure ℝ)] with x hx h0
    rw [hx (mem_univ x), h0]
    rfl
  · intro s u hu
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure, SetLike.mem_coe,
      Submodule.mem_orthogonal]
    intro w hw
    have h := orth_zero d (Ioi s) isOpen_Ioi w fun β v u h1 h2 h3 h4 =>
      (Submodule.mem_orthogonal _ _).1 hw u (Submodule.subset_span
        ⟨β, v, h1, h2, fun x hx => h3 x (fun h => not_lt.2 hx h), h4⟩)
    rw [L2.inner_def]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h, hu] with x h1 h2
    rcases le_or_gt x s with hx | hx
    · simp [h2 hx]
    · simp [h1 hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LinAlg
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem rankOne {F : Type} [Field F] (b d : Fin 2 → F) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d 0 * b 0 + d 1 * b 1 = 0) :
    ∃ m : GL (Fin 2) F, Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
  have key : ∀ u0 u1 : F, u0 * b 0 + u1 * b 1 = 1 → ∃ m : GL (Fin 2) F,
      Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
    intro u0 u1 hu
    have hdet : (!![u0, u1; d 0, d 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      intro h0
      apply hd
      funext i
      fin_cases i
      · show d 0 = 0
        linear_combination (-d 0) * hu + u0 * h - b 1 * h0
      · show d 1 = 0
        linear_combination (-d 1) * hu + u1 * h + b 0 * h0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
    rw [Matrix.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.single_apply]
    · linear_combination d 0 * hu
    · linear_combination d 1 * hu
    · linear_combination d 0 * h
    · linear_combination d 1 * h
  by_cases h0 : b 0 = 0
  · have h1 : b 1 ≠ 0 := fun h1 => hb (by funext i; fin_cases i <;> simpa)
    exact key 0 (b 1)⁻¹ (by simp [h1])
  · exact key (b 0)⁻¹ 0 (by simp [h0])

private theorem core {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ) (p q : Fin (2 + 2) → F)
    (hp : ∀ i : Fin (2 + 2), r ≤ (i : ℕ) → (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p i = 0)
    (hq : ∀ j : Fin (2 + 2), (j : ℕ) < r → Matrix.vecMul q γ.val j = 0)
    (h : ((fun i => q (Fin.castAdd 2 i)) = 0 ∧ (fun i => q (Fin.natAdd 2 i)) ≠ 0 ∧ (fun i => p (Fin.natAdd 2 i)) ≠ 0) ∨
      ((fun i => p (Fin.natAdd 2 i)) = 0 ∧ (fun i => p (Fin.castAdd 2 i)) ≠ 0 ∧ (fun i => q (Fin.castAdd 2 i)) ≠ 0)) :
    ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  set l := (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p with hl
  set v := Matrix.vecMul q γ.val with hv
  have hX : blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) = Matrix.vecMulVec l v := by
    ext i j
    rw [blockEntry_apply, Matrix.vecMulVec_apply]
    split_ifs with hij
    · rfl
    · by_cases hi : (i : ℕ) < r
      · rw [hq j (by omega), mul_zero]
      · rw [hp i (by omega), zero_mul]
  have hE : (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) *
      (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.vecMulVec p q := by
    rw [hX, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hl, hv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
      Units.mul_inv, Matrix.one_mulVec, Matrix.vecMul_one]
  have hdot : q ⬝ᵥ p = 0 := by
    have h1 : v ⬝ᵥ l = q ⬝ᵥ p := by
      rw [hl, hv, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · rw [hq i hi, zero_mul]
    · rw [hp i (by omega), mul_zero]
  rw [dotProduct, Fin.sum_univ_add, Fin.sum_univ_two, Fin.sum_univ_two] at hdot
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have h1' : ∀ i, q (Fin.castAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h3 h2 (by simpa only [h1', zero_mul, zero_add] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inl (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', mul_zero,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
  · have h1' : ∀ i, p (Fin.natAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h2 h3 (by simpa only [h1', mul_zero, add_zero] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inr (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', zero_mul,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]

private theorem perp {F : Type} [Field F] (a : Fin 2 → F) (ha : a ≠ 0) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ ∑ i, c i * a i = 0 := by
  refine ⟨![a 1, -a 0], fun h => ha ?_, ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    funext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  · simp [Fin.sum_univ_two]
    ring

private theorem halves {F : Type} [Field F] (p : Fin (2 + 2) → F) (h1 : (fun i => p (Fin.castAdd 2 i)) = 0)
    (h2 : (fun i => p (Fin.natAdd 2 i)) = 0) : p = 0 := by
  funext i
  exact Fin.addCases (fun i => congrFun h1 i) (fun i => congrFun h2 i) i

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.linAlg :
    ∀ {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ), (r = 1 ∨ r = 3 ∨ (r = 2 ∧
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2) ≠ 0 ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det = 0)) →
      ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  intro F _ γ r hr
  have hcol : ∀ k i : Fin (2 + 2), (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s k) i =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i k := fun k i => by
    rw [← Units.inv_mul γ]; rfl
  have hrow : ∀ k j : Fin (2 + 2), Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val k s) γ.val j =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) k j := fun k j => by
    rw [← Units.inv_mul γ]; rfl
  rcases hr with rfl | rfl | ⟨rfl, hne, hdet⟩
  · have hp : ∀ i : Fin (2 + 2), 1 ≤ (i : ℕ) →
        (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s 0) i = 0 := fun i hi => by
      rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      simp at hi
    have h0 : ∀ j : Fin (2 + 2), (j : ℕ) < 1 → j = 0 := fun j hj => Fin.ext (by simpa using hj)
    by_cases hb : (fun i => γ.val (Fin.natAdd 2 i) 0) = 0
    · have ha : (fun i => γ.val (Fin.castAdd 2 i) 0) ≠ 0 := fun ha => by
        have := hcol 0 0
        rw [halves (fun s => γ.val s 0) ha hb] at this
        simp at this
      obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 1 _ (Fin.append c 0) hp (fun j hj => ?_) (Or.inr ⟨hb, ha, by simpa only [Fin.append_left] using hc⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 1 _ (Fin.append 0 c) hp (fun j hj => ?_)
        (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hb⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] using hs
  · have hq : ∀ j : Fin (2 + 2), (j : ℕ) < 3 →
        Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) γ.val j = 0 := fun j hj => by
      rw [hrow, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hj
    have h0 : ∀ j : Fin (2 + 2), 3 ≤ (j : ℕ) → j = 3 := fun j hj => Fin.ext (by
      have := j.2
      show (j : ℕ) = 3
      omega)
    by_cases ha : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.castAdd 2 i)) = 0
    · have hb : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.natAdd 2 i)) ≠ 0 := fun hb => by
        have := hrow 3 3
        rw [halves (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) ha hb, Matrix.zero_vecMul, Matrix.one_apply_eq] at this
        exact zero_ne_one this
      obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 3 (Fin.append 0 c) _ (fun j hj => ?_) hq (Or.inl ⟨ha, hb, by simpa only [Fin.append_right] using hc⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
        mul_comm] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 3 (Fin.append c 0) _ (fun j hj => ?_) hq
        (Or.inr ⟨by funext i; simp only [Fin.append_right], by simpa only [Fin.append_left] using hc, ha⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        mul_comm] using hs
  · obtain ⟨c, hc, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, (fun i => γ.val (Fin.natAdd 2 i) (Fin.castAdd 2 k)) ≠ 0 := by
      by_contra hall
      apply hne
      ext i k
      by_contra hik
      exact hall ⟨k, fun h => hik (congrFun h i)⟩
    refine core γ 2 (fun s => γ.val s (Fin.castAdd 2 k)) (Fin.append 0 c) (fun i hi => ?_) (fun j hj => ?_)
      (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hk⟩)
    · rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      have := k.2
      simp only [Fin.val_castAdd] at hi
      omega
    · have hj' : j = Fin.castAdd 2 ⟨j, hj⟩ := rfl
      rw [hj', Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      exact congrFun hs ⟨j, hj⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PluckOne
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem pluck_cb {F : Type} [Field F] (A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (i i' p q : Fin (2 + 2)) :
    (A * B) i p * (A * B) i' q - (A * B) i q * (A * B) i' p =
      ∑ k, ∑ l, (A i k * A i' l - A i l * A i' k) * (B k p * B l q) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_two]
  ring

private theorem pluck_det {F : Type} [Field F] (A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (k l : Fin (2 + 2)) :
    (A.submatrix (Fin.natAdd 2) ![k, l]).det =
      A (Fin.natAdd 2 0) k * A (Fin.natAdd 2 1) l - A (Fin.natAdd 2 0) l * A (Fin.natAdd 2 1) k := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

private theorem pluck_one {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) :
    ∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∀ k l : Fin (2 + 2), (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) k * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) l -
      (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 0) l * (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) (Fin.natAdd 2 1) k = 0 := by
    intro k l
    by_cases hkl : k = l
    · subst hkl; ring
    · rw [← pluck_det]
      apply h
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have := pluck_cb (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) ((γ⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F)
    (Fin.natAdd 2 0) (Fin.natAdd 2 1) (Fin.natAdd 2 0) (Fin.natAdd 2 1)
  rw [Units.mul_inv] at this
  simp only [hz, zero_mul, Finset.sum_const_zero] at this
  have hne : (Fin.natAdd 2 (0 : Fin 2) : Fin (2 + 2)) ≠ Fin.natAdd 2 1 := by decide
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hne] at this
  simp at this

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.pluck :
    ∀ {F : Type} [Field F] (γ γ' : GL (Fin (2 + 2)) F),
      (∃ c : Fin 2 → Fin (2 + 2), Function.Injective c ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det ≠ 0) ∧
      ∀ a : F, (∀ c : Fin 2 → Fin (2 + 2), ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det =
          a * ((γ' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) c).det) →
        ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 → ((γ * γ'⁻¹ : GL (Fin (2 + 2)) F) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i j = 0 := by
  intro F _ γ γ'
  refine ⟨pluck_one γ, ?_⟩
  intro a ha i j hi hj
  have ha0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨c, -, hc⟩ := pluck_one γ
    exact hc (by rw [ha, zero_mul])
  rw [Units.val_mul]
  set A : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ with hA
  set A' : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑γ' with hA'
  set B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F := ↑(γ'⁻¹) with hB
  have h1 : A' * B = 1 := Units.mul_inv γ'
  set r : Fin (2 + 2) := Fin.natAdd 2 (0 : Fin 2) with hr
  set s : Fin (2 + 2) := Fin.natAdd 2 (1 : Fin 2) with hs
  have key : ∀ p q, (A * B) r p * (A * B) s q - (A * B) r q * (A * B) s p =
      a * ((1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r p * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s q -
        (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) r q * (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) s p) := by
    intro p q
    rw [← h1, pluck_cb, pluck_cb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have := ha ![k, l]
    rw [pluck_det, pluck_det] at this
    rw [hr, hs, this, mul_assoc]
  have hrs : r ≠ s := by rw [hr, hs]; decide
  have hrv : (r : ℕ) = 2 := rfl
  have hsv : (s : ℕ) = 3 := rfl
  have hrj : r ≠ j := by intro h; rw [h] at hrv; omega
  have hsj : s ≠ j := by intro h; rw [h] at hsv; omega
  have k1 := key j r
  have k2 := key j s
  have k3 := key r s
  rw [Matrix.one_apply_ne hrj, Matrix.one_apply_ne hsj] at k1 k2
  rw [Matrix.one_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_ne hrs] at k3
  have hi' : i = r ∨ i = s := by
    have := i.isLt
    rcases (by omega : (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h | h
    · left; exact Fin.ext (by omega)
    · right; exact Fin.ext (by omega)
  apply mul_left_cancel₀ ha0
  rcases hi' with h | h
  · rw [h]
    linear_combination (-(A * B) r j) * k3 + (A * B) r r * k2 - (A * B) r s * k1
  · rw [h]
    linear_combination (-(A * B) s j) * k3 + (A * B) s r * k2 - (A * B) s s * k1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SubDet
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem row_two {K : Type} [Field K] {n : ℕ} {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i : Fin n) {a b : Fin n} (hab : a ≠ b) : ‖k i a‖ ^ 2 + ‖k i b‖ ^ 2 ≤ 1 := by
  classical
  have h := mem_archCompact.1 hk (Pi.single i 1)
  rw [Matrix.single_one_vecMul] at h
  have h1 : euclidNorm (Pi.single i (1 : w.Completion)) = 1 := by
    rw [euclidNorm, Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp only [Pi.single_eq_same, norm_one, one_pow, Real.sqrt_one]
  rw [h1, euclidNorm, Real.sqrt_eq_one] at h
  rw [← h, ← Finset.sum_pair (f := fun j => ‖k i j‖ ^ 2) hab]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.subDet :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) (k : AdelicGLn.AdelicGL K n), k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) → ∀ (r c : Fin 2 → Fin n), Function.Injective r → Function.Injective c →
      (∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1) ∧
      ∀ m : AdelicGLn.AdelicGL K 2, (m : Matrix (Fin 2) (Fin 2) 𝔸[K]) = (k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c → (detModule K 2 m).1 ≤ 1 := by
  intro K _ _ n k hk r c _ hc
  have hc01 : c 0 ≠ c 1 := fun h => absurd (hc h) (by decide)
  have H1 : ∀ w : InfinitePlace K, ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w‖ ≤ 1 := by
    intro w
    have h0 := row_two ((mem_maxCompact.1 hk).1 w) (r 0) hc01
    have h1 := row_two ((mem_maxCompact.1 hk).1 w) (r 1) hc01
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).1 w =
        infAt w k (r 0) (c 0) * infAt w k (r 1) (c 1) - infAt w k (r 0) (c 1) * infAt w k (r 1) (c 0) := by
      rw [← infEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [sq_nonneg (‖infAt w k (r 0) (c 0)‖ - ‖infAt w k (r 1) (c 1)‖),
      sq_nonneg (‖infAt w k (r 0) (c 1)‖ - ‖infAt w k (r 1) (c 0)‖)]
  have H2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ‖(((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v‖ ≤ 1 := by
    intro v
    have hv := (mem_maxCompact.1 hk).2 v
    rw [GLnLocal.mem_integralGL_iff] at hv
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hv
    have e : (((k : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det).2 v =
        finAt v k (r 0) (c 0) * finAt v k (r 1) (c 1) - finAt v k (r 0) (c 1) * finAt v k (r 1) (c 0) := by
      rw [← finEval_apply, Matrix.det_fin_two, map_sub, map_mul, map_mul]
      rfl
    rw [e]
    exact norm_le_one_of_mem v (sub_mem (mul_mem (hv.1 _ _) (hv.1 _ _)) (mul_mem (hv.1 _ _) (hv.1 _ _)))
  refine ⟨H1, H2, fun m hm => ?_⟩
  rw [← hm] at H1 H2
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 m) : ℝ) ≤ 1
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  refine mul_le_one₀ (Finset.prod_le_one₀ (fun _ _ => by positivity)
    fun w _ => pow_le_one₀ (norm_nonneg _) (H1 w)) (finprod_nonneg fun _ => norm_nonneg _) ?_
  exact finprod_induction (fun x : ℝ => 0 ≤ x ∧ x ≤ 1) ⟨zero_le_one, le_rfl⟩
    (fun x y hx hy => ⟨mul_nonneg hx.1 hy.1, mul_le_one₀ hx.2 hy.1 hy.2⟩)
    (fun v => ⟨norm_nonneg _, H2 v⟩) |>.2
end

