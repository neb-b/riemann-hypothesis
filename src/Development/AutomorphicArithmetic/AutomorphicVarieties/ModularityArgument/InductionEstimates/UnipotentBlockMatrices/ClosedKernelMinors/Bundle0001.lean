module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {a b : ℕ}

private theorem blk_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private theorem blk_inv_val (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y)⁻¹ = blk x⁻¹ y⁻¹ := Units.ext rfl

private theorem wGL_val :
    (wGL R).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) R) 1 0) := rfl

private theorem wGL_inv : (wGL R)⁻¹ = wGL R := Units.ext rfl

private theorem blk_mul' (x x' : GL (Fin a) R) (y y' : GL (Fin b) R) :
    blk x y * blk x' y' = blk (x * x') (y * y') := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem blk_one' : blk (1 : GL (Fin a) R) (1 : GL (Fin b) R) = 1 := by
  apply Units.ext
  simp only [blk_val, Units.val_one, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

private theorem w_blk (x y : GL (Fin 2) R) : wGL R * blk x y = blk y x * wGL R := by
  apply Units.ext
  simp only [Units.val_mul, blk_val, wGL_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem blk_det (x : GL (Fin a) R) (y : GL (Fin b) R) :
    Matrix.GeneralLinearGroup.det (blk x y) = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det y := by
  apply Units.ext
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, blk_val, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₂₁]

private theorem blk_map (f : R →+* S) (x : GL (Fin a) R) (y : GL (Fin b) R) :
    (blk x y).val.map f =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (x.val.map f) 0 0 (y.val.map f)) := by
  ext i j
  simp only [blk_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

private theorem w_map (f : R →+* S) : (wGL R).val.map f = (wGL S).val := by
  ext i j
  simp only [wGL_val, Matrix.reindex_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp [Matrix.one_apply, apply_ite f]

private theorem blk_cont [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun p : GL (Fin a) R × GL (Fin b) R => blk p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem blk_ent (O : Subring S) (x : GL (Fin a) S) (y : GL (Fin b) S) (hx : ∀ i j, x i j ∈ O)
    (hy : ∀ i j, y i j ∈ O) (i j : Fin (a + b)) : blk x y i j ∈ O := by
  change (blk x y).val i j ∈ O
  simp only [blk_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [hx, hy]

private theorem w_ent (O : Subring S) (i j : Fin (2 + 2)) : wGL S i j ∈ O := by
  change (wGL S).val i j ∈ O
  simp only [wGL_val, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, O.zero_mem] <;>
    split_ifs <;> simp

private theorem vec_l (M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) S) (y : Fin (a + b) → S) (j : Fin a ⊕ Fin b) :
    Matrix.vecMul y (Matrix.reindex finSumFinEquiv finSumFinEquiv M) (finSumFinEquiv j) =
      ∑ i : Fin a, y (finSumFinEquiv (Sum.inl i)) * M (Sum.inl i) j +
        ∑ i : Fin b, y (finSumFinEquiv (Sum.inr i)) * M (Sum.inr i) j := by
  simp only [Matrix.vecMul, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply]

end SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
private theorem blk_arch {a b : ℕ} (w : InfinitePlace K) {x : GL (Fin a) w.Completion} {y : GL (Fin b) w.Completion}
    (hx : x ∈ archCompact w) (hy : y ∈ archCompact w) : blk x y ∈ archCompact (n := a + b) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  have h1 := congrArg (· ^ 2) (hx fun i => z (finSumFinEquiv (Sum.inl i)))
  have h2 := congrArg (· ^ 2) (hy fun i => z (finSumFinEquiv (Sum.inr i)))
  simp only [euclidNorm_sq, Matrix.vecMul, dotProduct] at h1 h2
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, ← h1, ← h2]
  simp only [blk_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add]

omit [NumberField K] in
private theorem w_arch (w : InfinitePlace K) : wGL w.Completion ∈ archCompact (n := 2 + 2) w := by
  intro z
  refine (sq_eq_sq₀ (euclidNorm_nonneg _) (euclidNorm_nonneg _)).1 ?_
  rw [euclidNorm_sq, euclidNorm_sq, ← finSumFinEquiv.sum_comp, ← finSumFinEquiv.sum_comp (fun i => ‖z i‖ ^ 2),
    Fintype.sum_sum_type, Fintype.sum_sum_type, add_comm]
  simp only [wGL_val, vec_l, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add,
      Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem blk_max {a b : ℕ} {x : AdelicGLn.AdelicGL K a} {y : AdelicGLn.AdelicGL K b}
    (hx : x ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K a)))
    (hy : y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K b))) :
    blk x y ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (a + b))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (blk x y) = blk (infAt w x) (infAt w y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (infEval w) x y))
    rw [this]
    exact blk_arch w (hx.1 w) (hy.1 w)
  · have : finAt v (blk x y) = blk (finAt v x) (finAt v y) :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (blk_map (finEval v) x y))
    rw [this, GLnLocal.mem_integralGL_iff, blk_inv_val]
    have h1 := (GLnLocal.mem_integralGL_iff _ _).1 (hx.2 v)
    have h2 := (GLnLocal.mem_integralGL_iff _ _).1 (hy.2 v)
    exact ⟨blk_ent _ _ _ h1.1 h2.1, blk_ent _ _ _ h1.2 h2.2⟩

private theorem w_max : wGL 𝔸[K] ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := by
  refine ⟨fun w => ?_, fun v => ?_⟩
  · have : infAt w (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (infEval w)))
    rw [this]
    exact w_arch w
  · have : finAt v (wGL 𝔸[K]) = wGL _ :=
      Units.ext (Matrix.ext fun i j => congrArg (fun N => N i j) (w_map (finEval v)))
    rw [this, GLnLocal.mem_integralGL_iff, wGL_inv]
    exact ⟨w_ent _, w_ent _⟩

private theorem det_blk (a b : AdelicGLn.AdelicGL K 2) :
    detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b := by
  simp only [detModule, MonoidHom.comp_apply, AdelicGLn.det, blk_det, map_mul]

private theorem coe_ret {n : ℕ} {g : AdelicGLn.AdelicGL K n} (h : g ∈ normOneGL (K := K) (n := n)) :
    (retractOne g : AdelicGLn.AdelicGL K n) = g :=
  congrArg Subtype.val (retractOne_coe (⟨g, h⟩ : normOneGL (K := K) (n := n)))

private theorem zt_add (s t : ℝ) : zt K (s + t) = zt K s * zt K t := by
  rw [zt, zt, zt, ← map_mul]
  exact congrArg _ (Subtype.ext (Real.exp_add s t))

private theorem zt_zero : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem lv_coe (m₁ m₂ : G1 K 2) (t : ℝ) :
    ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t)) := by
  refine coe_ret (mem_normOneGL_iff_detModule.2 ?_)
  rw [det_blk, map_mul, map_mul, mem_normOneGL_iff_detModule.1 m₁.2, mem_normOneGL_iff_detModule.1 m₂.2,
    one_mul, one_mul, ← map_mul, ← zt_add, add_neg_cancel, zt_zero, map_one]

private theorem mul_zt (m m' : AdelicGLn.AdelicGL K 2) (s t : ℝ) :
    m * zt K s * (m' * zt K t) = m * m' * zt K (s + t) := by
  rw [zt_add, mul_assoc, ← mul_assoc (zt K s), show zt K s * m' = m' * zt K s from centralSection_mul_comm _ _]
  simp only [mul_assoc]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.blkLaws :
    ∀ {K : Type} [Field K] [NumberField K], (∀ (m₁ m₂ : G1 K 2) (t : ℝ), ((lv m₁ m₂ t : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))) ∧
      (∀ (m₁ m₂ m₁' m₂' : G1 K 2) (t t' : ℝ), lv m₁ m₂ t * lv m₁' m₂' t' = lv (m₁ * m₁') (m₂ * m₂') (t + t')) ∧ lv (1 : G1 K 2) 1 0 = 1 ∧
      Continuous (fun p : G1 K 2 × G1 K 2 × ℝ => lv p.1 p.2.1 p.2.2) ∧
      (∀ a b : AdelicGLn.AdelicGL K 2, detModule K (2 + 2) (blk a b) = detModule K 2 a * detModule K 2 b) ∧
      (∀ a b a' b' : AdelicGLn.AdelicGL K 2, blk a b * blk a' b' = blk (a * a') (b * b')) ∧
      ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] ∧ w0 K ∈ Gam K (2 + 2) ∧ w0 K ∈ KG K (2 + 2) ∧
      (∀ (m₁ m₂ : G1 K 2) (t : ℝ), w0 K * lv m₁ m₂ t = lv m₂ m₁ (-t) * w0 K) ∧
      (∀ u₁ ∈ KG K 2, ∀ u₂ ∈ KG K 2, lv u₁ u₂ 0 ∈ KG K (2 + 2)) ∧ ∀ n, IsCompact (KG K n : Set (G1 K n)) ∧
        ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), k ∈ normOneGL (K := K) (n := n) := by
  intro K _ _
  have hw : ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = wGL 𝔸[K] :=
    coe_ret (maxCompact_le_normOneGL w_max)
  have hz : Continuous (zt K) := continuous_centralSection.comp (Real.continuous_exp.subtype_mk _)
  refine ⟨lv_coe, ?_, ?_, ?_, det_blk, fun a b a' b' => blk_mul' a a' b b', hw, ?_, ?_, ?_, ?_, fun n => ⟨?_, ?_⟩⟩
  · intro m₁ m₂ m₁' m₂' t t'
    apply Subtype.ext
    rw [Subgroup.coe_mul, lv_coe, lv_coe, lv_coe, blk_mul', mul_zt, mul_zt, neg_add, Subgroup.coe_mul, Subgroup.coe_mul]
  · apply Subtype.ext
    rw [lv_coe, neg_zero, zt_zero, Subgroup.coe_one, Subgroup.coe_one, mul_one, blk_one']
  · exact continuous_retractOne.comp (blk_cont.comp
      (((continuous_subtype_val.comp continuous_fst).mul (hz.comp continuous_snd.snd)).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).mul (hz.comp continuous_snd.snd.neg))))
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ AdelicGLn.rationalGL K (2 + 2)
    rw [hw]
    exact ⟨wGL K, Units.ext (w_map (algebraMap K 𝔸[K]))⟩
  · change ((w0 K : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [hw]
    exact w_max
  · intro m₁ m₂ t
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, lv_coe, lv_coe, hw, neg_neg, w_blk]
  · intro u₁ h₁ u₂ h₂
    change ((lv u₁ u₂ 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ Reduction.maxCompact
    rw [lv_coe, neg_zero, zt_zero, mul_one, mul_one]
    exact blk_max h₁ h₂
  · refine Topology.IsInducing.subtypeVal.isCompact_preimage' isCompact_maxCompact ?_
    intro k hk
    exact ⟨⟨k, maxCompact_le_normOneGL hk⟩, rfl⟩
  · exact fun k hk => maxCompact_le_normOneGL hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BumpEx
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_cont (ν : Measure H) [ν.IsHaarMeasure] {ρ : H → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) {Φ : G → H → ℝ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun x => ∫ p, ρ p * Φ x p ∂ν := by
  have e : (fun x => ∫ p, ρ p * Φ x p ∂ν) = fun x => ∫ p in tsupport ρ, ρ p * Φ x p ∂ν := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
  rw [e]
  exact continuous_parametric_integral_of_continuous ((hρ.comp continuous_snd).mul hΦ) hρc

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_split {O : Set G} (hO : O ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, a * b * c⁻¹ ∈ O := by
  obtain ⟨V₁, h₁, e₁⟩ := exists_nhds_split_inv hO
  obtain ⟨V₂, h₂, e₂⟩ := exists_nhds_one_split h₁
  refine ⟨V₁ ∩ V₂, inter_mem h₁ h₂, fun a ha b hb c hc => ?_⟩
  rw [← div_eq_mul_inv]
  exact e₁ _ (e₂ a ha.2 b hb.2) c hc.1

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_step (ν : Measure H) [ν.IsHaarMeasure] (π : H →* G) (hπ : Continuous π)
    {ρ : H → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ p, 0 ≤ ρ p) {p₀ : H} (hρ1 : ρ p₀ ≠ 0)
    {h : G → ℝ} (hh : Continuous h) (hh0 : ∀ x, 0 ≤ h x) (hh1 : h 1 ≠ 0) (hs : ∀ x, h x⁻¹ = h x)
    {O : Set G} (hO : ∀ p q y, ρ p ≠ 0 → ρ q ≠ 0 → h y ≠ 0 → π p * y * (π q)⁻¹ ∈ O) :
    ∃ F a : G → ℝ, Continuous F ∧ (∀ x, a x = ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν) ∧
      (∀ u, (∀ x, h (u * x) = h x) → ∀ x, F (u * x) = F x) ∧
      Continuous a ∧ (∀ x, 0 ≤ a x) ∧ a 1 ≠ 0 ∧ (∀ x, a x⁻¹ = a x) ∧ ∀ x, a x ≠ 0 → x ∈ O := by
  set F : G → ℝ := fun y => ∫ q, ρ q * h (y * π q) ∂ν with hF
  have hFc : Continuous F := bump_cont ν hρ hρc (Φ := fun y q => h (y * π q))
    (hh.comp (continuous_fst.mul (hπ.comp continuous_snd)))
  have hF0 : ∀ y, 0 ≤ F y := fun y => integral_nonneg fun q => mul_nonneg (hρ0 q) (hh0 _)
  have hF1 : 0 < F (π p₀)⁻¹ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hh.comp (continuous_const.mul hπ))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hh0 _)) ?_
    simpa using ⟨hρ1, hh1⟩
  have ha : ∀ x, ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν = ∫ p, ∫ q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) ∂ν ∂ν := by
    intro x
    simp only [hF, integral_const_mul]
  refine ⟨F, fun x => ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν, hFc, fun _ => rfl, fun u hu x => ?_, ?_,
    fun x => integral_nonneg fun q => mul_nonneg (hρ0 q) (hF0 _), ne_of_gt ?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [hF, mul_assoc, hu]
  · exact bump_cont ν hρ hρc (Φ := fun x p => F ((π p)⁻¹ * x))
      (hFc.comp ((hπ.comp continuous_snd).inv.mul continuous_fst))
  · refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hFc.comp (hπ.inv.mul continuous_const))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hF0 _)) ?_
    simpa using ⟨hρ1, hF1.ne'⟩
  · beta_reduce
    rw [ha, ha, integral_integral_swap_of_hasCompactSupport]
    · refine integral_congr_ae (Eventually.of_forall fun p => integral_congr_ae (Eventually.of_forall fun q => ?_))
      beta_reduce
      rw [← hs ((π p)⁻¹ * x * π q)]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
      ring
    · exact (hρ.comp continuous_fst).mul ((hρ.comp continuous_snd).mul (hh.comp
        (((hπ.comp continuous_fst).inv.mul continuous_const).mul (hπ.comp continuous_snd))))
    · refine HasCompactSupport.intro (hρc.isCompact.prod hρc.isCompact) fun z hz => ?_
      rw [mem_prod, not_and_or] at hz
      rcases hz with hz | hz <;> simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  · by_contra hxO
    refine hx ?_
    beta_reduce
    rw [ha]
    have : ∀ p q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) = 0 := by
      intro p q
      by_contra h0
      refine hxO ?_
      have := hO p q _ (left_ne_zero_of_mul h0) (left_ne_zero_of_mul (right_ne_zero_of_mul h0))
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
      simpa [mul_assoc] using this
    simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bumpEx :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (O : Set (G1 K n)), O ∈ 𝓝 (1 : G1 K n) →
      ∃ a : CC K n, tsupport a ⊆ O ∧ (∀ g, 0 ≤ (a g).re ∧ (a g).im = 0) ∧ ∫ g, a g ∂μ = 1 ∧ CuspidalProjection.ccStar a = a ∧ UpperTheory.ConvolutionTheory.C.IsLeftSmooth a := by
  intro K _ _ n μ _ O hO
  letI : FirstCountableTopology (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  letI : RegularSpace (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  letI : R1Space (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  obtain ⟨O', hO', hO'O, hO'c⟩ := local_compact_nhds hO
  obtain ⟨V₂, hV₂, e₂⟩ := bump_split hO'
  obtain ⟨V₁, hV₁, e₁⟩ := bump_split hV₂

  obtain ⟨f, hf1, hf0, -, hf⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G1 K n)))
    (isOpen_interior (s := V₁)).isClosed_compl
    (disjoint_singleton_left.2 fun h => h (mem_interior_iff_mem_nhds.2 hV₁))
  have hf1' : f 1 = 1 := hf1 rfl
  have hfV : ∀ y, f y ≠ 0 → y ∈ V₁ := fun y hy => by
    by_contra hn
    exact hy (hf0 fun h => hn (interior_subset h))

  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((isOpen_interior (s := V₁)).preimage (continuous_finOne (K := K) (n := n)))
    (by rw [mem_preimage, map_one]; exact mem_interior_iff_mem_nhds.2 hV₁)
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) := N.toOpenSubgroup.toSubgroup
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := N.toOpenSubgroup.isOpen
  have hUV : ∀ u : U, finOne K n u ∈ V₁ := fun u => interior_subset (hN u.2)
  have := compactSpace_of_isOpen U hU
  set_option synthInstance.maxHeartbeats 200000 in
   obtain ⟨F₁, h, -, hF₁, -, hc, h0, h1, hs, hV⟩ := bump_step (haarProb U) ((finOne K n).comp U.subtype)
    (continuous_finOne.comp continuous_subtype_val) (ρ := fun _ => 1) continuous_const
    (HasCompactSupport.of_compactSpace _) (fun _ => zero_le_one) (p₀ := 1) one_ne_zero (h := fun x => f x * f x⁻¹)
    (f.continuous.mul (f.continuous.comp continuous_inv)) (fun x => mul_nonneg (hf _).1 (hf _).1)
    (by simp [hf1']) (fun x => by simp [mul_comm]) (O := V₂)
    (fun p q y _ _ hy => e₁ _ (hUV p) _ (hfV _ (left_ne_zero_of_mul hy)) _ (hUV q))
  have hinv : ∀ u ∈ U, ∀ x, h (finOne K n u * x) = h x := by
    intro u hu x
    rw [hF₁, hF₁, ← integral_mul_left_eq_self _ (⟨u, hu⟩ : U)]
    simp [mul_assoc]

  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν (N := archP K n ⁻¹' V₂)
    (continuous_archP.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  have hρc : Continuous ρ := Complex.continuous_re.comp (hρt.continuous _)
  have hρs : HasCompactSupport ρ := hρt.2.comp_left (g := Complex.re) rfl
  obtain ⟨p₀, hp₀⟩ : ∃ p, ρ p ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hρ1
  obtain ⟨F, a, hFc, hF, hFi, ac, a0, a1, as, aO⟩ := bump_step ν (archP K n) continuous_archP hρc hρs hρ0 hp₀ hc h0 h1 hs
    (O := O') (fun p q y hp hq hy => e₂ _ (hρN p hp) _ (hV y hy) _ (hρN q hq))
  have acs : HasCompactSupport a := HasCompactSupport.intro hO'c fun x hx => by
    by_contra hn
    exact hx (aO x hn)
  have hI : 0 < ∫ x, a x ∂μ := ac.integral_pos_of_hasCompactSupport_nonneg_nonzero acs a0 a1
  set I := ∫ x, a x ∂μ with hIdef
  refine ⟨⟨⟨fun x => ((a x * I⁻¹ : ℝ) : ℂ), Complex.continuous_ofReal.comp (ac.mul continuous_const)⟩,
    HasCompactSupport.comp_left (g := Complex.ofReal) (f := fun x => a x * I⁻¹) acs.mul_right Complex.ofReal_zero⟩,
    ?_, fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, ?_, fun x => ?_, U, hU, fun u hu x => ?_⟩
  · refine Subset.trans (closure_minimal (fun x hx => aO x fun h0 => ?_) hO'c.isClosed) hO'O
    have hx' : ((a x * I⁻¹ : ℝ) : ℂ) ≠ 0 := hx
    simp [h0] at hx'
  · exact mul_nonneg (a0 g) (inv_nonneg.2 hI.le)
  · change ∫ x, ((a x * I⁻¹ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_mul_const, mul_inv_cancel₀ hI.ne', Complex.ofReal_one]
  · ext g
    change conj ((a g⁻¹ * I⁻¹ : ℝ) : ℂ) = ((a g * I⁻¹ : ℝ) : ℂ)
    rw [Complex.conj_ofReal, as]
  · change (isExpLieAlgebra K n).IsSmoothFun fun A => ((a (archP K n A * x) * I⁻¹ : ℝ) : ℂ)
    have hΨ : Continuous fun y : archGroup K n => ((F ((archP K n y)⁻¹ * x) * I⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((hFc.comp (continuous_archP.inv.mul continuous_const)).mul continuous_const)
    have hsm := IsExpLieAlgebra.isSmoothFun_comp_inv ((isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hρt)
    convert hsm using 2 with A
    rw [hF, ← integral_mul_const, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
    push_cast
    ring
  · change ((a (finOne K n u * x) * I⁻¹ : ℝ) : ℂ) = ((a x * I⁻¹ : ℝ) : ℂ)
    rw [hF, hF]
    simp only [archimedeanProjection_apply, ← mul_assoc, archProj_inv_mul_finOne]
    simp only [mul_assoc, hFi _ (hinv u hu)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtClosed
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private def ctKer {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ) :
    Submodule ℂ (L2 μ) where
  carrier := {w | constantTermL2 μ r w =ᵐ[μ] 0}
  zero_mem' := by
    change constantTermL2 μ r 0 =ᵐ[μ] 0
    filter_upwards [ae_constantTermL2_sub μ r 0 0] with y hy
    rw [sub_self, sub_self] at hy
    exact hy
  add_mem' := fun {φ ψ} hφ hψ => by
    change constantTermL2 μ r (φ + ψ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    have h2 : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    filter_upwards [ae_constantTermL2_add μ r φ ψ, h1, h2] with y e1 e2 e3
    rw [e1, e2, e3]
    simp
  smul_mem' := fun c φ hφ => by
    change constantTermL2 μ r (c • φ) =ᵐ[μ] 0
    have h1 : constantTermL2 μ r φ =ᵐ[μ] 0 := hφ
    filter_upwards [ae_constantTermL2_smul μ r c φ, h1] with y e1 e2
    rw [e1, e2]
    simp

private theorem ctKer_closed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (r : ℕ) : IsClosed (ctKer μ r : Set (L2 μ)) := by
  refine isClosed_of_closure_subset fun φ hφ => ?_
  change constantTermL2 μ r φ =ᵐ[μ] 0
  refine ae_of_forall_isCompact μ fun S hS => ?_
  obtain ⟨C, hC, hCφ⟩ := exists_lintegral_constantTermL2_sq_le μ r hS
  set I := ∫⁻ y in S, ‖constantTermL2 μ r φ y‖ₑ ∂μ
  have hle : ∀ ε : ℝ, 0 < ε → I ^ 2 ≤ C * ENNReal.ofReal ε ^ 2 := by
    intro ε hε
    obtain ⟨ψ, hψ, hdist⟩ := Metric.mem_closure_iff.1 hφ ε hε
    have hψ' : constantTermL2 μ r ψ =ᵐ[μ] 0 := hψ
    have hI : I = ∫⁻ y in S, ‖constantTermL2 μ r (φ - ψ) y‖ₑ ∂μ := by
      refine lintegral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [ae_constantTermL2_sub μ r φ ψ, hψ'] with y h1 h2
      rw [h1, h2, Pi.zero_apply, sub_zero]
    rw [hI]
    refine (hCφ (φ - ψ)).trans ?_
    gcongr
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hdist.le
  have hI0 : I ^ 2 = 0 := by
    refine le_antisymm ?_ zero_le
    have ht : Tendsto (fun ε : ℝ => C * ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun ε : ℝ => ENNReal.ofReal ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have := (((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal).tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
        simpa [Function.comp_def] using this
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hC)
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hle ε hε)
  have hI' : I = 0 := pow_eq_zero_iff two_ne_zero |>.1 hI0
  have hm : AEMeasurable (fun y => ‖constantTermL2 μ r φ y‖ₑ) (μ.restrict S) :=
    (stronglyMeasurable_ctFun r (Lp.stronglyMeasurable φ)).measurable.eNorm.aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hm).1 hI'] with y hy
  simpa using hy

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.ctClosed :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (r : ℕ), ∃ S : Submodule ℂ (L2 μ), IsClosed (S : Set (L2 μ)) ∧
      ∀ w, w ∈ S ↔ constantTermL2 μ r w =ᵐ[μ] 0 := by
  intro K _ _ n μ _ r
  exact ⟨ctKer μ r, ctKer_closed μ r, fun _ => Iff.rfl⟩
end

