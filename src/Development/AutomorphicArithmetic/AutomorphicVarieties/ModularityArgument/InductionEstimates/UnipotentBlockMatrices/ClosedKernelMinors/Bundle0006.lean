module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ConjMat
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem vL (i : Fin 2) : ((finSumFinEquiv (Sum.inl i : Fin 2 ⊕ Fin 2) : Fin (2 + 2)) : ℕ) = i := rfl

private theorem vR (i : Fin 2) : ((finSumFinEquiv (Sum.inr i : Fin 2 ⊕ Fin 2) : Fin (2 + 2)) : ℕ) = 2 + i := rfl

private theorem exBlock {R : Type} [CommRing R] (C : Matrix (Fin 2) (Fin 2) R) :
    ∃ Z : UPos (2 + 2) 2 → R,
      unipMatrix Z = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 C 0 1) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 C 0 (1 : Matrix (Fin 2) (Fin 2) R)) p.1.1 p.1.2, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Fin.ext_iff, vL, vR]

private theorem triang {R : Type} [CommRing R] (a d : GL (Fin 2) R) (C : Matrix (Fin 2) (Fin 2) R) :
    ∃ Z : UPos (2 + 2) 2 → R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val C 0 d.val) = (unipGL Z * blk a d).val := by
  obtain ⟨Z, hZ⟩ := exBlock (C * (d⁻¹).val)
  refine ⟨Z, ?_⟩
  rw [Units.val_mul, coe_unipGL, hZ]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_assoc, Units.inv_mul]

private theorem bigCell {F : Type} [Field F] (g : GL (Fin (2 + 2)) F)
    (h : ((g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det ≠ 0) :
    ∃ ξ : UPos (2 + 2) 2 → F, ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
      (g * (unipGL ξ)⁻¹ * (wGL F)⁻¹).val i j = 0 := by
  obtain ⟨M, hM⟩ := (Matrix.reindex (finSumFinEquiv (m := 2) (n := 2)) (finSumFinEquiv (m := 2) (n := 2))).surjective g.val
  rw [← Matrix.fromBlocks_toBlocks M] at hM
  have hC : (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2) = M.toBlocks₂₁ := by
    rw [← hM]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁]
  rw [hC] at h
  obtain ⟨Z, hZ⟩ := exBlock (-(M.toBlocks₂₁⁻¹ * M.toBlocks₂₂))
  refine ⟨-Z, fun i j hi hj => ?_⟩
  have hw : ((wGL F)⁻¹).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) F) 1 0) := rfl
  rw [Units.val_mul, Units.val_mul, coe_unipGL_inv, neg_neg, hZ, hw, ← hM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h), Matrix.one_mul, neg_add_cancel]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [vL] at hi; omega
  · rw [vL] at hi; omega
  · simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [vR] at hj; omega

private theorem oneInt {K : Type} [Field K] [NumberField K] (f : (UPos 2 1 → 𝔸[K]) → ℂ) :
    ∫ y in GroundTheory.Global.fundamentalSet K, f (fun _ => y) ∂GroundTheory.Global.adeleMeasure K =
      ∫ Y in unipFundamentalDomain K 2 1, f Y ∂unipMeasure K 2 1 := by
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[K]) (unipMeasure K 2 1) (GroundTheory.Global.adeleMeasure K) := by
    convert measurePreserving_funUnique (GroundTheory.Global.adeleMeasure K) (UPos 2 1)
  rw [← hm.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  · congr 1
    ext Y
    simp [unipFundamentalDomain, Unique.forall_iff]
  · funext Y
    congr 1
    funext p
    simp [Subsingleton.elim p default]

private theorem ratOne {K : Type} [Field K] [NumberField K] {n : ℕ} (g : GL (Fin n) K) :
    ∃ γ : Gam K n, ((γ : G1 K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n g :=
  ⟨⟨⟨_, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, ⟨g, rfl⟩⟩, rfl⟩

private theorem coeLv {K : Type} [Field K] [NumberField K] (a d : G1 K 2) :
    ((lv a d 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = blk (a : AdelicGLn.AdelicGL K 2) (d : AdelicGLn.AdelicGL K 2) := by
  have hz : zt K 0 = 1 := by
    have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
    rw [zt, this, map_one]
  rw [blkLaws.1, neg_zero, hz, mul_one, mul_one]

private theorem uMat {R : Type} [CommRing R] (y : R) :
    unipMatrix (fun _ : UPos 2 1 => y) = 1 + y • Matrix.single 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply]

private theorem conjMat {K : Type} [Field K] [NumberField K] {r : ℕ} (g : GL (Fin (2 + 2)) K) (X₀ : UPos (2 + 2) r → K)
    (A C D : Matrix (Fin 2) (Fin 2) K)
    (h : g.val * blockEntry X₀ * (g⁻¹).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 D)) (y : 𝔸[K]) :
    (AdelicGLn.diagonal K _ g * unipGL (fun p => y * algebraMap K 𝔸[K] (X₀ p)) * (AdelicGLn.diagonal K _ g)⁻¹).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (1 + y • (algebraMap K 𝔸[K]).mapMatrix A)
        (y • C.map (algebraMap K 𝔸[K])) 0 (1 + y • (algebraMap K 𝔸[K]).mapMatrix D)) := by
  have hb : blockEntry (fun p => y * algebraMap K 𝔸[K] (X₀ p)) = y • (algebraMap K 𝔸[K]).mapMatrix (blockEntry X₀) := by
    ext i j
    simp only [blockEntry_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  have hd : ∀ u : GL (Fin (2 + 2)) K, (AdelicGLn.diagonal K _ u).val = (algebraMap K 𝔸[K]).mapMatrix u.val := fun _ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_unipGL, unipMatrix, hb, hd, hd, mul_add, add_mul, mul_one, ← map_mul,
    Units.mul_inv, map_one, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, h]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

private theorem conjU {K : Type} [Field K] [NumberField K] (m : GL (Fin 2) K) (μ : G1 K 2)
    (hμ : (μ : AdelicGLn.AdelicGL K 2) = AdelicGLn.diagonal K 2 m) (y : 𝔸[K]) :
    ((μ⁻¹ * unipOne (K := _) (n := _) 1 (fun _ => y) * μ : G1 K 2) : AdelicGLn.AdelicGL K 2).val =
      1 + y • (algebraMap K 𝔸[K]).mapMatrix ((m⁻¹).val * Matrix.single 0 1 1 * m.val) := by
  have hd : ∀ u : GL (Fin 2) K, (AdelicGLn.diagonal K _ u).val = (algebraMap K 𝔸[K]).mapMatrix u.val := fun _ => rfl
  have hs : (algebraMap K 𝔸[K]).mapMatrix (Matrix.single (0 : Fin 2) 1 1) = Matrix.single 0 1 1 := by
    simp [Matrix.map_single]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hμ, ← map_inv, coe_unipOne, Units.val_mul, Units.val_mul, coe_unipGL,
    uMat, hd, hd, mul_add, add_mul, mul_one, ← map_mul, Units.inv_mul, map_one, Matrix.mul_smul, Matrix.smul_mul,
    map_mul, map_mul, hs]

private theorem fromMat {K : Type} [Field K] [NumberField K] (γ u : G1 K (2 + 2)) (a d : G1 K 2) (C : Matrix (Fin 2) (Fin 2) 𝔸[K])
    (h : ((γ : AdelicGLn.AdelicGL K (2 + 2)) * (u : AdelicGLn.AdelicGL K (2 + 2)) * (γ : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (a : AdelicGLn.AdelicGL K 2).val C 0 (d : AdelicGLn.AdelicGL K 2).val)) :
    ∃ Z, γ * u = nn Z * (lv a d 0 * γ) := by
  obtain ⟨Z, hZ⟩ := triang (a : AdelicGLn.AdelicGL K 2) (d : AdelicGLn.AdelicGL K 2) C
  refine ⟨Z, ?_⟩
  rw [← mul_assoc, ← mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, hZ, Subgroup.coe_mul, coeLv, coe_unipOne]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.dies :
    ∀ {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ), PFun F → ∀ (γ : Gam K (2 + 2)) (r : ℕ), (r = 1 ∨ r = 3 ∨ (r = 2 ∧ γ ∉ ParΓ K 2 2 ∧
        ¬ ∃ δ ∈ PK K, ∃ ξ : unipLattice K (2 + 2) 2, (γ : G1 K (2 + 2)) = δ * w0 K * nn ξ.1)) → ∃ X₀, Dies F r γ X₀ := by
  intro K _ _ F hF γ r hr
  obtain ⟨g, hg⟩ : ∃ g, AdelicGLn.diagonal K (2 + 2) g = ((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := γ.2
  have hmul := (blkLaws (K := K)).2.1
  have hP : ∀ a d : Gam K 2, lv (a : G1 K 2) (d : G1 K 2) 0 ∈ PK K := fun a d =>
    ((pkLaws (K := K)).2.1 _).2 ⟨0, a, d, by
      simp only [AddSubgroup.coe_zero, unipOne_zero, one_mul]⟩
  obtain ⟨X₀, m, C, hC⟩ := linAlg g r (by
    rcases hr with h | h | ⟨h, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨h, fun h0 => h1 ?_, by_contra fun h0 => h2 ?_⟩)
    · refine Subgroup.subset_closure fun i j hi hj => ?_
      rw [← hg, AdelicGLn.diagonal_apply]
      have := congrFun (congrFun h0 ⟨i - 2, by omega⟩) ⟨j, hj⟩
      rw [Matrix.submatrix_apply, show Fin.natAdd 2 (⟨i - 2, by omega⟩ : Fin 2) = i from Fin.ext (by simp; omega),
        show Fin.castAdd 2 (⟨j, hj⟩ : Fin 2) = j from Fin.ext rfl] at this
      rw [this, Matrix.zero_apply, map_zero]
    · obtain ⟨ξ, hξ⟩ := bigCell g h0
      obtain ⟨δ, hδ⟩ := ratOne (g * (unipGL ξ)⁻¹ * (wGL K)⁻¹)
      have hw : AdelicGLn.diagonal K (2 + 2) (wGL K) = wGL 𝔸[K] := by
        ext i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        rw [AdelicGLn.diagonal_apply]
        rcases i with i | i <;> rcases j with j | j <;> simp [wGL, Matrix.one_apply]
      refine ⟨δ, ⟨δ, Subgroup.subset_closure fun i j hi hj => ?_, rfl⟩,
        ⟨fun p => algebraMap K 𝔸[K] (ξ p), ξ, rfl⟩, Subtype.ext ?_⟩
      · rw [hδ, AdelicGLn.diagonal_apply, hξ i j hi hj, map_zero]
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, hδ, (blkLaws (K := K)).2.2.2.2.2.2.1, coe_unipOne, ← hw, ← diagonal_unipGL,
          ← map_mul, ← map_mul, ← hg, inv_mul_cancel_right, inv_mul_cancel_right])
  obtain ⟨μ, hμ⟩ := ratOne m
  refine ⟨X₀, fun x => ?_⟩
  rcases hC with hC | hC
  · rw [← hF.cusp₂ (lv 1 (μ : G1 K 2) 0 * (γ : G1 K (2 + 2)) * x), ← oneInt]
    congr 1
    funext y
    obtain ⟨Z, hZ⟩ := fromMat γ (unipOne (K := _) (n := _) r fun p => y * algebraMap K 𝔸[K] (X₀ p)) 1
      ((μ : G1 K 2)⁻¹ * unipOne (K := _) (n := _) 1 (fun _ => y) * (μ : G1 K 2)) (y • C.map (algebraMap K 𝔸[K])) (by
        rw [← hg, coe_unipOne, conjMat g X₀ _ _ _ hC]
        rw [conjU m μ hμ]
        simp)
    rw [hZ, mul_assoc, hF.unip, ← hF.rat _ (hP 1 μ)]
    simp only [← mul_assoc, hmul, OneMemClass.coe_one, mul_inv_cancel, one_mul, add_zero]
  · rw [← hF.cusp₁ (lv (μ : G1 K 2) 1 0 * (γ : G1 K (2 + 2)) * x), ← oneInt]
    congr 1
    funext y
    obtain ⟨Z, hZ⟩ := fromMat γ (unipOne (K := _) (n := _) r fun p => y * algebraMap K 𝔸[K] (X₀ p))
      ((μ : G1 K 2)⁻¹ * unipOne (K := _) (n := _) 1 (fun _ => y) * (μ : G1 K 2)) 1 (y • C.map (algebraMap K 𝔸[K])) (by
        rw [← hg, coe_unipOne, conjMat g X₀ _ _ _ hC]
        rw [conjU m μ hμ]
        simp)
    rw [hZ, mul_assoc, hF.unip, ← hF.rat _ (hP μ 1)]
    simp only [← mul_assoc, hmul, OneMemClass.coe_one, mul_inv_cancel, one_mul, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CoordUnf
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem iter3 {B C : Type} [MeasurableSpace B] [MeasurableSpace C] (κ : Measure B) (l : Measure C)
    [SFinite κ] [SFinite l] (f : ℝ × B × C → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod (κ.prod l) =
      ∫⁻ t : ℝ, (∫⁻ k, ∫⁻ X, f (t, k, X) ∂l ∂κ) * ENNReal.ofReal (Real.exp (-4 * t)) := by
  rw [lintegral_prod _ hf.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf.lintegral_prod_right']
  refine lintegral_congr fun t => ?_
  rw [Pi.mul_apply, mul_comm, lintegral_prod (fun y => f (t, y)) (hf.comp measurable_prodMk_left).aemeasurable]

private theorem oms5 (A B C : Type) [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [OpensMeasurableSpace A] [OpensMeasurableSpace B] [OpensMeasurableSpace C]
    [SecondCountableTopology A] [SecondCountableTopology C] : OpensMeasurableSpace (A × A × ℝ × B × C) := inferInstance

variable {K : Type} [Field K] [NumberField K]

private theorem nn_add (X Y : UPos (2 + 2) 2 → 𝔸[K]) : nn (X + Y) = nn X * nn Y :=
  Subtype.ext (unipGL_add X Y)

private theorem nn_zero : nn (0 : UPos (2 + 2) 2 → 𝔸[K]) = 1 :=
  Subtype.ext unipGL_zero

private theorem nn_cont : Continuous (nn : (UPos (2 + 2) 2 → 𝔸[K]) → G1 K (2 + 2)) :=
  continuous_unipGL.subtype_mk _

private theorem pt_cont : Continuous (pt : Par K → G1 K (2 + 2)) := by
  have h := (blkLaws (K := K)).2.2.2.1
  unfold pt
  refine Continuous.mul (Continuous.mul (nn_cont.comp (by fun_prop)) ?_) (by fun_prop)
  exact h.comp (f := fun p : Par K => (p.1, p.2.1, p.2.2.1)) (by fun_prop)

private theorem pt_meas : Measurable (pt : Par K → G1 K (2 + 2)) := by
  haveI i1 : OpensMeasurableSpace (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance
  haveI i2 : OpensMeasurableSpace (G1 K 2) := inferInstance
  haveI i3 : OpensMeasurableSpace (KG K (2 + 2)) := inferInstance
  haveI i4 : SecondCountableTopology (G1 K 2) := inferInstance
  haveI i5 : SecondCountableTopology (UPos (2 + 2) 2 → 𝔸[K]) := inferInstance
  haveI i9 : OpensMeasurableSpace (Par K) := oms5 _ _ _
  exact pt_cont.measurable

private theorem inv_eq (ξ : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) :
    (nn ξ * lv a b 0)⁻¹ = lv a⁻¹ b⁻¹ 0 * nn (-ξ) := by
  obtain ⟨-, hm, h1, -⟩ := blkLaws (K := K)
  refine inv_eq_of_mul_eq_one_right ?_
  rw [mul_assoc, ← mul_assoc (lv a b 0), hm, mul_inv_cancel, mul_inv_cancel, add_zero, h1, one_mul, ← nn_add,
    add_neg_cancel, nn_zero]

private theorem unfX (Φ : G1 K (2 + 2) → ℝ≥0∞) (hΦ : Measurable Φ) (a b m₁ m₂ : G1 K 2) (t : ℝ) (k : G1 K (2 + 2)) :
    ∫⁻ X, Φ (nn X * lv (a⁻¹ * m₁) (b⁻¹ * m₂) t * k) ∂unipMeasure K (2 + 2) 2 =
      ∫⁻ X, ∑' ξ : unipLattice K (2 + 2) 2, Φ ((nn ξ.1 * lv a b 0)⁻¹ * (nn X * lv m₁ m₂ t * k))
        ∂(unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2) := by
  obtain ⟨e, he, hme⟩ := adMeas a⁻¹ b⁻¹ 0
  obtain ⟨-, hm, -⟩ := blkLaws (K := K)
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at hme
  have hmeas : ∀ c : G1 K (2 + 2), Measurable fun X : UPos (2 + 2) 2 → 𝔸[K] => Φ (c * (nn X * lv m₁ m₂ t * k)) :=
    fun c => hΦ.comp (continuous_const.mul ((nn_cont.mul continuous_const).mul continuous_const)).measurable
  have h1 : ∀ X, Φ (nn X * lv (a⁻¹ * m₁) (b⁻¹ * m₂) t * k) = Φ (lv a⁻¹ b⁻¹ 0 * (nn (e X) * lv m₁ m₂ t * k)) := by
    intro X
    have : lv (a⁻¹ * m₁) (b⁻¹ * m₂) t = lv a⁻¹ b⁻¹ 0 * lv m₁ m₂ t := by rw [hm, zero_add]
    rw [this, ← mul_assoc (nn X), he]
    simp only [mul_assoc]
  simp only [h1]
  have hec : Measurable (e : (UPos (2 + 2) 2 → 𝔸[K]) → (UPos (2 + 2) 2 → 𝔸[K])) := e.continuous.measurable
  rw [← lintegral_map (hmeas _) hec, hme,
    isAddFundamentalDomain_unipFundamentalDomain.lintegral_eq_tsum',
    lintegral_tsum fun ξ => (hmeas _).aemeasurable]
  refine tsum_congr fun ξ => lintegral_congr fun X => ?_
  have : (-ξ) +ᵥ X = -ξ.1 + X := rfl
  rw [this, inv_eq, nn_add]
  simp only [mul_assoc]

private theorem sum_one (E : Set (G1 K (2 + 2))) (hE : ∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E)
    (Ψ : G1 K (2 + 2) → ℝ≥0∞) (hΨ : ∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) (y : G1 K (2 + 2)) :
    ∑' a : Gam K 2, ∑' b : Gam K 2, ∑' ξ : unipLattice K (2 + 2) 2,
      E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * y) = Ψ y := by
  obtain ⟨-, hP, hinj, -⟩ := pkLaws (K := K)
  obtain ⟨δ, hδ, hu⟩ := hE y
  obtain ⟨ξ₀, a₀, b₀, h0⟩ := (hP _).1 ((PK K).inv_mem δ.2)
  have key : ∀ (a b : Gam K 2) (ξ : unipLattice K (2 + 2) 2), ¬ (a = a₀ ∧ b = b₀ ∧ ξ = ξ₀) →
      E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * y) = 0 := by
    intro a b ξ hne
    refine indicator_of_notMem (fun hm => hne ?_) _
    have := hu ⟨_, (PK K).inv_mem ((hP _).2 ⟨ξ, a, b, rfl⟩)⟩ hm
    rw [← this] at h0
    obtain ⟨h1, h2, h3, -⟩ := hinj _ _ _ _ _ _ _ _ ((inv_inv _).symm.trans h0)
    exact ⟨Subtype.ext h2, Subtype.ext h3, Subtype.ext h1⟩
  rw [tsum_eq_single a₀ fun a ha => by simp only [key a _ _ fun h => ha h.1, tsum_zero],
    tsum_eq_single b₀ fun b hb => by simp only [key a₀ b _ fun h => hb h.2.1, tsum_zero],
    tsum_eq_single ξ₀ fun ξ hξ => key _ _ _ fun h => hξ h.2.2, ← h0, inv_inv]
  exact (indicator_of_mem hδ _).trans (hΨ _ δ.2 _)

set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.coordUnf :
    ∀ {K : Type} [Field K] [NumberField K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (κ : Measure (KG K (2 + 2))) [κ.IsHaarMeasure] (E : Set (G1 K (2 + 2))), MeasurableSet E → (∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E) →
      ∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
        ∫⁻ m₁, ∫⁻ m₂, ∫⁻ t : ℝ, ∫⁻ k : KG K (2 + 2), ∫⁻ X, E.indicator Ψ (nn X * lv m₁ m₂ t * k) * ENNReal.ofReal (Real.exp (-4 * t))
          ∂unipMeasure K (2 + 2) 2 ∂κ ∂volume ∂μ₂ ∂μ₂ = ∫⁻ p, Ψ (pt p) ∂parM μ₂ κ := by
  intro K _ _ μ₂ _ κ _ E hEm hE Ψ hΨm hΨ
  haveI : CompactSpace (KG K (2 + 2)) :=
    isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 (2 + 2)).1
  haveI : SFinite κ := inferInstance
  haveI : SFinite (fd μ₂) := inferInstance
  haveI : SFinite ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)) := inferInstance
  haveI : SFinite (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2))) := inferInstance
  haveI : SFinite (((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-4 * t))).prod
    (κ.prod ((unipMeasure K (2 + 2) 2).restrict (unipFundamentalDomain K (2 + 2) 2)))) := inferInstance
  have hΦ : Measurable (E.indicator Ψ) := hΨm.indicator hEm
  set S : Gam K 2 → Gam K 2 → Par K → ℝ≥0∞ := fun a b p => ∑' ξ : unipLattice K (2 + 2) 2,
    E.indicator Ψ ((nn ξ.1 * lv a b 0)⁻¹ * pt p) with hS
  have hSm : ∀ a b, Measurable (S a b) := fun a b =>
    Measurable.tsum fun ξ => hΦ.comp (pt_meas.const_mul _)
  have hTm : ∀ a, Measurable fun p => ∑' b, S a b p := fun a => Measurable.tsum (hSm a)
  have hR : ∀ p, Ψ (pt p) = ∑' a, ∑' b, S a b p := fun p => (sum_one E hE Ψ hΨ _).symm
  simp only [hR]
  rw [lintegral_tsum fun a => (hTm a).aemeasurable,
    (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']
  refine tsum_congr fun a => ?_
  rw [parM, lintegral_prod _ (hTm a).aemeasurable]
  refine lintegral_congr fun m₁ => ?_
  have h2 : ∀ b, Measurable fun q => S a b (m₁, q) := fun b => (hSm a b).comp measurable_prodMk_left
  rw [lintegral_tsum fun b => (h2 b).aemeasurable,
    (isFundamentalDomain_fundamentalDomain (Gam K 2) μ₂).lintegral_eq_tsum']
  refine tsum_congr fun b => ?_
  rw [lintegral_prod _ (h2 b).aemeasurable]
  refine lintegral_congr fun m₂ => ?_
  rw [iter3 _ _ (fun y => S a b (m₁, m₂, y)) ((h2 b).comp measurable_prodMk_left)]
  refine lintegral_congr fun t => ?_
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun k => ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact congrArg (· * _) (unfX _ hΦ a b m₁ m₂ t k)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TowerPoint
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem tower_point {G : Type*} [Group G] (Γ : Subgroup G) (P : Subgroup Γ) (E : Set G)
    (hE : ∀ x : G, ∃! γ : P.map Γ.subtype, γ • x ∈ E) (Ψ : G → ℝ≥0∞)
    (hΨ : ∀ γ ∈ P.map Γ.subtype, ∀ g, Ψ (γ * g) = Ψ g) (y : G) :
    ∑' γ : Γ, E.indicator Ψ ((γ : G) * y) =
      ∑' q : Quotient (QuotientGroup.rightRel P), Ψ (((q.out : Γ) : G) * y) := by
  classical
  rw [← (Equiv.sigmaFiberEquiv (fun γ : Γ => (Quotient.mk (QuotientGroup.rightRel P) γ))).tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun q => ?_
  obtain ⟨⟨δ, hδ⟩, hδE, huniq⟩ := hE (((q.out : Γ) : G) * y)
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hδ
  have hmk : Quotient.mk (QuotientGroup.rightRel P) (p * q.out) = q := by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Quotient.sound ?_
    change (QuotientGroup.rightRel P) _ _
    rw [QuotientGroup.rightRel_apply]
    simpa using P.inv_mem hp
  have hδE' : (p : G) * (((q.out : Γ) : G) * y) ∈ E := hδE
  rw [tsum_eq_single ⟨p * q.out, hmk⟩]
  · simp only [Equiv.sigmaFiberEquiv_apply, Subgroup.coe_mul, mul_assoc]
    rw [indicator_of_mem hδE']
    exact hΨ _ hδ _
  · rintro ⟨γ, hγ⟩ hne
    simp only [Equiv.sigmaFiberEquiv_apply]
    refine indicator_of_notMem (fun hmem => hne ?_) _
    have hrel : (QuotientGroup.rightRel P) q.out γ := by
      refine Quotient.exact ?_
      rw [Quotient.out_eq, hγ]
    rw [QuotientGroup.rightRel_apply] at hrel
    have h1 := huniq ⟨((γ * q.out⁻¹ : Γ) : G), Subgroup.mem_map.2 ⟨_, hrel, rfl⟩⟩ (by
      change ((γ * q.out⁻¹ : Γ) : G) * (((q.out : Γ) : G) * y) ∈ E
      simpa [mul_assoc] using hmem)
    have h2 : γ * q.out⁻¹ = p := Subtype.ext (congrArg (fun z : P.map Γ.subtype => (z : G)) h1)
    refine Subtype.ext ?_
    change γ = p * q.out
    rw [← h2]; simp

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.tower :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (E : Set (G1 K (2 + 2))), MeasurableSet E → (∀ x : G1 K (2 + 2), ∃! γ : PK K, γ • x ∈ E) →
      ∀ Ψ : G1 K (2 + 2) → ℝ≥0∞, Measurable Ψ → (∀ γ ∈ PK K, ∀ g, Ψ (γ * g) = Ψ g) →
        ∫⁻ y, ∑' q : Cos K, Ψ ((q.out : G1 K (2 + 2)) * y) ∂fd μ = ∫⁻ g in E, Ψ g ∂μ := by
  intro K _ _ μ _ E hEm hE Ψ hΨm hΨ
  haveI : Countable (Gam K (2 + 2)) := inferInstance
  have hD := isFundamentalDomain_fundamentalDomain (Gam K (2 + 2)) μ
  set_option synthInstance.maxHeartbeats 200000 in
    rw [← lintegral_indicator hEm, hD.lintegral_eq_tsum'', ← lintegral_tsum]
  · refine lintegral_congr fun y => ?_
    exact (tower_point (Gam K (2 + 2)) (ParΓ K 2 2) E hE Ψ hΨ y).symm
  · intro γ
    exact ((hΨm.indicator hEm).comp (measurable_const_mul (γ : G1 K (2 + 2)))).aemeasurable
end

