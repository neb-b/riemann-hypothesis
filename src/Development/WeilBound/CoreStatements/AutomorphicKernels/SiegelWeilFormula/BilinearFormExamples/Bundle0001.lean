module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.MapCAMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.BfENondeg
section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def BfE (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) : LinearMap.BilinForm F (Matrix (Fin m) (Fin n) E) :=
  LinearMap.mk₂ F (fun x z => Algebra.trace F E (xᵀ * J * z.map σ).trace)
    (fun x x' z => by simp [Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add])
    (fun c x z => by simp [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul])
    (fun x z z' => by simp [Matrix.map_add _ (map_add σ), Matrix.mul_add, Matrix.trace_add])
    (fun c x z => by
      have : (c • z).map σ = c • z.map σ := by ext i j; exact σ.toLinearMap.map_smul c (z i j)
      simp [this, Matrix.mul_smul, Matrix.trace_smul])

theorem BfE_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (x z : Matrix (Fin m) (Fin n) E) :
    BfE σ J x z = Algebra.trace F E (xᵀ * J * z.map σ).trace := rfl

theorem BfE_nondeg [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) : (BfE (n := n) σ J).Nondegenerate := by
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hdetT : IsUnit Jᵀ.det := by
    rw [Matrix.det_transpose]
    exact hdet
  have htr1 : Algebra.trace F E 1 ≠ 0 := by
    rw [← map_one (algebraMap F E), Algebra.trace_algebraMap]
    simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
    exact Module.finrank_pos.ne'
  refine ⟨fun x hx => ?_, fun z hz => ?_⟩
  · by_contra hne
    have hy : Jᵀ * x ≠ 0 := by
      intro h0
      apply hne
      have h2 := congrArg (fun M => (Jᵀ)⁻¹ * M) h0
      simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetT] using h2
    obtain ⟨b0, j0, hb⟩ : ∃ b j, (Jᵀ * x) b j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (Matrix.ext h)
    have h1 := hx ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ)
    have hσσ : ((Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).map σ).map σ =
        Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹ := by
      ext a b
      simp only [Matrix.map_apply]
      exact hσ _
    have hswap : (xᵀ * J) j0 b0 = (Jᵀ * x) b0 j0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hv : (xᵀ * J * Matrix.single b0 j0 ((Jᵀ * x) b0 j0)⁻¹).trace = 1 := by
      rw [Matrix.trace_mul_single, hswap, op_smul_eq_mul, mul_inv_cancel₀ hb]
    rw [BfE_apply, hσσ, hv] at h1
    exact htr1 h1
  · by_contra hne
    have hw : J * z.map σ ≠ 0 := by
      intro h0
      apply hne
      have hz0 : z.map σ = 0 := by
        have h2 := congrArg (fun M => J⁻¹ * M) h0
        simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet] using h2
      ext a b
      have := congrFun (congrFun hz0 a) b
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      rw [Matrix.zero_apply, ← hσ (z a b), this, map_zero]
    obtain ⟨a0, b0, hb⟩ : ∃ a b, (J * z.map σ) a b ≠ 0 := by
      by_contra h
      push_neg at h
      exact hw (Matrix.ext h)
    have h1 := hz (Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)
    have hv : ((Matrix.single a0 b0 ((J * z.map σ) a0 b0)⁻¹)ᵀ * J * z.map σ).trace = 1 := by
      rw [Matrix.mul_assoc, Matrix.transpose_single, Matrix.trace_single_mul]
      simp [inv_mul_cancel₀ hb, mul_inv_cancel₀ hb]
    rw [BfE_apply, hv] at h1
    exact htr1 h1

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.TraceIntMul
section
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

theorem trace_int_mul (u : ℤ) (t : AE F E) :
    Algebra.trace (AF F) (AE F E) ((u : AE F E) * t) = (u : AF F) * Algebra.trace (AF F) (AE F E) t := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem trace_map_cA {σ : E →ₐ[F] E} {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) :
    (M.map (cA σ)).trace = cA σ M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

theorem Bf_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E) (u : ℤ)
    (hJ : ∀ i j, σ (J j i) = (u : E) * J i j) (X Z : Mx F E m n) :
    Bf σ J X Z = (u : AF F) * Bf σ J Z X := by
  have hJc : (incM F J).map (cA σ) = ((u : ℤ) : AE F E) • (incM F J)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    change cA σ (inclR (F := F) (AF F) (J i j)) = _ * inclR (F := F) (AF F) (J j i)
    rw [show cA σ (inclR (F := F) (AF F) (J i j)) = inclR (F := F) (AF F) (σ (J i j)) from rfl, hJ j i, map_mul, map_intCast]
  have hcc : (Z.map (cA σ)).map (cA σ) = Z := by ext i j; exact cA_cA hσ _
  unfold Bf
  rw [← trace_cA hσ, ← trace_map_cA, map_cA_mul, map_cA_mul, Matrix.transpose_map, hJc, hcc,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_int_mul]
  congr 2
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem mapS_mul {σ : E →ₐ[F] E} {a b c : Type} [Fintype b] (x : Matrix a b E) (y : Matrix b c E) :
    (x * y).map σ = x.map σ * y.map σ := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem congr_symm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {ι : Type} [Fintype ι] (D b : Matrix ι ι E) (u : ℤ)
    (hD : Dᵀ.map σ = (u : E) • D) : ((bᵀ * D * b.map σ).map σ)ᵀ = (u : E) • (bᵀ * D * b.map σ) := by
  have hbb : (b.map σ).map σ = b := by ext i j; simp [hσ]
  rw [mapS_mul, mapS_mul, hbb, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.transpose_map,
    ← Matrix.transpose_map, Matrix.transpose_transpose, hD, Matrix.smul_mul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

theorem eps_eq {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) (YJ : Matrix (Fin n) (Fin n) E) (u : ℤ)
    (hY : ∀ i j, σ (YJ j i) = (u : E) * YJ i j) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε) (hn : 1 ≤ n) : (ε : ℤ) = u := by
  have hD : (dbl YJ)ᵀ.map σ = (u : E) • dbl YJ := by
    ext (i | i) (j | j) <;> simp [dbl, hY]
  have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => M (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩))
    (congr_symm hσ (dbl YJ) b.1 u hD)
  simp only [hb] at h
  simp [jeps] at h
  exact_mod_cast h

end PositivityTheory.SiegelWeilFormula.Ldexa
end
end

