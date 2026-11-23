module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.DZMulDZInv
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem dZ_mul_dZ_inv (n : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) : dZ n ζ⁻¹ * dZ n ζ = 1 := by
  simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul,
    smul_smul, mul_inv_cancel₀ hζ, one_smul, smul_zero, Matrix.fromBlocks_one]

theorem rot_cols' (n m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) (s : ℤˣ) (t x y : ℝ) (Ww : Matrix (Fin m) (Fin n) ℂ) (D : M2 n)
    (hD : dZ n ζ * D = yrotM n s t * dZ n ζ) :
    Matrix.fromCols ((y : ℂ) • ((-(((s : ℤ) : ℂ) * ζ)) • Ww)) ((x : ℂ) • Ww) * Dᵀ =
      Matrix.fromCols (((y * Real.cos t - x * Real.sin t : ℝ) : ℂ) • ((-(((s : ℤ) : ℂ) * ζ)) • Ww))
        (((x * Real.cos t + y * Real.sin t : ℝ) : ℂ) • Ww) := by
  have cancel : ∀ X Y : Matrix (Fin m) (Fin n ⊕ Fin n) ℂ, X * (dZ n ζ)ᵀ = Y * (dZ n ζ)ᵀ → X = Y := by
    intro X Y h
    have h2 := congrArg (· * (dZ n ζ⁻¹)ᵀ) h
    simpa only [Matrix.mul_assoc, ← Matrix.transpose_mul, dZ_mul_dZ_inv n hζ, Matrix.transpose_one,
      Matrix.mul_one] using h2
  apply cancel
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hD, Matrix.transpose_mul, ← Matrix.mul_assoc]
  simp only [dZ, yrotM, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks, Matrix.mul_one, Matrix.mul_zero,
    Matrix.mul_smul, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul, add_zero, zero_add, smul_smul,
    ← add_smul]
  rcases Int.units_eq_one_or s with rfl | rfl <;>
  · congr 2 <;> push_cast <;> ring

end PositivityTheory.SiegelWeilFormula.KFP

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoRot
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem cw_mul' (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul

theorem cw_add' (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B

theorem cw_one' (w : InfinitePlace F) : d.cw w (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem cw_transpose' (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl

theorem incM_b_mul_inv (d : SD σ) : incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_b_inv_mul (d : SD σ) :
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
      incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_mul' (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)), incM_b_mul_inv, Matrix.one_mul]

theorem inFrame_one' : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, incM_b_inv_mul]

theorem matrix_eq_frame_conj (x : d.G) : mat2 x = incM F (d.b : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) * inFrame d.b x *
    incM F ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) := by
  simp only [inFrame, Matrix.mul_assoc]
  rw [incM_b_mul_inv, Matrix.mul_one, ← Matrix.mul_assoc, incM_b_mul_inv, Matrix.one_mul]

theorem cw_inFrame_prod' (R : RD d) (f : InfinitePlace F → GR d.n) (w' : InfinitePlace F) :
    ∀ L : List (InfinitePlace F), L.Nodup → d.cw w' (inFrame d.b ((L.map fun w => R.ι w (f w)).prod)) =
      if w' ∈ L then d.cw w' (inFrame d.b (R.ι w' (f w'))) else 1 := by
  intro L
  induction L with
  | nil => intro _; simp [inFrame_one', cw_one']
  | cons a L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.map_cons, List.prod_cons, inFrame_mul', cw_mul', ih hL.2]
    by_cases h : w' = a
    · subst h
      simp [hL.1]
    · rw [R.off_w a w' (f a) h, Matrix.one_mul]
      simp [h]

theorem dZ_cw_rot' (R : RD d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (rot R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  rw [rot, cw_inFrame_prod' R (fun w => yrot d.n (R.sg w) t) w _ (Finset.nodup_toList _),
    if_pos (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]

end PositivityTheory.SiegelWeilFormula.KFP

end
end

