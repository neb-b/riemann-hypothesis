module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real MeasureTheory

namespace KThetaMean

variable {g : ℕ}

theorem continuous_exp_qf_add (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ) (a : Fin g → ℝ) :
    Continuous fun x : Fin g → ℝ => exp (-c * qf Y (x + a)) := by
  have h1 : Continuous fun x : Fin g → ℝ => x + a := continuous_id.add continuous_const
  have h2 : Continuous fun x : Fin g → ℝ => qf Y (x + a) := by
    unfold qf
    exact h1.dotProduct (continuous_const.matrix_mulVec h1)
  exact (continuous_const.mul h2).rexp

end KThetaMean

theorem ThetaMean.proof (h : ThetaInnerMean.Statement) : ThetaMean.Statement := by
  intro g X Y a b hY
  set F : (Fin g → ℝ) → ℝ := fun x => exp (-(2 * π) * qf Y (x + a)) with hF
  have hinner : ∀ u₁ : Fin g → ℝ,
      ∫ u₂ in Set.Icc (0 : Fin g → ℝ) 1, thetaNorm X Y a b u₁ u₂ ^ 2 =
        ∑' k : Fin g → ℤ, F (intVec k + u₁) := by
    intro u₁
    rw [h g X Y a b u₁ hY]
    congr 1
    simp [hF, add_assoc, add_comm, add_left_comm]
  simp_rw [hinner]
  have hs : ∀ u : Fin g → ℝ, Summable fun k : Fin g → ℤ => F (intVec k + u) := by
    intro u
    simp only [hF, add_assoc]
    exact KTheta.summable_exp_qf Y hY (2 * π) (by positivity) (u + a)
  rw [KTheta.integral_cube_tsum F (fun x => (exp_pos _).le)
    (KThetaMean.continuous_exp_qf_add Y (2 * π) a) hs]
  rw [hF, integral_add_right_eq_self (fun x : Fin g → ℝ => exp (-(2 * π) * qf Y x)) a]
  exact KTheta.integral_exp_two_pi_qf Y hY

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaNormMajorant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

namespace KThetaNormMajorant

theorem isSymm_of_posDef {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) : Y.IsSymm := by
  have h := hY.isHermitian
  unfold Matrix.IsHermitian at h
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

end KThetaNormMajorant

theorem ThetaNormMajorant.proof (h : ThetaSummandNorm.Statement) : ThetaNormMajorant.Statement := by
  intro g X Y a b u₁ u₂ hY
  have hS := KThetaNormMajorant.isSymm_of_posDef hY
  set z : Fin g → ℂ := periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ) with hz
  set E : ℝ := exp (-π * qf Y u₁) with hE
  have hEpos : 0 < E := exp_pos _
  have hterm : ∀ k : Fin g → ℤ,
      ‖thetaSummand X Y a b z k‖ = exp (-π * qf Y (intVec k + a + u₁)) * E⁻¹ := by
    intro k
    rw [← h g X Y a b u₁ u₂ k hS, mul_inv_cancel_right₀ hEpos.ne']
  have hG : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π Real.pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hsum : Summable fun k : Fin g → ℤ => ‖thetaSummand X Y a b z k‖ := by
    simp_rw [hterm]
    exact hG.mul_right _
  have hN : thetaNorm X Y a b u₁ u₂ = ‖∑' k, thetaSummand X Y a b z k‖ * E := rfl
  rw [hN]
  calc ‖∑' k, thetaSummand X Y a b z k‖ * E
      ≤ (∑' k, ‖thetaSummand X Y a b z k‖) * E :=
        mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hsum) hEpos.le
    _ = ∑' k, ‖thetaSummand X Y a b z k‖ * E := (tsum_mul_right).symm
    _ = ∑' k : Fin g → ℤ, exp (-π * qf Y (intVec k + a + u₁)) := by
        congr 1; funext k
        rw [hterm, inv_mul_cancel_right₀ hEpos.ne']

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def GrassGeomDegChart.Statement : Prop :=
  ∀ n : ℕ, ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = chartMass (Bᴴ * B)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassLinesProj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder

noncomputable section

def stdLattice (K : Type*) [Field K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.span (𝓞 K) (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K))

def stdSumBasis (K : Type*) [Field K] (m k : ℕ) : Module.Basis (Fin m ⊕ Fin k) K (Fin (m + k) → K) :=
  (Pi.basisFun K (Fin (m + k))).reindex finSumFinEquiv.symm

def LinesLatticeBasis.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι],
    Fintype.card ι = Module.finrank ℚ V → ∀ M : Submodule ℤ V, Submodule.IsFullLattice ℚ M →
      ∃ b : Module.Basis ι ℚ V, M = Submodule.span ℤ (Set.range b)

def LinesGenIndexDet.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (ι : Type) [Fintype ι]
    [DecidableEq ι] (bA bB : Module.Basis ι ℚ V) (A B : AddSubgroup V),
    A = AddSubgroup.closure (Set.range bA) → B = AddSubgroup.closure (Set.range bB) →
      genIndex A B = |((bA.det bB : ℚ) : ℝ)|

def LinesIsLattice.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (M : Submodule (𝓞 K) (ι → K)),
    (M.restrictScalars ℤ).FG → Submodule.span K (M : Set (ι → K)) = ⊤ →
      Submodule.IsFullLattice ℚ (M.restrictScalars ℤ)

def LinesGenIndexTrans.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (A B C : Submodule ℤ V),
    Submodule.IsFullLattice ℚ A → Submodule.IsFullLattice ℚ B → Submodule.IsFullLattice ℚ C →
      0 < genIndex A.toAddSubgroup B.toAddSubgroup ∧
        genIndex A.toAddSubgroup B.toAddSubgroup * genIndex B.toAddSubgroup C.toAddSubgroup =
          genIndex A.toAddSubgroup C.toAddSubgroup

def LinesIdealLatticeFG.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (a : Fin n → FractionalIdeal (𝓞 K)⁰ K),
    (∀ x, a x ≠ 0) →
      (idealLattice a).FG ∧ Submodule.span K (idealLattice a : Set (Fin n → K)) = ⊤

theorem stdSumBasis_inl (K : Type*) [Field K] (m k : ℕ) (i : Fin m) :
    stdSumBasis K m k (Sum.inl i) = Pi.single (Fin.castAdd k i) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_inr (K : Type*) [Field K] (m k : ℕ) (j : Fin k) :
    stdSumBasis K m k (Sum.inr j) = Pi.single (Fin.natAdd m j) 1 := by
  simp [stdSumBasis]

theorem stdSumBasis_elim (K : Type*) [Field K] (m k : ℕ) :
    Sum.elim (fun i => stdSumBasis K m k (Sum.inl i)) (fun j => stdSumBasis K m k (Sum.inr j)) =
      ⇑(stdSumBasis K m k) := by
  funext x; cases x <;> rfl

theorem stdLattice_isLattice_example :
    Submodule.IsFullLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) := by
  have : Submodule.IsLattice ℚ ((stdLattice ℚ 1).restrictScalars ℤ) :=
    Submodule.IsLattice.of_fg ℚ ((Submodule.fg_span (Set.finite_range _)).restrictScalars)
  refine { span_eq_top := ?_ }
  change Submodule.span ℚ (stdLattice ℚ 1 : Set (Fin 1 → ℚ)) = ⊤
  rw [stdLattice, Submodule.span_span_of_tower (𝓞 ℚ)]
  have h : ⇑(Pi.basisFun ℚ (Fin 1)) = fun j => Pi.single j 1 :=
    funext (Pi.basisFun_apply ℚ (Fin 1))
  rw [← h, Module.Basis.span_eq]

end

end GroundTheory.Heights₂.Heights
end

