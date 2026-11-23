module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.KHerm

variable {n : ℕ}

def skA (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

def skB (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b Complex.I + Matrix.single b a Complex.I)

theorem skA_skew (a b : Fin n) : (skA a b)ᴴ = -skA a b := by
  ext i j
  simp only [skA, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem skB_skew (a b : Fin n) : (skB a b)ᴴ = -skB a b := by
  ext i j
  simp only [skB, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have h1 : (Kf a b h).1 g = (e1 DR a b h).1 g - (f1 DR b a h).1 g := by
    simp [Kf, e2, sub_eq_add_neg]
  rw [h1, orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, liftOneFormsToCompatible_apply b a h hg]
  simp only [Eu, Rd, skA, skB, Pi.smul_apply, Pi.add_apply, ite_true, Bool.false_eq_true, ite_false,
    Matrix.mul_smul, mul_sub, mul_add, map_smul, map_sub, map_add, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem Rd_neg (X : Mat n) (f : Mat n → ℂ) (g : Mat n) : Rd (-X) f g = -Rd X f g := by
  simp [Rd]

theorem Kf_apply_swap (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf b a h).1 g = -Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have hA : skA b a = -skA a b := by
    simp only [skA, ← smul_neg, neg_sub]
  have hB : skB b a = skB a b := by
    simp only [skB, add_comm]
  rw [Kf_apply b a h hg, hA, hB, Rd_neg]

theorem Rd_conj_mul (X : Mat n) {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (fun g => conj (x g) * y g) g = conj (Rd X x g) * y g + conj (x g) * Rd X y g := by
  have dx := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hx hg).hasFDerivAt
  have dy := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hy hg).hasFDerivAt
  have dc : HasFDerivAt (fun g => conj (x g)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ x g)) g :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp g dx
  have hm : HasFDerivAt (fun g => conj (x g) * y g) _ g := dc.mul dy
  simp only [Rd]
  rw [hm.fderiv]
  change conj (x g) * fderiv ℝ y g (g * X) + y g * conj (fderiv ℝ x g (g * X)) = _
  ring

theorem conj_mul_smooth {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n)) :
    ContDiffOn ℝ ∞ (fun g => conj (x g) * y g) (GLs n) :=
  (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hx).mul hy

section Int

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

omit [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] in
theorem cont_on_unit {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => f k.1 :=
  hf.comp_continuous continuous_subtype_val fun k => unit_mem k

theorem integrable_of_cont {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Int

end GlobalTheory.CompanionTheory.ModelS.KHerm


open GlobalTheory.CompanionTheory.ModelS.KHerm in
theorem GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  intro n _ _ κ _ hI a b x y
  have hx := x.2.1
  have hy := y.2.1
  have i1 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (Rd X x.1 k.1) * y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hx).continuousOn)).mul (cont_on_unit hy.continuousOn))
  have i2 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * Rd X y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp (cont_on_unit hx.continuousOn)).mul
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hy).continuousOn))
  have key : ∀ X : Mat n, Xᴴ = -X → (∫ k, conj (Rd X x.1 k.1) * y.1 k.1 ∂κ) + ∫ k, conj (x.1 k.1) * Rd X y.1 k.1 ∂κ = 0 := by
    intro X hX
    rw [← integral_add (i1 X) (i2 X), ← hI _ (conj_mul_smooth hx hy) X hX]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => (Rd_conj_mul X hx hy (unit_mem k)).symm)
  have L : ipK κ (Kf a b x) y = (∫ k, conj (Rd (skA a b) x.1 k.1) * y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (Rd (skB a b) x.1 k.1) * y.1 k.1 ∂κ := by
    rw [← integral_const_mul, ← integral_add (i1 _) ((i1 _).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply a b x (unit_mem k), map_sub, map_mul, Complex.conj_I]
    ring
  have R : ipK κ x (Kf b a y) = -((∫ k, conj (x.1 k.1) * Rd (skA a b) y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (x.1 k.1) * Rd (skB a b) y.1 k.1 ∂κ) := by
    rw [← integral_const_mul, ← integral_add (i2 _) ((i2 _).const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply_swap a b y (unit_mem k)]
    ring
  rw [L, R]
  linear_combination key _ (skA_skew a b) + Complex.I * key _ (skB_skew a b)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianForm
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  delta ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  delta ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  delta ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  delta ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowUpdateNhdsGeneration
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

variable {k : Type} [Field k] {n : ℕ}

def lastRowMat (r : Fin (n + 1) → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r

def rowInv (r : Fin (n + 1) → k) : Fin (n + 1) → k :=
  fun j => if j = Fin.last n then (r (Fin.last n))⁻¹ else -r j * (r (Fin.last n))⁻¹

theorem lastRowMat_mul_last (r s : Fin (n + 1) → k) (j : Fin (n + 1)) :
    (lastRowMat r * lastRowMat s) (Fin.last n) j =
      (if j = Fin.last n then 0 else r j) + r (Fin.last n) * s j := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_self,
    Matrix.updateRow_ne (Fin.castSucc_ne_last _), Matrix.one_apply]
  congr 1
  first
  | refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [Fin.castSucc_ne_last]
    · simp [Fin.castSucc_ne_last]
  | induction j using Fin.lastCases with
    | last => simp [Fin.castSucc_ne_last]
    | cast j => simp [Fin.castSucc_ne_last]

theorem lastRowMat_mul_rowInv {r : Fin (n + 1) → k} (hr : r (Fin.last n) ≠ 0) :
    lastRowMat r * lastRowMat (rowInv r) = 1 := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst hi
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat_mul_last]
    by_cases hj : j = Fin.last n
    · subst hj
      first
      | simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, hr]
      | (simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_true, ite_true, zero_add, Matrix.one_apply_eq]
         exact mul_inv_cancel₀ hr)
    · rw [Matrix.one_apply_ne (Ne.symm hj), if_neg hj]
      simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
      linear_combination (-r j) * mul_inv_cancel₀ hr
  · first
    | (rw [Matrix.mul_apply]
       simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi]
       rw [← Matrix.mul_apply, Matrix.one_mul, Matrix.updateRow_ne hi])
    | simp [Matrix.mul_apply, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, Matrix.updateRow_ne hi, Matrix.one_apply,
        Matrix.updateRow_apply, hi]

def lastRowGL (r : Fin (n + 1) → k) (hr : r (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k where
  val := lastRowMat r
  inv := lastRowMat (rowInv r)
  val_inv := lastRowMat_mul_rowInv hr
  inv_val := mul_eq_one_comm.1 (lastRowMat_mul_rowInv hr)

def invRow (x : GL (Fin (n + 1)) k) : Fin (n + 1) → k :=
  fun j => ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j

theorem invRow_one : invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) = 1 := by
  simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]

theorem vecMul_eLast (x : GL (Fin (n + 1)) k) :
    vecMul (eLast k n) (lastRowMat (invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) = eLast k n := by
  have h : vecMul (GlobalTheory.BZMir.eLast k n) (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)) =
      vecMul (GlobalTheory.BZMir.eLast k n)
        ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    ext j
    first
    | simp [GlobalTheory.BZMir.eLast, Matrix.single_vecMul, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
    | simp [GlobalTheory.BZMir.eLast, Matrix.vecMul, dotProduct, Pi.single_apply,
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat, GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow, Matrix.updateRow_apply]
  rw [← Matrix.vecMul_vecMul, h, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

section Top

variable [TopologicalSpace k] [IsTopologicalDivisionRing k] [T1Space k]

theorem continuous_invRow : Continuous (invRow : GL (Fin (n + 1)) k → _) := by
  have hc : Continuous fun x : GL (Fin (n + 1)) k =>
      ((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow
  first
  | exact continuous_pi fun j => hc.matrix_elem (Fin.last n) j
  | exact continuous_pi fun j => (continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hc)

theorem continuous_lastRowMat : Continuous (lastRowMat : (Fin (n + 1) → k) → _) := by
  unfold GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat
  exact continuous_const.matrix_updateRow (Fin.last n) continuous_id

theorem continuousAt_rowInv : ContinuousAt (fun x : GL (Fin (n + 1)) k => rowInv (invRow x)) 1 := by
  have hv : Continuous (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow : GL (Fin (n + 1)) k → _) := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow
  have hl : ContinuousAt (fun x : GL (Fin (n + 1)) k => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n))⁻¹) 1 :=
    ((continuous_apply (Fin.last n)).comp hv).continuousAt.inv₀
      (show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 by
        rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero)
  refine continuousAt_pi.2 fun j => ?_
  by_cases hj : j = Fin.last n
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_pos hj]
    exact hl
  · simp only [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv, if_neg hj]
    exact (((continuous_apply j).comp hv).continuousAt.neg).mul hl

theorem exists_nhd {V : Set (GL (Fin (n + 1)) k)} (hV : V ∈ 𝓝 (1 : GL (Fin (n + 1)) k)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ x ∈ N, ∃ hr : invRow x (Fin.last n) ≠ 0,
      lastRowGL (invRow x) hr * x ∈ V := by
  have h1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
    rw [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow_one]; exact one_ne_zero
  have hv1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
    funext j; simp [GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow]
  have hg1 : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) h1 = 1 := by
    apply Units.ext
    show GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow (1 : GL (Fin (n + 1)) k)) = 1
    rw [hv1]
    exact Matrix.updateRow_eq_self _ _
  let ψ : GL (Fin (n + 1)) k →
      Matrix (Fin (n + 1)) (Fin (n + 1)) k × (Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵐᵒᵖ :=
    fun x => (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k),
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x))))
  have hψ : ∀ x (hr : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x) = ψ x := fun x hr => by
    first
    | rfl
    | (rw [Units.embedProduct_apply]; rfl)
  have hfst : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) * (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) 1 := by
    first
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).mul
        Units.continuous_val).continuousAt
    | exact ((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).matrix_mul
        Units.continuous_val).continuousAt
  have hsnd : ContinuousAt (fun x : GL (Fin (n + 1)) k =>
      MulOpposite.op (((x⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
        GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowMat (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.rowInv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x)))) 1 :=
    MulOpposite.continuous_op.continuousAt.comp
      ((Units.continuous_coe_inv (M := Matrix (Fin (n + 1)) (Fin (n + 1)) k)).continuousAt.mul
        (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_lastRowMat.continuousAt.comp
          GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuousAt_rowInv))
  have hψc : ContinuousAt ψ 1 := hfst.prodMk hsnd
  have hψ1 : ψ 1 = Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1 := by
    rw [← hψ 1 h1, hg1, mul_one]
  obtain ⟨U, hU, hUV⟩ : ∃ U ∈ 𝓝 (Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) 1),
      Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k) ⁻¹' U ⊆ V := by
    rw [Units.isEmbedding_embedProduct.toIsInducing.nhds_eq_comap] at hV
    exact Filter.mem_comap.1 hV
  have hne : ∀ᶠ x in 𝓝 (1 : GL (Fin (n + 1)) k), GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).comp GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.continuous_invRow).continuousAt.eventually_ne h1
  refine ⟨ψ ⁻¹' U ∩ {x | GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x (Fin.last n) ≠ 0},
    Filter.inter_mem (hψc.preimage_mem_nhds (by rw [hψ1]; exact hU)) hne, ?_⟩
  rintro x ⟨hxU, hx⟩
  refine ⟨hx, hUV ?_⟩
  show Units.embedProduct (Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hx * x) ∈ U
  rw [hψ x hx]
  exact hxU

end Top

theorem row_replacement (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (S : Subgroup (GL (Fin (n + 1)) k))
    (hS : ∀ (r : Fin (n + 1) → k), r (Fin.last n) ≠ 0 → ∀ g : GL (Fin (n + 1)) k,
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow (Fin.last n) r → g ∈ S)
    (O : Set (Mir k n)) (hO : O ∈ 𝓝 (1 : Mir k n)) :
    ∃ N ∈ 𝓝 (1 : GL (Fin (n + 1)) k), ∀ p ∈ S, ∀ x ∈ N, ∀ m : Mir k n, (m : GL (Fin (n + 1)) k) = p * x →
      ∃ a : Mir k n, (a : GL (Fin (n + 1)) k) ∈ S ∧ ∃ x' ∈ O, m = a * x' := by
  obtain ⟨V, hV, hVO⟩ := (mem_nhds_subtype _ _ _).1 hO
  obtain ⟨N, hN, hNV⟩ := GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.exists_nhd (k := k) (n := n) hV
  refine ⟨N, hN, fun p hp x hx m hm => ?_⟩
  obtain ⟨hr, hgx⟩ := hNV x hx
  have hgS : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr ∈ S := hS _ hr _ rfl
  have hmir : GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x ∈ GlobalTheory.BZMir.Mir k n :=
    GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.vecMul_eLast x
  refine ⟨m * ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩⁻¹, ?_,
    ⟨GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x, hmir⟩, hVO hgx, (inv_mul_cancel_right _ _).symm⟩
  show (m : GL (Fin (n + 1)) k) * (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.lastRowGL (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep.invRow x) hr * x)⁻¹ ∈ S
  rw [hm, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
  exact S.mul_mem hp (S.inv_mem hgS)

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO.RowRep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChain
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem adCL_mem_omU {n : ℕ} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hl : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) (hm : l ∈ omU lev) : k ∈ omU lev ∧ k ≠ l := by
  have hcase : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) ∨
      (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adCL, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := (mem_filter.1 hm).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev p < lev l.2.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev l.2.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem Lv_single_omU : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  intro n lev V _ _ E1 E2 u hu p q hpq hl
  have h1 : liftL n (kA E1 E2 p q) (Pi.single (omU lev) u : Cq n V) = 0 := by
    funext A
    rw [liftL_apply]
    by_cases e : A = omU lev
    · subst e
      rw [Pi.single_eq_same]
      exact hu p q hpq
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adLL lev false p q (Pi.single (omU lev) u : Cq n V) = 0 := by
    simp only [adLL, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hS
    swap
    · rfl
    by_cases hc : adCL false p q l k = 0
    · rw [hc, zero_smul]; rfl
    suffices h : creL k (annL l (Pi.single (omU lev) u : Cq n V)) = 0 by
      rw [LinearMap.smul_apply, Module.End.mul_apply, h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := creL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    have e : insert l (B.erase k) = omU lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hm : l ∈ omU lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hkl⟩ := adCL_mem_omU hpq hl hc hm
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hkl h5
    · exact notMem_erase _ _ h5
  show liftL n (kA E1 E2 p q) _ + adLL lev false p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.LvChain
end
end

