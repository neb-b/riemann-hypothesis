module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem GaussianSum.full : GaussianSum.Statement :=
  GaussianSum.proof
    (GaussPoissonDual.proof GaussSqrt.proof
      (GaussPoissonBound.proof GaussLatticeIsLattice.proof
        (GaussLatticeCovolume.proof GaussLatticeIsLattice.proof) GaussLatticeCoords.proof
        GaussFourierSelf.proof)
      GaussDualMin.proof GaussDetFactor.proof)
    (GaussShellSum.proof (GaussShell.proof GaussPacking.proof GaussTermBound.proof))
    GaussConstant.proof

theorem ThetaMean.full : ThetaMean.Statement :=
  ThetaMean.proof
    (ThetaInnerMean.proof ThetaSummandNorm.proof
      (ThetaCubeParseval.proof ThetaCharIntegral.proof))

theorem ThetaBound.full : ThetaBound.Statement :=
  ThetaBound.proof GaussianSum.full ThetaMean.full
    (ThetaNormMajorant.proof ThetaSummandNorm.proof) ThetaFirstCoordSplit.proof ThetaConstants.proof

theorem PlueckerNormSq.full : PlueckerNormSq.Statement := PlueckerNormSq.proof CauchyBinet.proof

theorem PlueckerUnitBound.full : PlueckerUnitBound.Statement :=
  PlueckerUnitBound.proof HadamardPSD.proof

theorem PlueckerKernel.full : PlueckerKernel.Statement :=
  PlueckerKernel.proof PlueckerNormSq.full PlueckerUnitBound.full

theorem RootsOfUnityDense.full : RootsOfUnityDense.Statement := RootsOfUnityDense.proof

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {e : ℕ}

def chartInv (y : Fin (e + 1) → ℂ) : Fin (e + 1) → ℂ := fun j => (y 0)⁻¹ * (if j = 0 then 1 else y j)

theorem chartInv_zero (y : Fin (e + 1) → ℂ) : chartInv y 0 = (y 0)⁻¹ := by
  simp [chartInv]

theorem chartInv_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [chartInv]
  · simp only [chartInv, hj, if_false, if_true]
    field_simp

theorem swap_mulVec_cons (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    swapFirstTwo e *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) =
      y 0 • (Fin.cons 1 (chartInv y) : Fin (e + 1 + 1) → ℂ) := by
  funext p
  rw [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]
  refine Fin.cases ?_ (fun i => ?_) p
  · simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [chartInv, hy]
    · have h0 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
        exact Fin.succ_ne_zero _
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Pi.smul_apply,
        smul_eq_mul, chartInv, Fin.succ_ne_zero, if_false]
      field_simp

theorem hermChartPot_swap (M : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hM : M.PosDef)
    (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    hermChartPot ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) y = hermChartPot M (chartInv y) + Real.log ‖y 0‖ := by
  set u : Fin (e + 1 + 1) → ℂ := Fin.cons 1 (chartInv y) with hu
  have hTv := swap_mulVec_cons y hy
  have hq : star (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) ⬝ᵥ
      (((swapFirstTwo e)ᴴ * M * swapFirstTwo e) *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ)) =
      (Complex.normSq (y 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (y 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr hy) (Real.sqrt_pos.mpr hx).ne']
  ring

theorem contDiff_gbPot {D : ℕ} : ContDiff ℝ 2 (gbPot (D := D)) := by
  have hs : ContDiff ℝ 2 fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

theorem contDiff_hermChartPot (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact (contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const

theorem contDiffAt_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 chartInv y := by
  have h0 : ContDiffAt ℂ 2 (fun y : Fin (e + 1) → ℂ => (y 0)⁻¹) y :=
    (contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.inv hy
  refine contDiffAt_pi.2 fun j => ?_
  by_cases hj : j = 0
  · subst hj
    simpa [chartInv] using h0
  · simpa [chartInv, hj] using h0.mul (contDiff_apply ℂ (fun _ => ℂ) j).contDiffAt

def logCoord (y : Fin (e + 1) → ℂ) (y' : Fin (e + 1) → ℂ) : ℂ :=
  Complex.log (y' 0 / y 0) + (Real.log ‖y 0‖ : ℂ)

theorem logCoord_re (y y' : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) (hy' : y' 0 ≠ 0) :
    (logCoord y y').re = Real.log ‖y' 0‖ := by
  rw [logCoord, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hy') (norm_ne_zero_iff.mpr hy)]
  ring

theorem contDiffAt_logCoord {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 (logCoord y) y := by
  have hmem : y 0 / y 0 ∈ Complex.slitPlane := by
    rw [div_self hy]
    exact Complex.one_mem_slitPlane
  exact ((Complex.contDiffAt_log hmem).comp y
    ((contDiff_apply ℂ (fun _ => ℂ) (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const

end ChartEnergySwapHessian


open ChartEnergySwapHessian ChartMongeAmpereAffineInvariance in
theorem ChartEnergySwapInvariant.proof : ChartEnergySwapInvariant.Statement := by
  intro e M N hM hN k
  set S := swapFirstTwo e with hS
  set U : Set (Fin (e + 1) → ℂ) := {y | y 0 ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun (continuous_apply 0) continuous_const
  have hUm : MeasurableSet U := hUo.measurableSet
  have hae : ∀ᵐ y ∂(volume : Measure (Fin (e + 1) → ℂ)), y ∈ U := by
    set K : Submodule ℝ (Fin (e + 1) → ℂ) :=
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (e + 1) => ℂ) 0) with hK
    have hKtop : K ≠ ⊤ := fun h => by
      have hm : (Pi.single 0 1 : Fin (e + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
      simp [hK] at hm
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin (e + 1) → ℂ)) K hKtop
    rw [ae_iff]
    convert h0 using 2
    ext y
    simp [hK, hU]
  set Φ : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ :=
    fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  set f : (Fin (e + 1) → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y ∈ U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
      maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) y = |(fderiv ℝ chartInv y).det| • f (chartInv y) := by
    intro y hy
    have hy : y 0 ≠ 0 := hy
    have hev : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0 := (continuous_apply 0).continuousAt.eventually_ne hy
    have hΦ' : ∀ j : Fin (e + 1), (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) j =ᶠ[𝓝 y] fun y' => Φ j (chartInv y') + (logCoord y y').re := by
      intro j
      filter_upwards [hev] with y' hy'
      rw [logCoord_re y y' hy hy']
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact hermChartPot_swap M hM y' hy'
      · simp only [hΦ, hj, if_false]
        exact hermChartPot_swap N hN y' hy'
    have hΦs : ∀ j, ContDiffAt ℝ 2 (Φ j) (chartInv y) := fun j => by
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact (contDiff_hermChartPot M hM).contDiffAt
      · simp only [hΦ, hj, if_false]
        exact (contDiff_hermChartPot N hN).contDiffAt
    rw [maDensity_comp_holo _ Φ chartInv (logCoord y) y hΦs (contDiffAt_chartInv hy)
      (contDiffAt_logCoord hy) hΦ', det_fderiv_real ((contDiffAt_chartInv hy).differentiableAt (by norm_num)),
      abs_of_nonneg (Complex.normSq_nonneg _), hermChartPot_swap M hM y hy, hermChartPot_swap N hN y hy, hf,
      smul_eq_mul]
    ring
  have hinj : Set.InjOn chartInv U := fun a ha b hb hab => by
    rw [← chartInv_chartInv (show a 0 ≠ 0 from ha), hab, chartInv_chartInv (show b 0 ≠ 0 from hb)]
  have himage : chartInv '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show chartInv x 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hx
    · intro hy
      refine ⟨chartInv y, ?_, chartInv_chartInv hy⟩
      show chartInv y 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hy
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt chartInv (fderiv ℝ chartInv y) U y := fun y hy =>
    (((contDiffAt_chartInv (show y 0 ≠ 0 from hy)).restrict_scalars ℝ).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  unfold chartMixedEnergy
  calc ∫ y, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y
      = ∫ y in U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∫ y in U, |(fderiv ℝ chartInv y).det| • f (chartInv y) := setIntegral_congr_fun hUm hpt
    _ = ∫ y in chartInv '' U, f y :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f).symm
    _ = ∫ y in U, f y := by rw [himage]
    _ = ∫ y, f y := by rw [Measure.restrict_eq_self_of_ae_mem hae]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexDet

theorem span_basis_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsFullLattice ℚ (Submodule.span ℤ (Set.range b)) := by
  have : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) :=
    Submodule.IsLattice.of_fg ℚ (Submodule.fg_span (Set.finite_range b))
  refine { span_eq_top := ?_ }
  rw [Submodule.span_span_of_tower ℤ, b.span_eq]

end KLinesGenIndexDet


open KLinesGenIndexDet in
theorem LinesGenIndexDet.proof (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have : Submodule.IsFullLattice ℚ MA := span_basis_isLattice bA
  have : Submodule.IsFullLattice ℚ MB := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB)
    (Submodule.IsFullLattice.inf ℚ MA MB)
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

theorem toAddSubgroup_span {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s

end KLinesGenIndexTrans


open KLinesGenIndexTrans in
theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hBC := h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hAC := h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

namespace KLinesIdealLatticeFG

theorem idealLattice_eq_iSup (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice a = ⨆ x, Submodule.map (LinearMap.single (𝓞 K) (fun _ : Fin n => K) x)
      (a x : Submodule (𝓞 K) K) :=
  (Submodule.iSup_map_single).symm

theorem fg (K : Type) [Field K] [NumberField K] {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    (idealLattice a).FG := by
  rw [idealLattice_eq_iSup]
  exact Submodule.fg_iSup _ fun x =>
    ((a x).fg_of_isNoetherianRing le_rfl).map _

theorem single_mem_span (K : Type) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) (hx : a x ≠ 0) :
    (Pi.single x 1 : Fin n → K) ∈ Submodule.span K (idealLattice a : Set (Fin n → K)) := by
  have hbot : (a x : Submodule (𝓞 K) K) ≠ ⊥ := by
    rwa [Ne, FractionalIdeal.coeToSubmodule_eq_bot]
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hmem : (Pi.single x y : Fin n → K) ∈ idealLattice a := by
    rw [idealLattice, Submodule.mem_pi]
    intro i _
    by_cases h : i = x
    · subst h; simpa using hy
    · simp [h]
  have heq : (Pi.single x 1 : Fin n → K) = y⁻¹ • (Pi.single x y : Fin n → K) := by
    ext i
    by_cases h : i = x
    · subst h; simp [hy0]
    · simp [h]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end KLinesIdealLatticeFG


open KLinesIdealLatticeFG in
theorem LinesIdealLatticeFG.proof : LinesIdealLatticeFG.Statement := by
  intro K _ _ n a ha
  refine ⟨fg K a, ?_⟩
  refine eq_top_iff.mpr ?_
  rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_span K a x (ha x)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

namespace KLinesIsLattice

theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))

theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx

def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv

end KLinesIsLattice

theorem LinesIsLattice.proof : LinesIsLattice.Statement := by
  intro K _ _ ι _ M hfg hspan
  letI : Submodule.IsLattice ℚ (M.restrictScalars ℤ) := Submodule.IsLattice.of_fg ℚ hfg
  have htop : Submodule.span ℚ (M : Set (ι → K)) = ⊤ := by
    have hMN : Submodule.span K (M : Set (ι → K)) ≤ KLinesIsLattice.qSpan M :=
      Submodule.span_le.mpr fun v hv => Submodule.subset_span hv
    rw [hspan, top_le_iff] at hMN
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ KLinesIsLattice.qSpan M := hMN ▸ Submodule.mem_top
    exact hv
  letI : Submodule.IsFullLattice ℚ (M.restrictScalars ℤ) := ⟨htop⟩
  exact inferInstance
end GroundTheory.Heights₂.Heights
end

