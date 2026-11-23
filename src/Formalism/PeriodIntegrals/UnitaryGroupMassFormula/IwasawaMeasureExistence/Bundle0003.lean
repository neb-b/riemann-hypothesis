module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0021
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Formalism.LogSumExpBounds.StatementD
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Mathlib
public import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
public import Formalism.GelfandTransference.Bundle0001
public import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Formalism.LatticeRigidity.StatementC
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.DetNorm
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.IwasawaVolumeBoundOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviSizesMeasurable
section
noncomputable section

namespace PI.IwaMeasEx.Nrm

open Matrix NumberField Topology Filter MeasureTheory Formalism.MainNotions.S
  Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.GLOne
open scoped TensorProduct nonZeroDivisors

section Top

variable (I : AutInst)

attribute [local instance] AfT.tAf

theorem topRing : IsTopologicalRing (AEf I) := AfT.isTopologicalRing_tAf I

theorem t2 : T2Space (AEf I) := AfT.t2Space_finite_adeles_ext I

attribute [local instance] topRing t2

def mAf : MeasurableSpace (AEf I) := borel (AEf I)

attribute [local instance] mAf

theorem borel_mAf : BorelSpace (AEf I) := ⟨rfl⟩

attribute [local instance] borel_mAf

theorem isOpen_IntAf : IsOpen ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [(AfT.hasBasis_nhds_tAf I x).mem_iff]
  refine ⟨0, trivial, fun y hy => ?_⟩
  change y - x ∈ AfT.bsub I (0 + 1) at hy
  obtain ⟨z, hz, he⟩ := (AfT.mem_bsub I).1 hy
  have e : y = x + (y - x) := by ring
  show y ∈ IntAf I.F I.E
  rw [e, ← he]
  exact add_mem hx (mul_mem (natCast_mem _ _) hz)

theorem continuous_inclR :
    Continuous (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F) : Af I.F → AEf I) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero]
  refine (AfT.hasBasis_nhds_zero_tAf I).tendsto_right_iff.2 fun k _ => ?_
  have hk : ((k + 1 : ℕ) : I.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  have hU : IsOpen {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} :=
    Wau.isOpen_Ohat.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : Af I.F) ∈ {a : Af I.F | algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a ∈ Wau.Ohat I.F} := by
    show _ * 0 ∈ Wau.Ohat I.F
    rw [mul_zero]
    exact Wau.ohat_zero
  filter_upwards [hU.mem_nhds h0] with a ha
  show Algebra.TensorProduct.includeRight a ∈ AfT.bsub I (k + 1)
  refine (AfT.mem_bsub I).2 ⟨Algebra.TensorProduct.includeRight
    (algebraMap I.F (Af I.F) (((k + 1 : ℕ) : I.F)⁻¹) * a), AfT.includeRight_mem_IntAf I ha, ?_⟩
  rw [← map_natCast (Algebra.TensorProduct.includeRight (R := I.F) (A := I.E) (B := Af I.F)), ← map_mul, ← mul_assoc,
    ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, mul_inv_cancel₀ hk, map_one, one_mul]

theorem continuous_embC {ι : Type} [Fintype ι] (b : Module.Basis ι I.F I.E) :
    Continuous (fun c : ι → Af I.F => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) := by
  refine continuous_finsetSum _ fun j _ => ?_
  have e : (fun c : ι → Af I.F => (b j ⊗ₜ[I.F] c j : AEf I)) =
      fun c => iE I (b j) * Algebra.TensorProduct.includeRight (c j) := by
    funext c
    show b j ⊗ₜ[I.F] c j = (b j ⊗ₜ[I.F] (1 : Af I.F)) * ((1 : I.E) ⊗ₜ[I.F] c j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact continuous_const.mul ((continuous_inclR I).comp (continuous_apply j))

theorem isCompact_IntAf : IsCompact ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) := by
  let b := Module.finBasis I.F I.E
  obtain ⟨D, hD, hDb⟩ := AfT.exists_denom I b
  have hK : IsCompact ((fun c => (∑ j, b j ⊗ₜ[I.F] c j : AEf I)) '' Set.univ.pi fun _ => Wau.Cpt.Bx I D) :=
    (isCompact_univ_pi fun _ => Wau.Cpt.isCompact_Bx I D).image (continuous_embC I b)
  have hcl : IsClosed ((IntAf I.F I.E : Subring (AEf I)) : Set (AEf I)) :=
    AddSubgroup.isClosed_of_isOpen (IntAf I.F I.E).toAddSubgroup (isOpen_IntAf I)
  refine hK.of_isClosed_subset hcl fun x hx => ?_
  refine ⟨fun j => AfT.crd I b j x, fun j _ => Wau.Cpt.mem_Bx I (by omega) ?_, (AfT.sum_crd I b x).symm⟩
  rw [nsmul_eq_mul]
  exact AfT.crd_mem I b hDb (AfT.IntAf_le_sumsInt I hx) j


end Top

attribute [local instance] AfT.tAf topRing t2 mAf borel_mAf

end PI.IwaMeasEx.Nrm

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.NormExpSubOneSubLe
section
noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open Filter Topology Formalism.MainNotions.S

section Trotter

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [NormOneClass 𝔸]

theorem norm_exp_sub_partial_le (x : 𝔸) (m : ℕ) :
    ‖NormedSpace.exp x - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) • x ^ i‖ ≤
      Real.exp ‖x‖ - ∑ i ∈ Finset.range m, ((i.factorial : ℝ)⁻¹) * ‖x‖ ^ i := by
  have h1 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • x ^ i) (NormedSpace.exp x) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have h2 : HasSum (fun i : ℕ => ((i.factorial : ℝ)⁻¹) • ‖x‖ ^ i) (Real.exp ‖x‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖
  have h1' := (hasSum_nat_add_iff' m).mpr h1
  have h2' := (hasSum_nat_add_iff' m).mpr h2
  simp only [smul_eq_mul] at h2'
  refine h1'.norm_le_of_bounded h2' (fun i => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_le x _) (by positivity)

theorem norm_exp_le' (x : 𝔸) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  simpa using norm_exp_sub_partial_le x 0

end Trotter

section Mat

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end Mat

end PI.IwaMeasEx.Gauge.ZetaZeros

end
end

