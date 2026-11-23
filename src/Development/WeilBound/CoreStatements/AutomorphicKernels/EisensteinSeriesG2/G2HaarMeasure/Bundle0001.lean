module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import GroundTheory.GlobalFields.Adele.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.EisBL.DoubledParabolic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}

theorem incM_mul_inv (b : GL (Fin n ⊕ Fin n) E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  unfold incM
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem incM_inv_mul (b : GL (Fin n ⊕ Fin n) E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  unfold incM
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_mul (b : GL (Fin n ⊕ Fin n) E) (x y : G2 σ Y) : inFrame b (x * y) = inFrame b x * inFrame b y := by
  unfold inFrame
  show incM F (b⁻¹).1 * (mat2 x * mat2 y) * incM F b.1 =
    incM F (b⁻¹).1 * mat2 x * incM F b.1 * (incM F (b⁻¹).1 * mat2 y * incM F b.1)
  calc incM F (b⁻¹).1 * (mat2 x * mat2 y) * incM F b.1
      = incM F (b⁻¹).1 * mat2 x * (incM F b.1 * incM F (b⁻¹).1) * mat2 y * incM F b.1 := by
        rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inFrame_one (b : GL (Fin n ⊕ Fin n) E) : inFrame b (1 : G2 σ Y) = 1 := by
  unfold inFrame
  show incM F (b⁻¹).1 * 1 * incM F b.1 = 1
  rw [Matrix.mul_one, incM_inv_mul]

theorem inFrame_inv_mul (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x⁻¹ * inFrame b x = 1 := by
  rw [← inFrame_mul, inv_mul_cancel, inFrame_one]

theorem inFrame_inv (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : inFrame b x⁻¹ = (inFrame b x)⁻¹ :=
  (Matrix.inv_eq_left_inv (inFrame_inv_mul b x)).symm

theorem continuous_inFrame (b : GL (Fin n ⊕ Fin n) E) : Continuous (inFrame (σ := σ) (Y := Y) b) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : G2 σ Y => mat2 g := Units.continuous_val.comp continuous_subtype_val
  exact (continuous_const.matrix_mul hm).matrix_mul continuous_const


end GlobalTheory.EisBL.DoubledParabolic
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.UnipotentLeDiagonalStabiliser
section
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.EisBL.DoubledUnipotentRadical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]







omit [NumberField E] in
theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

omit [NumberField E] in
theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
      (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end GlobalTheory.EisBL.DoubledUnipotentRadical
end
end

