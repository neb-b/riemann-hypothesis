module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.UniformContinuousConstSMulOfIsIsometricSMul

@[expose] public section

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

variable (p : ℕ) [Fact p.Prime]
variable {C : Type u} [NormedField C] [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)]
variable (O : ValuationSubring C) [IsUnitBall O]

namespace BdRPlus

def thetaC : BdRPlus p O →+* C :=
  (IsUnitBall.awayEquiv O p).toRingEquiv.toRingHom.comp (theta p O)

variable {p O}

theorem thetaC_apply (x : BdRPlus p O) :
    thetaC p O x = IsUnitBall.awayEquiv O p (theta p O x) := rfl

@[simp] theorem thetaC_algebraMap (x : Ainf p O) :
    thetaC p O (algebraMap _ _ x) = (Ainf.theta p O x : C) := by
  rw [thetaC_apply, IsScalarTower.algebraMap_apply (Ainf p O) (AinfInv p O), theta_algebraMap,
    AinfInv.theta_algebraMap, IsUnitBall.awayEquiv_algebraMap]

theorem ker_thetaC : RingHom.ker (thetaC p O) = RingHom.ker (theta p O) := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, thetaC_apply,
    map_eq_zero_iff _ (IsUnitBall.awayEquiv O p).injective]

variable [IsAlgClosed C]

section General

variable {F : Type v} {L : Type w} [Field F] [Field L] [Algebra F L] [CharZero F]
  [Algebra.IsAlgebraic F L]

end General

end BdRPlus

section Padic

variable [NormedAlgebra ℚ_[p] C]



variable [IsAlgClosed C] {L : Type w} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]

variable {p O}

end Padic

section Witt

variable [IsAlgClosed C] {k : Type v} [Field k] [CharP k p] [PerfectRing k p]
variable {L : Type w} [Field L] [Algebra (FractionRing (WittVector p k)) L]
  [Algebra.IsAlgebraic (FractionRing (WittVector p k)) L]

omit [CompleteSpace C] [CharZero C] [Fact (‖(p : C)‖ < 1)] [IsUnitBall O] [IsAlgClosed C] in
theorem charZero_wittVector : CharZero (WittVector p k) := by
  refine ⟨fun m n h => ?_⟩
  have hinj : Function.Injective ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom) :=
    (WittVector.map_injective _ (RingHom.injective _)).comp (WittVector.equiv p).symm.injective
  exact Nat.cast_injective (R := ℤ_[p]) (hinj (by rw [map_natCast, map_natCast, h]))

instance : CharZero (FractionRing (WittVector p k)) :=
  haveI := charZero_wittVector p (k := k)
  inferInstance

variable {p O}

end Witt

end Reformulated.AutPerF
