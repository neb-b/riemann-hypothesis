module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWittBasisCompactStabiliser
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.TowU
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section

namespace GlobalTheory.WeilEx.Jac

section Alg

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] {α β ν X : Type} [Fintype β] [DecidableEq β]
  [AddCommGroup X] [Module R X] {e : ν ⊕ ν ≃ α}


variable [Invertible (2 : R)] {D : Matrix α β A ≃ₗ[R] X × X}
  (hΔ : ∀ w, GlobalTheory.SWLit.LinAct.Del e w → (D w).1 = 0)
  (hN : ∀ w, GlobalTheory.SWLit.LinAct.Nab e w → (D w).2 = 0)
include hΔ hN

end Alg

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_det_unitary {k : ℕ} {J : Matrix (Fin k) (Fin k) E} (hJ : J.det ≠ 0) (g : UA σ J) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E))) = 1 := by
  set d := Matrix.GeneralLinearGroup.det (g : GL (Fin k) (AE F E)) with hd
  have hJu : IsUnit (incM F J).det := by
    have e0 : (incM F J).det = inclR (F := F) (AF F) J.det := (RingHom.map_det _ _).symm
    rw [e0]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have h := congrArg Matrix.det (show ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E))ᵀ * incM F J *
    ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ) = incM F J from g.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show (((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin k) (AE F E)) : Matrix (Fin k) (Fin k) (AE F E)).det from
      ((cA σ).toRingHom.map_det _).symm] at h
  have h2 : (d : AE F E) * cA σ d = 1 := by
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply]
    exact hJu.mul_left_cancel (by linear_combination h)
  have hc : Units.map (cA σ : AE F E →* AE F E) d = conjUnit σ d := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rfl
  have h3 : d * Units.map (cA σ : AE F E →* AE F E) d = 1 := Units.ext (by simpa using h2)
  have h4 : absE F E d * absE F E d = 1 := by
    nth_rewrite 2 [← absE_conjUnit σ d]
    rw [← hc, ← map_mul, h3, map_one]
  apply NNReal.coe_injective
  have h6 : (absE F E d : ℝ) * absE F E d = 1 := by exact_mod_cast h4
  have h7 : (0 : ℝ) ≤ absE F E d := (absE F E d).2
  push_cast
  exact le_antisymm (by nlinarith) (by nlinarith)

end Main

end GlobalTheory.WeilEx.Jac
