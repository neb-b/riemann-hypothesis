module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007

@[expose] public section

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  show (Algebra.TensorProduct.map (AlgHom.id F R) σ) (algebraMap R (R ⊗[F] E) t) =
    algebraMap R (R ⊗[F] E) t
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    map_one]

theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

end PI.VolStabSW
