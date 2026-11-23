module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA

@[expose] public section

noncomputable section

namespace PI.OmFibreUniq.W.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.VolStabSW PI.VolStabSW.SdUniqW PI.AdicCompletionValuation
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (a : ℕ)

theorem sigR_algebraMap (c : R) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R _ c := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

theorem smul_mem_HermR (c : R) (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)) (hS : S ∈ HermR R σ a) :
    c • S ∈ HermR R σ a := by
  intro i j
  have h := hS i j
  simp only [Matrix.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, h, sigR_algebraMap]

instance hermSMul : SMul R (HermR R σ a) :=
  ⟨fun c S => ⟨c • (S : Matrix (Fin a) (Fin a) (R ⊗[F] E)), smul_mem_HermR R σ a c S S.2⟩⟩

instance hermContSMul [TopologicalSpace R] [IsTopologicalRing R] :
    ContinuousSMul R (HermR R σ a) :=
  ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩

instance hermSC [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    [FiniteDimensional F E] : SecondCountableTopology (HermR R σ a) := by
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → R ⊗[F] E))
  exact TopologicalSpace.Subtype.secondCountableTopology _

end HermMod

def PsiNT : Prop :=
  ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)),
    IsCharAF F ψ → IsStdChar ψ → NumberField.IsTotallyReal F → ∃ y, psiV F ψ v y ≠ 1

end PI.OmFibreUniq.W.Sd
