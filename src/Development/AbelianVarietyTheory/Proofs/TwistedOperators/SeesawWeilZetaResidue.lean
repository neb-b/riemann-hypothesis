module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.Transport

theorem exists_factor {V Q P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup P] [Module ℂ P] (T : V →ₗ[ℂ] Q) (S : Submodule ℂ V) (hT : ∀ Φ ∈ S, T Φ = 0 → Φ = 0)
    (pD : V →ₗ[ℂ] P) : ∃ q : Q →ₗ[ℂ] P, ∀ Ψ ∈ S, q (T Ψ) = pD Ψ := by
  have hinj : Function.Injective (T ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hT x.1 x.2 hx)
  let eq := LinearEquiv.ofInjective (T ∘ₗ S.subtype) hinj
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((pD ∘ₗ S.subtype) ∘ₗ eq.symm.toLinearMap)
  refine ⟨g, fun Ψ hΨ => ?_⟩
  have h1 : g (T Ψ) = (g ∘ₗ (LinearMap.range (T ∘ₗ S.subtype)).subtype) (eq ⟨Ψ, hΨ⟩) := rfl
  rw [h1, hg]
  simp

end GlobalTheory.TripleAssembly.Transport

