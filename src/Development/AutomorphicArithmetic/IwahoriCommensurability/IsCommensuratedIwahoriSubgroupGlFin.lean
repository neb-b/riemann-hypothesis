module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
public import Development.AutomorphicArithmetic.IwahoriCommensurability.Bundle0001

@[expose] public section

open Formalism.UG

theorem UpperTheory.isCommensurated_iwahoriSubgroup_gl_fin :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Formalism.UG.IsCommensurated (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n
  have h : GlobalTheory.SmGL.iwahori k (Fin n) =
      GroundTheory.Automorphic.GLnLocal.iwahori k n := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel] at hu
      refine ⟨u, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff]
        intro i j hij
        rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply]
        exact hu i j hij
      · ext i j
        rfl
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, GroundTheory.Automorphic.mem_borel_iff] at hu
      refine ⟨u, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, GlobalTheory.SmGL.mem_borel]
        intro i j hij
        have h := hu i j hij
        rw [GroundTheory.Automorphic.GLnLocal.residueReduction_apply] at h
        exact h
      · ext i j
        rfl
  rw [h]
  exact UpperTheory.isCommensurated_iwahori_gl k n
