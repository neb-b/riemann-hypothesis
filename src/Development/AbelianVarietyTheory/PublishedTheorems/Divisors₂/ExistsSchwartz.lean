module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula GlobalTheory.SiegelFormula.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published.ThetaConvModel

variable {D : D7}

theorem exists_schwartz (θ : InfFam D) (m n : ℕ) : ∃ Φ : schwartzA θ m n, Φ.1 0 ≠ 0 := by
  classical
  let b : ContDiffBump (0 : D.what₂.Tau → Fin m → Fin n → ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hb1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb2 : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := hb1.toSchwartzMap hb2
  have hf : f 0 = 1 := by
    show ((b 0 : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]; simp
  let W : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    { carrier := {a | ∀ i j, a i j ∈ Formalism.L2.Theta.intAE D}
      add_mem' := fun ha hb i j => (Formalism.L2.Theta.intAE D).add_mem (ha i j) (hb i j)
      zero_mem' := fun _ _ => (Formalism.L2.Theta.intAE D).zero_mem
      neg_mem' := fun ha i j => (Formalism.L2.Theta.intAE D).neg_mem (ha i j) }
  have hWe : (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (Formalism.L2.Theta.intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (W : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  let g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
    if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ W) = 0 then (1 : ℂ) else 0
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    GlobalTheory.SchwartzBruhatTensor.coset_mem_SB W hWo hWc 0
  let φ : Mx D m n → ℂ := fun x =>
    f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
  have hφ : φ ∈ schwartzA θ m n := Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show f _ * g _ ≠ 0
  have e : (fun τ i j => compAt θ τ (0 : Mx D m n) i j : D.what₂.Tau → Fin m → Fin n → ℂ) = 0 := by
    ext τ i j; simp [compAt]
  rw [e, hf]
  simp [g]
  exact (QuotientAddGroup.eq_zero_iff (N := W) (0 : Matrix (Fin m) (Fin n) _)).2 W.zero_mem

end GlobalTheory.Published.ThetaConvModel

end
