module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.SMulVec

@[expose] public section

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section locb

variable {k r : ℕ}

def omS (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' ((Hpk k r * gᴴ * Hpk k r) *ᵥ xcofL k r z z' g)

lemma inv_uh {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hL : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hH_sq]
  exact Matrix.inv_eq_left_inv hL

lemma omS_eq (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' g = omS k r z z' g := by
  rw [omW', omS, inv_uh hg]

lemma s_omS (z z' : Fin (2 * r + k + 1) → ℂ) {s : Set (B.Mat k r)} : Sm (fun g => omS k r z z' g) s := by
  unfold omS
  have h1 : Sm (fun g : B.Mat k r => Hpk k r * gᴴ * Hpk k r) s :=
    s_mmul (s_mmul contDiffOn_const (s_ct contDiffOn_id)) contDiffOn_const
  exact s_prW z' (s_mulVec h1 (s_xcofL z z' contDiffOn_id))

end locb

end PI.UnitaryGroupMassFormula.GsFr
