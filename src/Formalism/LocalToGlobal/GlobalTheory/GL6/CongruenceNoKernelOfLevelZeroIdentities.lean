module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0009
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

section UnramifiedDiagonal

variable (D : D7) (u : D.what₂.Word)

def DiamondCommutesLevelZero : Prop :=
  ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi 0,
    dia D u 0 v' a (Uop D u 0 v φ) = Uop D u 0 v (dia D u 0 v' a φ) ∧
    dia D u 0 v' a (Dop D u 0 v φ) = Dop D u 0 v (dia D u 0 v' a φ)

def TraceDiamondInvariantLevelZero : Prop :=
  ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi 0, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v φ

def DUFormulaLevelZero : Prop :=
  ∀ v, ∀ φ ∈ (D.fm u).Fi 0, Dop D u 0 v (Uop D u 0 v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • Nm D u 0 v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N 0 - 2) • trp D u 0 v φ

variable {D u}

theorem norm_commutes_hecke_level_zero (hc : DiamondCommutesLevelZero D u) (v v' : (D.mem u).A.vT) (φ : Fn D u 0) (hφ : φ ∈ (D.fm u).Fi 0) :
    Nm D u 0 v' (Uop D u 0 v φ) = Uop D u 0 v (Nm D u 0 v' φ) ∧
    Nm D u 0 v' (Dop D u 0 v φ) = Dop D u 0 v (Nm D u 0 v' φ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [norm_eq_sum_diamond, map_sum]
  exact ⟨Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).1, Finset.sum_congr rfl fun a _ => (hc v v' a φ hφ).2⟩

theorem trace_zero_of_norm_zero_level_zero (ht : TraceDiamondInvariantLevelZero D u) (v : (D.mem u).A.vT) (φ : Fn D u 0)
    (hφ : φ ∈ (D.fm u).Fi 0) (hN : Nm D u 0 v φ = 0) : trp D u 0 v φ = 0 := by
  have h1 : ∑ a : ((D.mem u).A.Fv v)ˣ, trp D u 0 v (dia D u 0 v a φ) = trp D u 0 v (Nm D u 0 v φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [norm_eq_sum_diamond, map_sum]
  rw [hN, map_zero, Finset.sum_congr rfl (fun a _ => ht v a φ hφ), Finset.sum_const,
    Finset.card_univ] at h1
  have hc : (Fintype.card ((D.mem u).A.Fv v)ˣ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

end UnramifiedDiagonal

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
