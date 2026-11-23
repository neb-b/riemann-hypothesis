module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace

variable (D : D7) (u : D.what₂.Word)

def d0 : ℕ := Module.finrank ℂ (D.s.Cu u)

def hsDev : ℝ := hsNormSq (Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u))

def DiagS (e : ℝ) : Prop := hsDev D u ≤ e * (d0 D u : ℝ)

def SAbs (Γ₀ : ℝ) : Prop := hsDev D u ≤ Γ₀ * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + (d0 D u : ℝ) / 4

abbrev Desc : Type := (D.mem u).P.Mt →ₗ⋆[ℂ] D.s.HH

def MIMap (Θ : Desc D u) : Prop :=
  ∃ (s l : ℂ) (FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u), l ≠ 0 ∧ Function.Injective FF ∧
    ∀ (φ : (D.mem u).A.Mram) (F : (D.mem u).P.Mt),
      s * PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ F = l * ⟪Θ F, D.s.Pu u (FF φ)⟫_ℂ

def OntoAll (Θ : Desc D u) : Prop := Function.Surjective Θ

def RamShare : Prop :=
  (dU D u : ℝ) = (d0 D u : ℝ) * (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f

def RamBig (δ : ℝ) : Prop := 0 < dU D u ∧ (1 - δ) * (d0 D u : ℝ) ≤ (dU D u : ℝ)

theorem d0_eq : d0 D u = D.duS u := (D.s_Cu u).finrank_eq

end GlobalTheory.Core.Rk

end
