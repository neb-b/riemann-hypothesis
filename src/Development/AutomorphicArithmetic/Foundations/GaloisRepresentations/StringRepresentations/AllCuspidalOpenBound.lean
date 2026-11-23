module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne

@[expose] public section

noncomputable section

namespace UpperTheory.GalN

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def OpenB (q : ℕ) (α : ℂ) : Prop := (q : ℝ) ^ (-(1 / 2) : ℝ) < ‖α‖ ∧ ‖α‖ < (q : ℝ) ^ (1 / 2 : ℝ)

theorem OpenB.of_mul {q : ℕ} {α e : ℂ} (h : OpenB q (α * e)) (he : ‖e‖ = 1) : OpenB q α := by
  rwa [OpenB, norm_mul, he, mul_one] at h

def TempAt {a : ℕ} (π : A.CG a) (w : PlE H) : Prop :=
  (a = 1 → A.tempered (A.locG π w)) ∧ (A.unr (A.locG π w) → ∀ α ∈ A.frobEig (A.locG π w), OpenB (normV w) α)

def AllCuspidalOpenBound : Prop := ∀ (a : ℕ) (π : A.CG a), 1 ≤ a → A.csd π → A.ralg π → ∀ w, TempAt N A π w

variable {N A}

theorem tempo' {D : D7} (h : AllCuspidalOpenBound D.nd D.naut) : AllCuspidalOpenBound D.nd D.naut := h

end UpperTheory.GalN
