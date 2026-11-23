module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private lemma ne_of_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

private lemma glue (F G : ℂ → ℂ) (hF : ∀ s : ℂ, 1 / 4 < s.re → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, s.re < 3 / 4 → DifferentiableAt ℂ G s)
    (h : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → F s = G s) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 / 4 < s.re → Z s = F s) ∧ ∀ s : ℂ, s.re < 3 / 4 → Z s = G s := by
  have a : ∀ s : ℂ, 1 / 4 < s.re → (if 1 / 4 < s.re then F s else G s) = F s := fun s hs => if_pos hs
  have b : ∀ s : ℂ, s.re < 3 / 4 → (if 1 / 4 < s.re then F s else G s) = G s := fun s hs => by
    split_ifs with h'
    · exact h s h' hs
    · rfl
  refine ⟨fun s => if 1 / 4 < s.re then F s else G s, fun s => ?_, a, b⟩
  by_cases hs : 1 / 4 < s.re
  · refine (hF s hs).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz using a z hz
  · have hs' : s.re < 3 / 4 := by linarith [not_lt.mp hs]
    refine (hG s hs').congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs'] with z hz using b z hz
