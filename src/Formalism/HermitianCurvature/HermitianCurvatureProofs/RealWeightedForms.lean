module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0024

@[expose] public section

namespace Formalism.FourierDecayAlt.P.RealWeightedForms

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix

theorem qwOfReal : QwOfReal := by
  intro S _ _ q w Y hq hw
  induction w with
  | nil =>
    simp only [qw, List.map_nil]
    exact Complex.ext (by simp) (by simpa using hq)
  | cons l w ih =>
    have him := hw l (List.mem_cons_self ..)
    have ih' := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨plus, intersection_update_fsHerm_neg_one, pt⟩ := l
    obtain ⟨p, rfl⟩ : ∃ p : ℝ, pt = p := ⟨pt.re, Complex.ext (by simp) (by simpa using him)⟩
    cases plus <;> simp [qw, ih']

section admitted

variable {S : Type}

end admitted

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

end Rep

end Formalism.FourierDecayAlt.P.RealWeightedForms

theorem Formalism.FourierDecayAlt.P.weighted_quadratic_of_real : Formalism.FourierDecayAlt.FormPairingAction.QwOfReal := Formalism.FourierDecayAlt.P.RealWeightedForms.qwOfReal
