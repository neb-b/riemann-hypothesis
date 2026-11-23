module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0003
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.GenericFramesLetters
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PointsPropertyOfD7
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0002
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfDifferent
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Formalism.SharpRestriction.GlobalSchurBounds.JointsL

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
section
namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions

theorem field_lemmas_two_to_six (D : D7) (sc : Scale) :
    Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc :=
  ⟨second_proposition_every_localisation D, points_property_of_d7 D, generic_frames_letters D, no_three_consecutive_thick_places D, branching_interlacing_pairs D sc⟩

theorem field_lemmas_except_seven : ∃ C₅ : ℝ, ∀ (D : D7) (sc : Scale),
    Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D 100 ∧ Conclusion5 D C₅ ∧ TorusPairsWithVariant D ∧ Conclusion6 D sc ∧ Conclusion8 D := by
  obtain ⟨C, hC⟩ := dropping_proposition_holds
  refine ⟨C, fun D sc => ?_⟩
  obtain ⟨h2, h3, h4, h5c, h6⟩ := field_lemmas_two_to_six D sc
  exact ⟨ramification_two_and_conjugation_at_q_and_d D, h2, h3, h4, hC D, h5c, h6, lemma_one_eight_holds D⟩

end Formalism.MainNotions.UnusedSlot33
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SlopesMFOfCountFam
section
noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

theorem numsL_of_fam_thr {eps : ℝ} (Fm : FamP eps) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      JSL.NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ JSL.WtsL (Fm.D x i) (Fm.L x i) Cn := by
  obtain ⟨C, x0, -, hx⟩ := hC
  exact nums_wts_of_fam Fm ⟨C, x0, fun x hx' i u => (hx x hx' i u).2.1⟩ hDl

theorem numsL_of_fam {eps : ℝ} (Fm : FamP eps) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn cL x0 : ℝ, 0 ≤ cL ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
      JSL.NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ JSL.WtsL (Fm.D x i) (Fm.L x i) Cn := by
  obtain ⟨Cn₀, h⟩ := numsL_of_fam_thr Fm hC hDl
  obtain ⟨x0, hx⟩ := h Cn₀ le_rfl 3 le_rfl
  exact ⟨Cn₀, 3, x0, by norm_num, hx⟩

theorem slopesMF_of_count_fam {eps : ℝ} (Fm : FamP eps) (h5 : ConclusionF5 Fm) (h6 : ConclusionF6 Fm) (hC : Lnk.CountF Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps)
    (hCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (ColVal (Fm.D x i) u)) : Lnk.SlopesMF Fm := by
  obtain ⟨Cn, cL, x0, hcL, hx⟩ := numsL_of_fam Fm hC hDl
  obtain ⟨x1, hx1⟩ := hCV
  refine slopesMF_of_count Fm Cn cL hcL h5 h6 ⟨max x0 x1, fun x hx' i => ?_⟩ hC
  have h0 := hx x (le_of_max_le_left hx') i
  exact ⟨h0.1, h0.2, hx1 x (le_of_max_le_right hx') i⟩

end Formalism.MainNotions.flipTwoThree

end
end

