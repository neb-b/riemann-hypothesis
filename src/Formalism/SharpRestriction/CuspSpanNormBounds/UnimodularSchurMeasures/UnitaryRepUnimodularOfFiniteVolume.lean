module

public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0003
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrdStronglyMeasurable

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set Topology
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

theorem adelic_regular_rep_unitary_continuous (X : CData) (hd : RegData X) (hu : UnimodA X) (hl : LocFinF X) : RepA X := by
  have hH : X.μf.IsHaarMeasure := hd.1
  have : SecondCountableTopology X.I.Gf := rr_secondCountable X.I X.μf
  have : SecondCountableTopology X.L2 := automorphic_L2_secondCountable X
  have : (X.I.muA X.μf).IsMulLeftInvariant := rr_muA_left X.I X.μf
  have : SigmaFinite (X.I.muA X.μf) := rr_muA_sigmaFinite X.I X.μf
  have : IsLocallyFiniteMeasure (X.I.muA X.μf) := rr_muA_locFin X hl
  have : (X.I.muA X.μf).IsOpenPosMeasure := rr_muA_openPos X
  have hne : X.I.muA X.μf ≠ 0 := fun h0 =>
    isOpen_univ.measure_ne_zero (X.I.muA X.μf) (univ_nonempty (α := X.I.GA))
      (by rw [h0, FunLike.coe_zero, Pi.zero_apply])
  obtain ⟨h1, h2, h3⟩ := rightRegular_isometric_multiplicative X hd hu
  exact ⟨h1, h2, h3, fun F => rr_cont_of_meas' (μ := X.I.muA X.μf) hne h1 h2 h3 (regular_rep_coeff_measurable X hd hu) F⟩

end Formalism.MainNotions.LeviCoordinates

end
