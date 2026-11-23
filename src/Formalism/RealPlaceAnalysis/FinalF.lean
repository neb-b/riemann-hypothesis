module

public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SatisfiesGlRelationsBilinearLeft
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005

@[expose] public section

namespace Formalism.REAL
theorem expUJ : ExpUJ := exp_indefinite_unitary_holds
theorem uJInv : UJInv := indefinite_unitary_inv_closed
theorem oneParam : OneParam := one_parameter_subgroup_holds
theorem kFacts : KFacts := maximal_compact_facts
theorem pChar : PChar := parabolic_character_holds
theorem polar : Polar := polar_decomposition_holds
theorem hSBall : HSBall := hermitian_small_ball
theorem ballOpen : BallOpen := ball_open_holds
theorem uJEmb : UJEmb := isClosedEmbeddingMatrix
theorem unimodular : Unimodular := indefinite_unitary_unimodular
theorem invInvariant : InvInvariant := by
  intro n ε
  have hR := indefinite_unitary_unimodular n ε
  haveI : (muG ε).IsMulRightInvariant := ⟨hR⟩
  show (muG ε).inv = muG ε
  have key : (muG ε).inv =
      MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) • muG ε := by
    exact MeasureTheory.Measure.isMulLeftInvariant_eq_smul _ _
  generalize MeasureTheory.Measure.haarScalarFactor (muG ε).inv (muG ε) = c at key
  have h2 : muG ε = (c * c) • muG ε := by
    calc muG ε = (muG ε).inv.inv := (MeasureTheory.Measure.inv_inv _).symm
      _ = (c • muG ε).inv := by rw [← key]
      _ = c • (muG ε).inv := MeasureTheory.Measure.map_smul _ measurable_inv.aemeasurable
      _ = (c * c) • muG ε := by rw [key, smul_smul]
  have hc1 : c = 1 := by
    obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : ↥(UJ ε))
    have hpos : muG ε K ≠ 0 := (MeasureTheory.Measure.measure_pos_of_mem_nhds (muG ε) hK1).ne'
    have hfin : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
    have hK : muG ε K = ((c * c : NNReal) : ENNReal) * muG ε K := by
      conv_lhs => rw [h2]
      rfl
    have h3 : ((c * c : NNReal) : ENNReal) = 1 := by
      have h4 : ((c * c : NNReal) : ENNReal) * muG ε K = 1 * muG ε K := by
        rw [one_mul]
        exact hK.symm
      exact (ENNReal.mul_left_inj hpos hfin).mp h4
    have h5 : (c : ℝ) * c = 1 := by exact_mod_cast h3
    have h6 : (0 : ℝ) ≤ c := c.2
    apply NNReal.eq
    push_cast
    nlinarith
  rw [key, hc1, one_smul]
theorem ballFinite : BallFinite := ball_finite_measure_holds
theorem volGrowth : VolGrowth := volume_growth
theorem cpartMem : CpartMem := complex_parts_mem_lie_algebra_holds
theorem rdExt : RdExt := right_derivative_extends
theorem rdLeft : RdLeft := right_derivative_left_invariant
theorem rdLin : RdLin := right_derivative_linear
theorem rdSmooth : RdSmooth := rdSmooth_of right_derivative_extends
theorem eabGl : EabGl := eabGl_of complex_parts_mem_lie_algebra_holds (rdLin_of right_derivative_extends)
  (rdBracket_of right_derivative_extends (rdSmooth_of right_derivative_extends)) (rdSmooth_of right_derivative_extends)
end Formalism.REAL

namespace Formalism.REAL

end Formalism.REAL
