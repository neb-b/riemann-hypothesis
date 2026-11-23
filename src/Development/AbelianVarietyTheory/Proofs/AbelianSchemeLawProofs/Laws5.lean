module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032

@[expose] public section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
theorem _root_.GlobalTheory.laws5 (hG : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) (hS : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt) : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws5 := by
  refine ⟨?_, _root_.GlobalTheory.qkToAk_baseChange hG hS, _root_.GlobalTheory.psiOnExists⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.OLinBaseChangeSt
  intro R R' _ _ _ _ I I' hI hI' φ D A G _ _ U G' _ _ bc hbc A' D' hD U' hU O _ _ _ ιD ιA ιG
    hlin ιG' hG' ιA' hA'
  obtain ⟨x, ιD', h1, h2⟩ :=
    _root_.GlobalTheory.exists_oAct_of_isPullDeg hG R R' φ D.toPre D'.toPre hD O ιD
  letI := x
  refine ⟨x, ιD', h1, h2, ?_, ?_⟩
  · apply _root_.GlobalTheory.PullLinear.oLinear_of_isPullUnif R R' I I' φ D D' hD A A' G G' bc hbc U U' hU O
      ιD ιD' ιA ιA' ιG ιG'
    all_goals assumption
  · exact _root_.GlobalTheory.traceFormTwistIso_of_overPullback R R' φ D.toPre D'.toPre hD O ιD ιD' h1 h2

end GlobalTheory
