module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.LengthBaseChangeLocal
public import Formalism.FilteredPoleLength.LocalDescentLevels.MemSpanBasisFun
public import Formalism.IncomingBounds.FlowDegreeBounds.Bundle0002
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0003
public import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0004
public import Formalism.FilteredPoleLength.LocalDescentLevels.LatticeIndexBis

@[expose] public section

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChain
section
namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsChain : LevelsChain := by
  intro ι _ ep f ν v νs c' T e hep hT hc' hv hν hcase
  apply levelsSum ι ep f (fun z => max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉) v T c'
  intro z
  have hpos : (0 : ℝ) < ep z := by exact_mod_cast hep z
  have h : ((max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - e)⌉ : ℤ) : ℝ) / ep z ≤ T * c' * v z := by
    rcases hcase with ⟨h1, h2⟩ | h3
    · exact poleOrderGood (ep z) T (ν z) νs c' (v z) e (hep z) hc' (hv z) (hν z) (h2 z) h1
    · subst h3
      exact poleOrderBad (ep z) T (ν z) νs c' (v z) (hep z) hT hc' (hv z) (hν z)
  rw [div_le_iff₀ hpos] at h
  linarith

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent
section
namespace Formalism.LatticeBaseChangeAlt

theorem localStepDescent : LocalStepDescent :=
  localStepDescent_of finrank_span_image_alt inter_baseChange_lattice index_baseChange_lattice

end Formalism.LatticeBaseChangeAlt
end

