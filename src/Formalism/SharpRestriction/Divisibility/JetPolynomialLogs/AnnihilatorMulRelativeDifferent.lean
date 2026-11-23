module

public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.DirichletDensity.HostDensityArith

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.placeRankTwoOne NumberField Formalism.FrobeniusOrbits
open scoped Pointwise

namespace Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent

theorem discr_K (D : D7) : discr D.host.K = -(D.host.d : ℤ) := by
  have hb : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  let x : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = ((-(D.host.d : ℤ) : ℤ) : D.host.K) := by
    apply Subtype.ext
    simpa [x] using hb
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  exact Formalism.HF.Final.quadDiscr D.host.K _ x hx htop (Formalism.HF.P.sqf_neg _ D.host.hyp.2.1)
    (by have := D.host.hyp.2.2.2.1; omega)

theorem finrank_K (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  SplitK.finrank_K (L := D.host.E) (b := D.host.sqd) (d := D.host.d) D.host.hyp.2.1.pos
    (D.host.sqd_sq)

end Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent
