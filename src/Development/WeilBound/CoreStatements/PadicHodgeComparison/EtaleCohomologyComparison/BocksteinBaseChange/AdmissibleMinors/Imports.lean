module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.Bundle0002
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdmissibleMinors.FilRZero

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

theorem inj : ComparisonInjectiveStrict := by
  intro l _ K R G P hR hE
  exact Inj.reduce P hR hE (fun M N u hu n r => Inj.filR_pull (Model.genMap u hu) (Model.genMap_q u hu) n r)
    (fun M hM d hc n => Inj.conn P hR hE M hM d hc n)

end CrystallineSemistableComparison
