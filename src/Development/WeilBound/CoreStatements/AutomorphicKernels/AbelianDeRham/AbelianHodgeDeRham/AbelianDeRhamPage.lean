module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.AbelianHodgeDeRham
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.PageOf

@[expose] public section

namespace MainStatements.Hodge.Free

theorem abelianDeRhamPage : FubiniStudyChowHeightFormula₂.Hdr.AbelianDeRhamPage := page_of_hodge abelianHodgeDeRham

end MainStatements.Hodge.Free
