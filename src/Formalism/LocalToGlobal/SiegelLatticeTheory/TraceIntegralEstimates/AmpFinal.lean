module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpCell
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpTrans
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig

@[expose] public section

namespace Formalism.L2.S.Pv.AmpFinal

open Formalism.MainNotions.S.Pv.LemmaJ

theorem rootCmp_of_parts (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt) : RootCmp :=
  rootCmp_of Formalism.L2.S.Pv.AmpCell.cell_representation Formalism.MainNotions.S.Pv.AmpTrans.amplitude_transport hRJ hRH hOQ hRA

theorem ampUnif_of_parts (hAO : AmpOrbU) (hRJ : RootJac) (hRH : RootHaar) (hOQ : OrbQuotEx) (hRA : RelAtPt)
    (hNZ : AmpNZ) : AmpUnif :=
  ampUnif_of' hAO (rootCmp_of_parts hRJ hRH hOQ hRA) hNZ

end Formalism.L2.S.Pv.AmpFinal
