module

public import Formalism.PeriodIntegrals.NablaSpans.ExpansionCoeffValuationGe
public import Formalism.PeriodIntegrals.NablaSpans.MinorProdSpanHasCompl
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024

@[expose] public section

open Formalism.BasicNotions

namespace Formalism.MainNotions.DIV.Lemmas

theorem kw_of_cutSB (h : CutKW.KWsb) : CutKW.KW := h minor_span_complement

end Formalism.MainNotions.DIV.Lemmas
