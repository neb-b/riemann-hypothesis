module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem cuspDecaySobolev : GlobalTheory.Published.CuspDecaySobolev :=
  GlobalTheory.Size.cuspDecaySobolev_of_bound GlobalTheory.CuspGeo.cuspDecayBound

theorem cuspBounded : GlobalTheory.Published.CuspBounded :=
  GlobalTheory.CuspDecay.cuspBounded_of_cuspRapidDecay (GlobalTheory.Grow.cuspRapidDecay_of_bound GlobalTheory.CuspGeo.cuspDecayBound)

end PositivityTheory.Stage1.PM
