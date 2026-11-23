module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0048
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0050
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0051

@[expose] public section

namespace CompanionTheory.RgExh.Dec.N.S

theorem exhaustion_start : CompanionTheory.RgExh.Dec.Start :=
  _root_.GlobalTheory.CompanionTheory.RgStart.startOf _root_.GlobalTheory.CompanionTheory.GradFlag.flagFacts _root_.GlobalTheory.CompanionTheory.PSubFlag.psubEq _root_.GlobalTheory.CompanionTheory.GradLine.lineFacts _root_.GlobalTheory.CompanionTheory.SlabLemma.slab (GlobalTheory.T.fubini_of_parabolic_haar_multiple _root_.GlobalTheory.CompanionTheory.FubNM.fub2) _root_.GlobalTheory.CompanionTheory.RgKMaj.kMaj

end CompanionTheory.RgExh.Dec.N.S
