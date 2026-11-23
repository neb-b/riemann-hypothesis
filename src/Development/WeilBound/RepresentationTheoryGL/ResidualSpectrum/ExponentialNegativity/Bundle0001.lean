module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOf
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UniformInitialGrowth.InitBnd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.BoxVolumes.ExistsMeasureLeProd
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.LatticeReduction.RedApplyCongr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumHyperplanesComplementFlags
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SqIntCritOfFinTr
section
namespace PositivityTheory.Rg.Rs

theorem sqIntCrit_of_finTr (h : FinTr) : SqIntCrit := sqIntCrit_of initBnd_holds h boxvol_holds

end PositivityTheory.Rg.Rs
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopGap
section
namespace PositivityTheory.Rg.Rs

theorem gap_holds : Gap := gap_of latOf_holds GlobalTheory.CompanionTheory.GapOpMain.gapOp

end PositivityTheory.Rg.Rs
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.TopNeg
section
namespace PositivityTheory.Rg.Rs

theorem expNeg_holds : ExpNeg := expNeg_of count_holds

end PositivityTheory.Rg.Rs
end

