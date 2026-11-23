module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0015
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommuteOfUnitaryConjugate
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ZetaDegZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0020
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KhwExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InnerEqZeroOfWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GlRelOfBracket
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0035
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.Spread
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0017
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CobApplyOfDeg
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll

@[expose] public section

namespace CompanionTheory.D.DSIC

theorem hCAR : CAR := GlobalTheory.CompanionTheory.ChainCAR.car
theorem hFRel : FRel := GlobalTheory.CompanionTheory.DSICFRel.car_imp_frel hCAR
theorem hBdFacts : BdFacts := GlobalTheory.CompanionTheory.KoszulBd.bdFacts hCAR
theorem hGFacts : GFacts := GlobalTheory.CompanionTheory.GopEntries.gFacts
theorem hKoszul : Koszul := GlobalTheory.CompanionTheory.DSICKoszul.koszul hCAR
theorem hVerma : Verma := GlobalTheory.CompanionTheory.DSVerma.verma
theorem hCover : Cover := GlobalTheory.CompanionTheory.DSCover.cover hKoszul hVerma
theorem hCO0 : CapelliDeterminantBlockProduct := GlobalTheory.CompanionTheory.CapelliBlocks.co0
theorem hCO : CO := GlobalTheory.CompanionTheory.CasselmanOsborne.co_of hBdFacts hGFacts hCover hCO0
theorem hZetaHW : ZetaHW := GlobalTheory.CompanionTheory.ZetaHighest.zetaHW
theorem hWLem : WLem := GlobalTheory.CompanionTheory.DSICWLem.wlem_of_gfacts hGFacts
theorem hNormLt : NormLt := GlobalTheory.CompanionTheory.DSNormLt.normLt
theorem hAdj : Adj := GlobalTheory.CompanionTheory.DSChainAdj.adj
theorem hGamDom : GamDom := GlobalTheory.CompanionTheory.GamDomProof.gamDom
theorem hKHWExists : KHWExists := GlobalTheory.CompanionTheory.KHighestExists.khwExists
theorem hLowSpan : LowSpan := GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
theorem hHWMap : HWMap := GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan hLowSpan
theorem hPRV : PRV := GlobalTheory.CompanionTheory.ChainHighest.aux₃ hFRel hGFacts hGamDom hKHWExists hHWMap
theorem hAlgCore : AlgCore := algCore_of hFRel hBdFacts hCO hZetaHW hWLem hNormLt hAdj hPRV
theorem hAlgCoreSub : AlgCoreSub := GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore hAlgCore
theorem hSmLin : SmLin := GlobalTheory.CompanionTheory.DSSmLin.smLin
theorem hSmBracket : SmBracket := GlobalTheory.CompanionTheory.SmBracket.smBracket_of hSmLin
theorem hSmMod : SmMod := GlobalTheory.CompanionTheory.SmoothModule.smMod hSmLin hSmBracket
theorem hActQ : ActQ := GlobalTheory.CompanionTheory.DSCapelliAction.actQ
theorem hSpread : Spread := capelli_spread
theorem hKFinStab : KFinStab := GlobalTheory.CompanionTheory.KFinStab.kFinStab
theorem hKExp : KExp := GlobalTheory.CompanionTheory.DSICKExp.kExp
theorem hStabLink : StabLink := GlobalTheory.CompanionTheory.DSStabLink.stabLink hKExp
theorem hWtLink : WtLink := GlobalTheory.CompanionTheory.WtLinkPf.wtLink
theorem hHWofType : HWofType := GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType hStabLink hWtLink
theorem hTypeOfHW : TypeOfHW := GlobalTheory.CompanionTheory.DSKType.typeOfHW hLowSpan hStabLink hWtLink

theorem discrete_series_infinitesimal_character : PI.DSInfCharCap.DSInfCharCap :=
  dsInfCharCap_of hAlgCoreSub hSmMod hActQ hSpread CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs hKFinStab hStabLink
    hHWofType hTypeOfHW

end CompanionTheory.D.DSIC
