module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
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
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.Spread
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0022
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0035
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0017
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CobApplyOfDeg
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinalAll

@[expose] public section

namespace GlobalTheory.CompanionTheory.TransS.InfChar

open CompanionTheory.D.DSIC

theorem hLowSpan : LowSpan := GlobalTheory.CompanionTheory.KLowSpan.lowSpan_holds
theorem hHWMap : HWMap := GlobalTheory.CompanionTheory.DSICHWMap.hwMap_of_lowSpan hLowSpan
theorem hSmLin : SmLin := GlobalTheory.CompanionTheory.DSSmLin.smLin
theorem hSmBracket : SmBracket := GlobalTheory.CompanionTheory.SmBracket.smBracket_of hSmLin
theorem hSmMod : SmMod := GlobalTheory.CompanionTheory.SmoothModule.smMod hSmLin hSmBracket
theorem hKFinStab : KFinStab := GlobalTheory.CompanionTheory.KFinStab.kFinStab
theorem hKExp : KExp := GlobalTheory.CompanionTheory.DSICKExp.kExp
theorem hStabLink : StabLink := GlobalTheory.CompanionTheory.DSStabLink.stabLink hKExp
theorem hWtLink : WtLink := GlobalTheory.CompanionTheory.WtLinkPf.wtLink
theorem hHWofType : HWofType := GlobalTheory.CompanionTheory.DSHighestOfKType.hwOfType hStabLink hWtLink
theorem hTypeOfHW : TypeOfHW := GlobalTheory.CompanionTheory.DSKType.typeOfHW hLowSpan hStabLink hWtLink

end GlobalTheory.CompanionTheory.TransS.InfChar
