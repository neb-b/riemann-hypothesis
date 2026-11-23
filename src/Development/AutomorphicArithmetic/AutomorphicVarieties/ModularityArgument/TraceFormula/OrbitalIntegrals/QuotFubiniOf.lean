module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.ExtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Unimod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

@[expose] public section

namespace UpperTheory.V.Z.Tf.Orb

theorem gLTop_of : GLTop := gLTop

theorem extCont_of : ExtCont := extCont

theorem centComm_of : CentComm := centComm

theorem twCent_of : TwCent := twCent extCont_of gLTop_of centComm_of

theorem unimod_of : Unimod := unimod gLTop_of

theorem finPres_of : FinPres := finPres

theorem haarComm_of : HaarComm := haarComm

theorem quotIndep_of : QuotIndep := quotIndep

theorem normEx_of : NormEx := normEx

theorem quotMass_of : QuotMass := quotMass

theorem quotInt_of : QuotInt := quotInt quotMass_of

theorem quotPos_of : QuotPos := quotPos quotIndep_of quotInt_of quotMass_of

theorem quotRight_of : QuotRight := quotRight quotIndep_of

theorem quotFubini_of : QuotFubini := quotFubini quotMass_of

theorem absComm_of : AbsComm := absComm quotFubini_of quotRight_of finPres_of

theorem untwist_of : Untwist := untwist

theorem twOrbFin_of (h : OrbProper) : TwOrbFin := twOrbFin gLTop_of extCont_of twCent_of h haarComm_of normEx_of quotInt_of quotPos_of

theorem twOrbLin_of (h : OrbProper) : TwOrbLin := twOrbLin (twOrbFin_of h)

theorem orbLin_of (h : OrbProper) : OrbLin := orbLin (twOrbLin_of h) untwist_of

theorem twOrbComm_of (h : OrbProper) : TwOrbComm := twOrbComm gLTop_of extCont_of twCent_of h haarComm_of unimod_of absComm_of

theorem orbComm_of (h : OrbProper) : OrbComm := orbComm (twOrbComm_of h) untwist_of

end UpperTheory.V.Z.Tf.Orb
