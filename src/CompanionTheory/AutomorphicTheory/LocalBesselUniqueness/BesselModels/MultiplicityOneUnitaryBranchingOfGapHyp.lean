module

public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.UniqGapOfBmu
public import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGapAlt

@[expose] public section

namespace CompanionTheory.Lime.BM

open Formalism.BasicNotions

theorem uniqGap_holds : UniqGap := CompanionTheory.Bmu.besselMapUniqGap

theorem ampUnif_holds : Formalism.MainNotions.S.Pv.LemmaJ.AmpUnif := ampUnif CompanionTheory.Bmu.besselMapUniqGap

theorem wuDecayOfGap_holds' : Formalism.L2.SG.Pf.WuDecayOfGap := wuDecayOfGap CompanionTheory.Bmu.besselMapUniqGap

end CompanionTheory.Lime.BM
