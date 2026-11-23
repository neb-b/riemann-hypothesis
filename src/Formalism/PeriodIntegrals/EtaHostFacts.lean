module

public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PI.EtaHostFacts

def Unram : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1


end PI.EtaHostFacts
