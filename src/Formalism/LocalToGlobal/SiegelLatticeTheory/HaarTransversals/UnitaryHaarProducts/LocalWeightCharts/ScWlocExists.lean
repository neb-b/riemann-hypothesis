module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfNilpotentChart
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0008

@[expose] public section

theorem scWlocExists (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : Formalism.L2.SG.SplitPrimeNormLemmas.WlocExists :=
  WlocSk.scWlocExists_of_chart WlocSk.nilpotent_chart_exists hR
