module

public import Formalism.TameInertiaTowers.CentralOrderTwo.OrderOfThreeUnitsTwoPow
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0001
public import Formalism.TameInertiaTowers.CentralOrderTwo.MemDecompositionSubgroupIff
public import Formalism.TameInertiaTowers.CentralOrderTwo.NegOneNeOneUnitsZmodFour
public import Formalism.TameInertiaTowers.CentralOrderTwo.Bundle0002
public import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
public import Formalism.TameInertiaTowers.CentralOrderTwo.DecompositionSubgroupIndex
public import Formalism.TameInertiaTowers.CentralOrderTwo.OddEqOneOfSubOneMem

@[expose] public section

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem layerConj : LayerConj := layerConj_of layerGalois
theorem layerReal : LayerReal := layerReal_of layerGalois layerConj
theorem layerDecompTwo : LayerDecompTwo := layerDecompTwo_of layerGalois
theorem layerInertiaTwo : LayerInertiaTwo := layerInertiaTwo_of layerGalois
theorem layerEFGTwo : LayerEFGTwo := layerEFGTwo_of layerGalois layerReal
theorem layerInertiaTame : LayerInertiaTame := layerInertiaTame_of layerGalois
theorem layerFrob : LayerFrob := layerFrob_of layerGalois

theorem tower_field_foundations :
    LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
    LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob :=
  ⟨layerExists, layerGalois, layerConj, layerReal, layerDecompTwo, layerInertiaTwo, layerEFGTwo,
    layerInertiaTame, layerFrob⟩

theorem towerProperties :
    (UnitsTwoPow ∧ QuotCyclic ∧ TwoAdicOrder ∧ TwoAdicVal ∧ DecompModel ∧ GmRank ∧ GensModel ∧
      GamEModel ∧ GGModel ∧ CentralExtAbelian ∧ CommGen ∧ RankBound ∧
      NormalOrderTwoCentral ∧ TwistVal ∧ CoinvLength ∧ PGroupGen ∧ GenusModel ∧ GenusAbelian) ∧
    InvLength ∧
    (LayerExists ∧ LayerGalois ∧ LayerConj ∧ LayerReal ∧ LayerDecompTwo ∧ LayerInertiaTwo ∧
      LayerEFGTwo ∧ LayerInertiaTame ∧ LayerFrob) :=
  ⟨⟨unitsTwoPow, quotCyclic, twoAdicOrder, twoAdicVal, decompModel, gmRank, gensModel, gamEModel,
      ggModel, centralExtAbelian, commGen, rankBound,
      normalOrderTwoCentral, twistVal, coinvLength, pGroupGen, genusModel, genusAbelian⟩,
    invLength, tower_field_foundations⟩

end Formalism.TwoAdicCyclotomicDecomposition
