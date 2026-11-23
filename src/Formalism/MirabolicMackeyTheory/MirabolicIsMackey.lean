module

public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0001
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0002
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LemmaGG
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0005
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.ThreeForms

@[expose] public section

namespace Formalism.EigenvalueLevelCeiling

theorem idxMono : IdxMono := index_monotone
theorem idxScaleIn : IdxScaleIn := index_scale_inclusion
theorem idxCutLe : IdxCutLe := index_truncation_le
theorem idxTransport : IdxTransport := index_transport
theorem latInter : LatInter := lattice_intersection
theorem threeForms : ThreeForms := three_forms
theorem idxPsiGood : IdxPsiGood := idxPsiGood_of idxMono idxScaleIn idxCutLe latInter
theorem lemmaGG : LemmaGG := good_index_GG
theorem mirabolicIsMackey : MirabolicIsMackey := mirabolic_is_mackey
theorem onLocal : OnLocal := onLocal_of idxMono idxCutLe idxTransport latInter threeForms idxPsiGood lemmaGG
theorem ramBasic : RamBasic := ramified_basic_bound

end Formalism.EigenvalueLevelCeiling
