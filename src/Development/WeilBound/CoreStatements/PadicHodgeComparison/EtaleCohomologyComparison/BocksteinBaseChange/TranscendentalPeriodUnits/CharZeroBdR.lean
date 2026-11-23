module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.CrystallineSemistableComparison
public import GroundTheory.PAdicHodge.BCrisNewtonLift
public import GroundTheory.PAdicHodge.AInfGalois
public import GroundTheory.PAdicHodge.AInfXi
public import GroundTheory.PAdicHodge.TiltAlgClosed
public import GroundTheory.PAdicHodge.Bundle0004
public import GroundTheory.PAdicHodge.Bundle0002
public import GroundTheory.PAdicHodge.ExtRobbaBounded
public import GroundTheory.PAdicHodge.Bundle0001
public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.Bundle0003
public import GroundTheory.PAdicHodge.BCrisEigenWitt
public import GroundTheory.PAdicHodge.BStPeriod
public import GroundTheory.PAdicHodge.ACrisBdR
public import GroundTheory.PAdicHodge.BdRGalois
public import GroundTheory.PAdicHodge.ACrisBdRGalois
public import GroundTheory.PAdicHodge.InstMulSemiringActionGalPlus
public import GroundTheory.PAdicHodge.BCrisNewtonApprox
public import GroundTheory.PAdicHodge.UnramifiedFrob
public import GroundTheory.PAdicHodge.BdRTGalois
public import GroundTheory.PAdicHodge.BCrisPlusInvariants
public import GroundTheory.PAdicHodge.BCrisRegularFinal
public import GroundTheory.PAdicHodge.ACrisGalois
public import GroundTheory.PAdicHodge.FundamentalSeqSurj
public import GroundTheory.PAdicHodge.FontaineLemmaInvariants
public import GroundTheory.PAdicHodge.ExistsNormLeOfNormLtOneFinite
public import GroundTheory.PAdicHodge.BCrisNewton

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}


variable (l) in
abbrev Fr : Subfield (BdR l) :=
  ACris.fracBCris (untilt_epsilon (p := l)) untilt_frobeniusEquiv_symm_epsilon_ne_one

end CrystallineSemistableComparison
