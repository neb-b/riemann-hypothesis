module

public import Formalism.SharpRestriction.GrowthBounds.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0015
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0011
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem witt_identification_of_admitted {D : Formalism.BasicNotions.D7} (hA : admitted D) : WittIdent :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem restForm (D : Formalism.BasicNotions.D7) : RestForm :=
  restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus

theorem stmtEExt_of_rawTail1 {D : Formalism.BasicNotions.D7} (h : admitted D → RestRawTail1) : ExtendedClosedForm D :=
  stmtEExt_of fun hA => paired_lifts_of_identity (witt_identification_of_admitted hA) (h hA) (restForm D)

def RawTailReduction : Prop := RestAsmRT

theorem stmtEExt_of_15c {D : Formalism.BasicNotions.D7} (h : admitted D → RawTailReduction) : ExtendedClosedForm D :=
  stmtEExt_of_rawTail1 fun hA => restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res))) (h hA)

end Formalism.MainNotions.ColumnSystems.Pf
