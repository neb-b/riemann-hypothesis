module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QuotLocalOfQuotientLength
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.LenDescentOfLengthBaseChangeLocal

@[expose] public section

namespace Formalism.L2.Pj.QAt

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions

variable {D : D7}

theorem qat_of_bridge' (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (CR Ck Ch Ah Cc Ac T c : ℝ) (hlat : Submodule.IsFullLattice B.KO (B.Mlat j ka))
    (hbr : QBridgeAt large₂ B j ka CR Ch Ah Cc Ac T c) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ B j ka CR Ck Ch Ah Cc Ac T c :=
  qat_of_bridge quotLocal_holds lenDescent_holds large₂ B j ka CR Ck Ch Ah Cc Ac T c hlat hbr

end Formalism.L2.Pj.QAt
