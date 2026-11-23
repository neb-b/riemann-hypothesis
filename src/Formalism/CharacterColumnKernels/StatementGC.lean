module

public import Formalism.CharacterColumnKernels.StatGlobalModule

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.NG

instance evalSpSMulComm (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
    (d : Type*) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (x' : X') : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') :=
  ⟨fun r c v => by
    show (matEnd (FractionRing O) (FractionRing O) d (evalAt O d R' x' r)) (c • v) =
      c • (matEnd (FractionRing O) (FractionRing O) d (evalAt O d R' x' r)) v
    exact LinearMap.map_smul _ c v⟩

end Formalism.NG
