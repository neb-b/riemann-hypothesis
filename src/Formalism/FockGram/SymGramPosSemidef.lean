module

public import Formalism.FockGram.Bundle0001
public import Formalism.FockGram.FockGramProofs.Bundle0002
public import Formalism.FockGram.FockGramProofs.Bundle0001
public import Mathlib
public import Formalism.FockGram.StatementLat
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

namespace Formalism.E

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
