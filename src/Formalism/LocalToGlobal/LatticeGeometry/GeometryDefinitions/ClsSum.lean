module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SatakeDualWeyl.DefsCS
public import Formalism.HermitianLattices.Bundle0002

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

section Frames

variable {K : Type} [Field K] [NumberField K] [StarRing K]


open Classical in
def frameOf {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : ∃ Y : Matrix ι ι ℂ, IsUnit Y.det ∧ (Y⁻¹).conjTranspose * Y⁻¹ = M then h.choose else 1


end Frames

end Formalism.L2.Geo.Def
