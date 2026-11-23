module

public import Formalism.LocalToGlobal.ClassOfRecordOfChoice

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.LinkGCl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.L2.Top3

variable {eps : ℝ}

theorem admissible_tops_of_class {𝒜 : FamClass} {C0 : ℝ} (Fm : FamP eps) (hc : D3 C0 𝒜 Fm) : Formalism.MainNotions.G.Adm2F Fm :=
  admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)

end Formalism.L2.DIV.LinkGCl

end
