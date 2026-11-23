module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.BVRApply
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.GlGeneratedTransvectionsDiag
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003

@[expose] public section

namespace PI.VolSemiDirect.W.Cj

theorem orthogonal_invariance_of_stable_rank_one (h1 : AdeleStableRankOne) : OrthInv :=
  orthInv_of h1 gl_generated_transvections_diag transvection_preserves_haar

theorem unipotent_modulus_of_stable_rank_one (h1 : AdeleStableRankOne) : VMod :=
  vMod_of (orthogonal_invariance_of_stable_rank_one h1) trace_basis_holds trace_gram_nondegenerate

theorem unipotent_modulus_holds : VMod := unipotent_modulus_of_stable_rank_one PI.VolSemiDirect.W.SR.stable_rank_one_adeles

end PI.VolSemiDirect.W.Cj
