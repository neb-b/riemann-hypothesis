module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0031
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.NinLamPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ClassMapPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.WLocal
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3mixlinkPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0022
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Bundle0023
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPf

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lifting_theorem_of_uniform_link (hU1L : FirstFrameOfModels) :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
      (CA CB CK C : ℝ), 160 ≤ C → FontExAll D HW F → DdRFull D → DiRank D HW F Cm →
        IntegralityFromMetric D HW F Cm CA CB CK C :=
  local_theorem_of_leaf_lemmas generator_bound_of_hypotheses lift_bound_of_hypotheses DvdPf.dvdCondition quotient_jumps_subset normR_holds
    uniformiser_ring_of_hypotheses ExtPf.ext_pf w_pf kerlam2_pf ninlam_pf gradNCondition frobPiNCondition gamPiCondition
    OneGenPf.onegen_pf univlink_pf invLiftCondition ClassMapPf.classmap_pf frame_pf modelflink_pf
    exponent_recursion_holds modell_pf modelqlink_pf hU1L kappi_pf RankLink.rank_link_holds
    (RankBounds.u2rank_of_ring u2ring_pf) DescentValuation.down_of_models (u3uplink_pf_of w_pf) u3mixlink_pf

end Formalism.MainNotions.N.Ln34

end
