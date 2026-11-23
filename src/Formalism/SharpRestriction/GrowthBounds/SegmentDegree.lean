module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.NonemptyDvrSettingOfStandard
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0021
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0020
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SumSingleApplyZero
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0022
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.M0LeBwOfIsW
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BfamAtWLetterEq

@[expose] public section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem second_estimate_of_restrictions (D : Formalism.BasicNotions.D7) (h41 : DiscriminantNonzeroModUniformiser) (h45 : AdmB D → GeneratorModuloUniformiser 1088)
    (hLam : AdmB D → RestLam 1088) (hPad : RestPad 1088) (hSum : RestSum 1088 1)
    (hMem : AdmB D → RestMem 1088) (hInd : AdmB D → RestInd 1088)
    (hT1 : AdmB D → GoodPathWeight 1088) (hMon : RestMon 1088) : SecondPartClosed D :=
  second_estimate_of_rank_bound D 1088 1 (by norm_num) (by norm_num) restDeg restSel fun hA =>
    restRank_of 1088 1 h41 (h45 hA)
      (restCount_of 1088 1 (hLam hA) (restSeg_of 1088 (hMem hA) (hInd hA) restFin (hT1 hA) hMon) hPad hSum)

theorem restMon : RestMon 1088 := restMon_of 1088 beta_ratio_bound tau_degree_on_path_bound residue_class_count

theorem restInd (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestInd 1088 := restInd_of 1088 (restKey_of D hAdm 1088)

theorem secondPartClosed (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  second_estimate_of_restrictions D discriminant_nonzero_mod_uniformiser (fun hA => generator_modulo_uniformiser_of_adm D hA 1088 (by norm_num))
    (fun hA => restLam_of D hA 1088 restLamDeg)
    restPad restSum (fun hA => restMem_of D hA) (fun hA => restInd D hA) (fun hA => good_path_weight D hA) restMon

end Formalism.MainNotions.SelectionLemmas.Pf
