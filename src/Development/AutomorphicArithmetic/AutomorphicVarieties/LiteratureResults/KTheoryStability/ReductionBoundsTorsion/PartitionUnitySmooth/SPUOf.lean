module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GSmMin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.TransZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GTrans
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GRDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.RhoNonnegBis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.PfGRLip
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.GThick
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PartitionUnitySmooth.Bundle0004

@[expose] public section

namespace PositivityTheory.KB

open SmoothPartitionUnityBasic

theorem sPU_of : SHt → SPU := fun hH =>
  have hC := pf_GCount pf_Basic
  have hT := pf_GTrans pf_Basic pf_TransZ
  have hE := pf_GREqv pf_Basic
  have hL := pf_GTLip pf_Basic hC
  have hP := pf_GProper pf_Basic
  pf_GFin hH (gSmMin pf_Basic hC) (pf_GRSmooth pf_Basic) hE (pf_GRLow pf_Basic hC hE hL) (pf_GRDual pf_Basic hT hE hL)
    (pf_GRLip pf_Basic hE hL) (pf_GThick pf_Basic hT) hP (pf_GBump pf_Basic hP) (pf_GNrm pf_Basic) pf_DerB

end PositivityTheory.KB
