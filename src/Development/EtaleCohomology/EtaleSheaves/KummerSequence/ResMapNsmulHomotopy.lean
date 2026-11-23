module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuMapPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafUnitRootPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder

open LateralTheory.E.E4 LeafKumSeqPf KummerH0Surjection

theorem muUnits : LeafKumMuPf.LeafKumMuUnits := by
  have hI := LeafKumMuInjPfGlue.LeafKumMuInj_of TwLocGenPf.TwLocGen_of GmSepPf.GmSep_of
  exact LeafKumMuUnitsPf.LeafKumMuUnits_of LeafKumMuMapPf.LeafKumMuMap_of hI
    (LeafKumMuSurjPf.etale_mu_twist_sections_surj_of_prim_root_pow_inj LeafKumMuSurjPrimPf.LeafKumMuSurjPrim_of
      LeafKumMuSurjPowPf.LeafKumMuSurjPow_of hI)

theorem kumSecSurj : LeafKumSecSurj := LeafKumSecSurjPf.LeafKumSecSurj_of LeafUnitRootPf.LeafUnitRoot_of

end LateralTheory.E.H2CurveOrder

end
