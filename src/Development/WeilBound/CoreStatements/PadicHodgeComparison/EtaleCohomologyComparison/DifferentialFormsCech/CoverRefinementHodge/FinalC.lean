module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FormToCOBijectiveI
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.PfPullC
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.HodgeCechComparison

@[expose] public section

open CategoryTheory AlgebraicGeometry GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.Nt2F

open CrystallineSemistableComparison.Om.Glob CrystallineSemistableComparison.Om.Cech CrystallineSemistableComparison.Om.Nt2

theorem glob_iso_c : type_of% (@CrystallineSemistableComparison.Om.Glob.glob_iso _) := CrystallineSemistableComparison.Om.GlobPf2.glob_iso
theorem cechOm_pull_c : type_of% (@CrystallineSemistableComparison.Om.Cech.cechOm_pull _) := CrystallineSemistableComparison.Om.Cech.CechFormPull.cechOm_pull_pf

theorem hodge_iso_natural_cech : type_of% (@CrystallineSemistableComparison.Om.hdg_iso _) :=
  hdg_iso_of_ing glob_iso_c formToCO_bijective_i formToCO_smul_i cechOmAdd_smul_i cechOm_pull_c formCoch_pull_i
    cov_refine pullH_id pullC_id

end CrystallineSemistableComparison.Om.Nt2F
