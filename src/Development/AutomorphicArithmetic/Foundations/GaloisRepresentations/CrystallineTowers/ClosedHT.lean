module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrystallinePeriodsOfSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SqCore
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateComparisonSmoothProjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FinalC

@[expose] public section

namespace UpperTheory.Gal.Seam.HT

open UpperTheory.Gal.Seam

open CrystallineSemistableComparison UpperTheory.Gal.KunnethLefschetz

theorem etSideS : EtSideS := fun l _ K _ => Top.etSide_sm_holds l K

theorem hodgeTate_comparison_smooth_projective : CrystallineSemistableComparison.HT.HodgeTateMapExists := CrystallineSemistableComparison.HT.hodgeTate_of_etale_side etSideS

theorem htBij : Onto.HTBij := Onto.htBij_of hodgeTate_comparison_smooth_projective G.sqEx3 Top.diagEt3_holds Top.etFin_holds

theorem htSpecGood : HTSpecB.HTSpecGood := Spec.htSpecGood_of htBij CrystallineSemistableComparison.Om.Nt2F.hodge_iso_natural_cech Top.etFin_holds

end UpperTheory.Gal.Seam.HT
