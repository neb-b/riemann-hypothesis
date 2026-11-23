module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.GIdilFull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0099
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0094

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_full_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil'_k hT hAux hLE hAw (_root_.PositivityTheory.SiegelWeilFormula.Kdil.locFamG_done_k hT hAux (fun _ _ P => KFock.isSw_fP P) hLI)
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
