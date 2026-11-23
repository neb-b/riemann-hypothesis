module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.AdelicCoordinatesEvalZeroFormMemAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0011
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DiagonalColumns.AdChar

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelW
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx_wired (hD : SDarb) (hP : PartCharInv) (hC : ChartFacts) (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_of hD PositivityTheory.SiegelWeilFormula.Ldexa.sEv bigT sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.PartCharInvAlt
section
namespace PositivityTheory.SiegelWeilFormula.Ald

theorem partCharInv : PartCharInv := PCI.partCharInv_of PCI.finPart

end PositivityTheory.SiegelWeilFormula.Ald
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelP
section
namespace PositivityTheory.SiegelWeilFormula.Ald

theorem siegelSmall_of_slice (hF : SliceFacts) : SiegelSmall := siegelSmall_of hF Ldx.adaptedChar

end PositivityTheory.SiegelWeilFormula.Ald
end

