module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsHeckeSmul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0003

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

open PositivityTheory.RgBcC

theorem blkOp₀ : BlockOperatorsProductAdjoint := blkOp' wave_existence_speed_multiplicity.2.2.2

theorem blkComm₀ : BlockPureTensorsCommute := blkComm' wave_existence_speed_multiplicity.2.2.2

theorem blkWord₀ : BlockWordOperators := blkWord' wave_existence_speed_multiplicity.2.2.2

theorem pTTest₀ : PTTest := pTTest' wave_existence_speed_multiplicity.2.2.1

theorem locOk₀ : LocOk := locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem locComm₀ : LocComm := locComm idemAlg sphComm PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem seenTr₀ : SeenTr := seenTr PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem sqOk₀ : SqOk := sqOk adjKer₀ blkOp₀ blkWord₀

end PositivityTheory.Rg.BcB.F.BlockFiniteConvolution
