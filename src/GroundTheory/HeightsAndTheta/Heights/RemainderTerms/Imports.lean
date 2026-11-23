module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoinvReduction
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.RestAt
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealTransferOfSyzygy

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem CoinvStepReduction.full : CoinvStepReduction.Statement :=
  CoinvStepReduction.proof

theorem CoinvMonomialReduction.full : CoinvMonomialReduction.Statement :=
  CoinvMonomialReduction.proof CoinvStepReduction.full

theorem CoinvPolynomialReduction.full : CoinvPolynomialReduction.Statement :=
  CoinvPolynomialReduction.proof CoinvMonomialReduction.full

theorem CoinvIdealRepresentation.full : CoinvIdealRepresentation.Statement :=
  CoinvIdealRepresentation.proof

theorem HomogeneousComponentMul.full : HomogeneousComponentMul.Statement :=
  HomogeneousComponentMul.proof

theorem CoinvIdealComponent.full : CoinvIdealComponent.Statement :=
  CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full

theorem CoinvStaircaseDegree.full : CoinvStaircaseDegree.Statement :=
  CoinvStaircaseDegree.proof

theorem CoinvStaircaseComponent.full : CoinvStaircaseComponent.Statement :=
  CoinvStaircaseComponent.proof CoinvStaircaseDegree.full

theorem FlagCoeffBlockPermute.full : FlagCoeffBlockPermute.Statement :=
  FlagCoeffBlockPermute.proof

theorem FlagAltCoeffInjective.full : FlagAltCoeffInjective.Statement :=
  FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full

theorem FlagInjSumBound.full : FlagInjSumBound.Statement :=
  FlagInjSumBound.proof

theorem FlagStaircaseOrbit.full : FlagStaircaseOrbit.Statement :=
  FlagStaircaseOrbit.proof

theorem FlagVandermondeHomogeneous.full : FlagVandermondeHomogeneous.Statement :=
  FlagVandermondeHomogeneous.proof

theorem FlagAltTopDegree.full : FlagAltTopDegree.Statement :=
  FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full

theorem FlagAntisymHomogeneous.full : FlagAntisymHomogeneous.Statement :=
  FlagAntisymHomogeneous.proof

theorem FlagIntegralPermute.full : FlagIntegralPermute.Statement :=
  FlagIntegralPermute.proof FlagCoeffBlockPermute.full

theorem FlagIntegralAntisymmetrize.full : FlagIntegralAntisymmetrize.Statement :=
  FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full

theorem FlagIntegralTopComponent.full : FlagIntegralTopComponent.Statement :=
  FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full

theorem FlagHomogeneousComponentMul.full : FlagHomogeneousComponentMul.Statement :=
  FlagHomogeneousComponentMul.proof

theorem FlagIntegralVandermondeMul.full : FlagIntegralVandermondeMul.Statement :=
  FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full

theorem FlagIntegralViaQuotient.full : FlagIntegralViaQuotient.Statement :=
  FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full

theorem FlagIntegralTopDegree.full : FlagIntegralTopDegree.Statement :=
  FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full

theorem FlagIntegralVandermondePos.full : FlagIntegralVandermondePos.Statement :=
  FlagIntegralVandermondePos.proof

theorem FlagSwapDivisible.full : FlagSwapDivisible.Statement :=
  FlagSwapDivisible.proof

theorem FlagDiffPrime.full : FlagDiffPrime.Statement :=
  FlagDiffPrime.proof

theorem FlagDiffNotDvd.full : FlagDiffNotDvd.Statement :=
  FlagDiffNotDvd.proof

theorem FlagProdPrimesDvd.full : FlagProdPrimesDvd.Statement :=
  FlagProdPrimesDvd.proof

theorem FlagVandermondeDvd.full : FlagVandermondeDvd.Statement :=
  FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full

theorem FlagDividedDifferencePoly.full : FlagDividedDifferencePoly.Statement :=
  FlagDividedDifferencePoly.proof FlagVandermondeDvd.full

theorem FlagSymmetricMulAntisym.full : FlagSymmetricMulAntisym.Statement :=
  FlagSymmetricMulAntisym.proof

theorem FlagPowerSumSymmetric.full : FlagPowerSumSymmetric.Statement :=
  FlagPowerSumSymmetric.proof

theorem FlagAntisymDecomposition.full : FlagAntisymDecomposition.Statement :=
  FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full

theorem FlagQuotientHomogeneous.full : FlagQuotientHomogeneous.Statement :=
  FlagQuotientHomogeneous.proof

theorem FlagRestrictHomogeneous.full : FlagRestrictHomogeneous.Statement :=
  FlagRestrictHomogeneous.proof

theorem FlagRestrictSymmetric.full : FlagRestrictSymmetric.Statement :=
  FlagRestrictSymmetric.proof

theorem FlagRestrictPowerSum.full : FlagRestrictPowerSum.Statement :=
  FlagRestrictPowerSum.proof

theorem FlagRestrictDecomposition.full : FlagRestrictDecomposition.Statement :=
  FlagRestrictDecomposition.proof FlagRestrictPowerSum.full

theorem FlagPowerSumPreimage.full : FlagPowerSumPreimage.Statement :=
  FlagPowerSumPreimage.proof

theorem FlagRestrictConstantCoeff.full : FlagRestrictConstantCoeff.Statement :=
  FlagRestrictConstantCoeff.proof

theorem LemmaA.full : LemmaA.Statement :=
  LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full FlagRestrictDecomposition.full FlagPowerSumPreimage.full FlagRestrictConstantCoeff.full FlagIntegralViaQuotient.full

theorem SchAevalSignedRename.full : SchAevalSignedRename.Statement :=
  SchAevalSignedRename.proof

theorem SchAntisymmetrizePlace.full : SchAntisymmetrizePlace.Statement :=
  SchAntisymmetrizePlace.proof

theorem SchAlternantHomogeneous.full : SchAlternantHomogeneous.Statement :=
  SchAlternantHomogeneous.proof

theorem SchSmallBlockProduct.full : SchSmallBlockProduct.Statement :=
  SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full

theorem SchAlternantRenamePlace.full : SchAlternantRenamePlace.Statement :=
  SchAlternantRenamePlace.proof

theorem SchConcatExponent.full : SchConcatExponent.Statement :=
  SchConcatExponent.proof

theorem SchConcatAlternant.full : SchConcatAlternant.Statement :=
  SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full

theorem SchConcatAlternantZero.full : SchConcatAlternantZero.Statement :=
  SchConcatAlternantZero.proof

theorem SchBlockVandermondeOne.full : SchBlockVandermondeOne.Statement :=
  SchBlockVandermondeOne.proof

theorem SchSchurHomogeneous.full : SchSchurHomogeneous.Statement :=
  SchSchurHomogeneous.proof

theorem LemmaB.full : LemmaB.Statement :=
  LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full

theorem CombCardYoungCells.full : CombCardYoungCells.Statement :=
  CombCardYoungCells.proof

theorem CombTableauRowCount.full : CombTableauRowCount.Statement :=
  CombTableauRowCount.proof

theorem CombTableauRowPrefix.full : CombTableauRowPrefix.Statement :=
  CombTableauRowPrefix.proof

theorem CombTableauRowLattice.full : CombTableauRowLattice.Statement :=
  CombTableauRowLattice.proof

theorem CombYoungRowCard.full : CombYoungRowCard.Statement :=
  CombYoungRowCard.proof

theorem CombWordOfTableau.full : CombWordOfTableau.Statement :=
  CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full

theorem CombCellOfWordMem.full : CombCellOfWordMem.Statement :=
  CombCellOfWordMem.proof

theorem CombCellOfWordInj.full : CombCellOfWordInj.Statement :=
  CombCellOfWordInj.proof

theorem CombCellOfWordMono.full : CombCellOfWordMono.Statement :=
  CombCellOfWordMono.proof

theorem CombTableauOfWord.full : CombTableauOfWord.Statement :=
  CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full

theorem CombTableEqWords.full : CombTableEqWords.Statement :=
  CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full

theorem CombCfUpdateZero.full : CombCfUpdateZero.Statement :=
  CombCfUpdateZero.proof

theorem CombCfAtStair.full : CombCfAtStair.Statement :=
  CombCfAtStair.proof CombCfUpdateZero.full

theorem CombCfMonomialPsumOne.full : CombCfMonomialPsumOne.Statement :=
  CombCfMonomialPsumOne.proof

theorem CombDetDescFactorial.full : CombDetDescFactorial.Statement :=
  CombDetDescFactorial.proof

theorem CombCfVandermondePsumOne.full : CombCfVandermondePsumOne.Statement :=
  CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full

theorem FrobeniusDimensionFormula.full : FrobeniusDimensionFormula.Statement :=
  FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full

theorem LemmaC.full : LemmaC.Statement :=
  LemmaC.proof FrobeniusDimensionFormula.full

theorem SchPowerSumHomWeighted.full : SchPowerSumHomWeighted.Statement :=
  SchPowerSumHomWeighted.proof

theorem SchWeightedPreimage.full : SchWeightedPreimage.Statement :=
  SchWeightedPreimage.proof SchPowerSumHomWeighted.full

theorem SchPowerSumAtRootsOfUnity.full : SchPowerSumAtRootsOfUnity.Statement :=
  SchPowerSumAtRootsOfUnity.proof

theorem SchEvalPowerSumHom.full : SchEvalPowerSumHom.Statement :=
  SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full

theorem SchSchurRowsToK.full : SchSchurRowsToK.Statement :=
  SchSchurRowsToK.proof

theorem SchProdOneSubRootsOfUnity.full : SchProdOneSubRootsOfUnity.Statement :=
  SchProdOneSubRootsOfUnity.proof

theorem SchCompleteGenerating.full : SchCompleteGenerating.Statement :=
  SchCompleteGenerating.proof

theorem SchCompleteAtRootsOfUnity.full : SchCompleteAtRootsOfUnity.Statement :=
  SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full

theorem SchSchurEvalMatrix.full : SchSchurEvalMatrix.Statement :=
  SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full

theorem SchRootOfUnityBialternant.full : SchRootOfUnityBialternant.Statement :=
  SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full

theorem SchRootOfUnityRowsPerm.full : SchRootOfUnityRowsPerm.Statement :=
  SchRootOfUnityRowsPerm.proof

theorem SchRootOfUnityRowsEq.full : SchRootOfUnityRowsEq.Statement :=
  SchRootOfUnityRowsEq.proof

theorem SchHookResidues.full : SchHookResidues.Statement :=
  SchHookResidues.proof

theorem SchResidueCount.full : SchResidueCount.Statement :=
  SchResidueCount.proof

theorem SchNonHookResidues.full : SchNonHookResidues.Statement :=
  SchNonHookResidues.proof SchResidueCount.full

theorem SchRootOfUnityVandermondeNe.full : SchRootOfUnityVandermondeNe.Statement :=
  SchRootOfUnityVandermondeNe.proof

theorem SchJTMatrixDetAtRoots.full : SchJTMatrixDetAtRoots.Statement :=
  SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full

theorem SchSchurAtRootsOfUnity.full : SchSchurAtRootsOfUnity.Statement :=
  SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full

theorem SchurPowerSumCoefficient.full : SchurPowerSumCoefficient.Statement :=
  SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full

theorem SchStrictAntiSplit.full : SchStrictAntiSplit.Statement :=
  SchStrictAntiSplit.proof

theorem SchAltPartitionExpansion.full : SchAltPartitionExpansion.Statement :=
  SchAltPartitionExpansion.proof SchStrictAntiSplit.full

theorem FrobeniusCharacterFormula.full : FrobeniusCharacterFormula.Statement :=
  FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full

theorem CombSortLe.full : CombSortLe.Statement :=
  CombSortLe.proof

theorem CombSortShift.full : CombSortShift.Statement :=
  Comb.CombSortShift.proof CombSortLe.full

theorem CombSortShiftDistinct.full : CombSortShiftDistinct.Statement :=
  CombSortShiftDistinct.proof

theorem CombPcntAppend.full : CombPcntAppend.Statement :=
  CombPcntAppend.proof

theorem CombExtendWord.full : CombExtendWord.Statement :=
  CombExtendWord.proof CombPcntAppend.full

theorem CombStripSum.full : CombStripSum.Statement :=
  CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full

theorem CombCfBound.full : CombCfBound.Statement :=
  CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full

theorem CharacterBound.full : CharacterBound.Statement :=
  CharacterBound.proof CombTableEqWords.full CombCfBound.full

theorem CharacterAtIdentity.full : CharacterAtIdentity.Statement :=
  CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full

theorem CoinvAboveTop.full : CoinvAboveTop.Statement :=
  CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

theorem VandermondeOfHomogeneous.full : VandermondeOfHomogeneous.Statement :=
  VandermondeOfHomogeneous.proof

theorem RestPolynomialHomogeneous.full : RestPolynomialHomogeneous.Statement :=
  RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full

theorem RestPolynomialHomogeneousDecomposition.full : RestPolynomialHomogeneousDecomposition.Statement :=
  RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full

theorem RestPolynomialDecomposes.full : RestPolynomialDecomposes.Statement :=
  RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full

theorem SameFactorFormula.full : SameFactorFormula.Statement :=
  SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem SchurSignCoefficient.full : SchurSignCoefficient.Statement :=
  SchurSignCoefficient.proof SchurPowerSumCoefficient.full

theorem HookTableauCount.full : HookTableauCount.Statement :=
  HookTableauCount.proof FrobeniusDimensionFormula.full

theorem HookSumBound.full : HookSumBound.Statement :=
  HookSumBound.proof LemmaC.full HookTableauCount.full

theorem SameFactorBound.full : SameFactorBound.Statement :=
  SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem OtherFactorFormula.full : OtherFactorFormula.Statement :=
  OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

theorem OtherFactorBound.full : OtherFactorBound.Statement :=
  OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

theorem RestInnerTsumBound.full : RestInnerTsumBound.Statement :=
  RestInnerTsumBound.proof

theorem RestKSumBound.full : RestKSumBound.Statement :=
  RestKSumBound.proof

theorem RestPrimeBoundOfFactor.full : RestPrimeBoundOfFactor.Statement :=
  RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full

theorem RestPrimeBound.full : RestPrimeBound.Statement :=
  RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full

theorem RestBoundOfPrimeBound.full : RestBoundOfPrimeBound.Statement :=
  RestBoundOfPrimeBound.proof

theorem RestBound.full : RestBound.Statement :=
  RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full

end RestTerms

end GroundTheory.Heights₂.Heights
