module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianFields
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0649
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteBadScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0574
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixEqBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651

@[expose] public section

namespace PositivityTheory.Rg.Rsw.Cell

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem muCell : HtExist → IdemEx → MuCell := fun hH hI =>
  have hU := GlobalTheory.CompanionTheory.UnitCell.unitCrit hI
  have hA := GlobalTheory.CompanionTheory.CellTop.cellAlg hI
  muCell_of GlobalTheory.CompanionTheory.RswCell.riesz (GlobalTheory.CompanionTheory.RswCell.NullCompl.nullC_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) (GlobalTheory.CompanionTheory.RswCell.cellFormula_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) hA (GlobalTheory.CompanionTheory.CellDecomp.decomp hI)
    (GlobalTheory.CompanionTheory.CellFew.fewC hI hU (GlobalTheory.CompanionTheory.MoveCell.move_of_unitCrit hU) (GlobalTheory.CompanionTheory.SmallRatCell.smallRat hI) hA) (GlobalTheory.CompanionTheory.SetCell.setC hH) GlobalTheory.CompanionTheory.RswTop.topC

end PositivityTheory.Rg.Rsw.Cell
