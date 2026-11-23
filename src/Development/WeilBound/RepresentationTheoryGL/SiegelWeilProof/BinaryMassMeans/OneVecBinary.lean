module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0764
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0272

@[expose] public section

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  _root_.GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula (_root_.GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass) _root_.GlobalTheory.CompanionTheory.SW.MassSimil.simil _root_.GlobalTheory.CompanionTheory.SW.MassHasse.hasse
    (_root_.GlobalTheory.CompanionTheory.RgMass.cnt _root_.GlobalTheory.CompanionTheory.SW.MassTest.testEx (_root_.GlobalTheory.CompanionTheory.SW.LS.lside _root_.GlobalTheory.CompanionTheory.Equi.equi _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (_root_.GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd _root_.GlobalTheory.CompanionTheory.Equi.equi _root_.GlobalTheory.CompanionTheory.MassCount.countBd) _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
