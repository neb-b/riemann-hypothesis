module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockSA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.HasOfSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT

@[expose] public section

open UpperTheory.V.Z.Tf UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GaloisFromTraceFormula PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.V.Z.Mult

theorem noData_free : NoData := fun _ _ _ _ hE _ hn _ π _ hd D h1 h2 _ h4 => h1 (SR.has_of_split hE hn π hd D h2 h4)

theorem compOf_free : CompOf := fun E _ _ _ hE n hn _ π _ hd σ hσ hun hae =>
  (UpperTheory.Gal.Desc.match_of UpperTheory.Gal.Desc.speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound
    PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin hE hn π (GOne.unitOf E n hn π hd) σ hσ hun hae).3

theorem mult_free : Mult := by
  have hCount : CountAt := rCountAt compOf_free evalD cpUniq Asm.places
  have hEndo : EndoBlockS :=
    endoS
      (enlarge Th.stUnit hecke_eigenvalues_unitary_one_factor
        unitary_one_characters_separated_by_eigenvalues Asm.places)
      Asm.places (UpperTheory.Zero.ConvolutionTheory.EB.endoBlockG cuspReadI)
  have hIdent : Ident :=
    rIdent noData_free hCount geomTr UpperTheory.ConvolutionTheory.G2.g2s
      UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit
      hEndo stableBlockSA
  exact rMult hIdent hCount levTr geomTr levInd lcLev choiceM offSec muEx

end UpperTheory.V.Z.Mult
