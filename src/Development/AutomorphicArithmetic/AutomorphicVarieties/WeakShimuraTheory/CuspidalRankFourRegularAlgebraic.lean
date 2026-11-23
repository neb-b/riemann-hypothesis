module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

@[expose] public section

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions Formalism.MainNotions.N

def UpperTheory.V.Ws.CuspidalRankFourRegularAlgebraic {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (π : CuspSub L 4) : Prop := (CG.mk π).IsRegAlg
