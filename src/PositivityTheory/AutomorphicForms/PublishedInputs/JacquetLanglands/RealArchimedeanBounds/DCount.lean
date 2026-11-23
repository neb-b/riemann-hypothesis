module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle0004
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle0005
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMinkP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.Bundle0002
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DetR

@[expose] public section

namespace UpperTheory.Esk

theorem dAx : DAx :=
  have m := aMem
  have iw := aIw m
  have row := aRow m iw
  have orb := aOrb m
  have bnf := aBnfH (aBnf m iw aCls (aAdd m)) orb
  have ht := dHt row
  have mul := dMul m iw aMono row
  dAx_of (dCount m bnf orb) ht mul (dProd m aMono row) (dMink m aMono row bnf aMink ht mul)
    (dNormal m bnf orb aUnit aTrans ht mul) (dCnt (dScale m aCls aUnit) dBox dEntry)

theorem dTwo' : DTwo := dTwo aMem

theorem dGood' : DGood := dGood aMem

end UpperTheory.Esk
