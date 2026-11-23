module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRham
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009

@[expose] public section

open UpperTheory.V.Lit

theorem UpperTheory.V.Lit.deRhamInj :
    DeRhamInj :=
  Dr.deRhamInj_of Dr.absMain Dr.dEquiv Dr.inclFacts Dr.dExact Dr.average Dr.window Dr.cutoff Dr.retract Dr.locSec Dr.coneConvex Dr.geoProper Dr.gauge Dr.levelVal Dr.centralOf Dr.corrFwd Dr.corrSmooth Dr.corrBwd Dr.corrCochain Dr.corrUniq Dr.corrInv Dr.corrBasic Dr.corrD
