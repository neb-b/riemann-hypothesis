module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G1
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.g1 :
    G1 :=
  firstGeometricCondition_of_properties pairFacts qhtFacts levD bdGrowth approx ptBd fun E _ _ _ a μ _ => (GlobalTheory.CovolGL.finvol E a μ).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ImportsVariant
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.g2 :
    G2 :=
  Cs.galois_twist_preserves_siegel_bound Cs.lamEx Cs.descEx Cs.descFun Cs.rapidAll Cs.corrSz Cs.decP Cs.decK Cs.loc Cs.geoSum Cs.geoRet Cs.supp
end

