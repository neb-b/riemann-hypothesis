module

public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0004
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0001
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.Bundle0003
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.StFormB
public import Development.WeilBound.CoreStatements.JacobiBlockDeterminants.HtCancel
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.PolySmulOfSameSing
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
public import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryTranspositionFactor

@[expose] public section

namespace SquareStatements

theorem antisymmetry_of_singular_statement (hSing : StSing) : GoodTowerAntisymmetry :=
  good_tower_antisymmetry_of stXB (alg_of stEmb stFormB) HeightCancellation.stHt hSing stBase stCmp
    antisymmetry_transposition_factor

end SquareStatements
