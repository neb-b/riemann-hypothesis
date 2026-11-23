module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.Bundle0002
public import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.LocalToAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013

@[expose] public section

namespace PositivityTheory.EqVol

theorem indexEq : IndexEq := indexEq_of (coSA saOpen) divisible

theorem levelIndexEq : LevelIndexEq :=
  levelIndexEq_of indexEq (levelCO hatCompactOpen) levelConj (levelRat hatRat)

end PositivityTheory.EqVol
