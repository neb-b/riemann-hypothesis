module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.LimOddOfLimFinOdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.TwoUpOKOfSteps

@[expose] public section

namespace UpperTheory.Gal.Int.Core

theorem toCoreK (hT : UpperTheory.TP.TLiftK) :
    GlobalTheory.CongPhi.ClosedPhi → GlobalTheory.Cong.DescOffT → GlobalTheory.CongL.LimFinOdd → GlobalTheory.RoadU.Core :=
  toCore (UpperTheory.Gal.TP.twoUpOK_of_k hT)

end UpperTheory.Gal.Int.Core
